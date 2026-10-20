module

public import ComparisonActualHighOnlyCavityConcentrationRadius
public import ComparisonNativeCavityRadiusPolynomialAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

theorem highOnly_strength_antitone_nonnegative {d lam : ℝ}
    (hd : 0 < d) (hlam : 0 < lam) :
    AntitoneOn (laplaceComparisonStrength d lam) (Ici (0:ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (0:ℝ))
    (laplaceComparisonStrength_contDiff d lam).continuous.continuousOn
  · intro r _
    exact ((laplaceComparisonStrength_contDiff d lam).differentiable (by norm_num) r).differentiableWithinAt
  · intro r hr
    have hrpos : 0 < r := by simpa only [interior_Ici,mem_Ioi] using hr
    have hg := laplaceComparisonStrength_pos d hlam r
    have hp := (laplaceComparisonStrength_logSlope_mem hd.ne' hlam.ne' r).1
    have hprod := mul_nonneg hp hg.le
    have heq : comparisonLogSlope (laplaceComparisonStrength d lam) r*
        laplaceComparisonStrength d lam r= -r*deriv (laplaceComparisonStrength d lam) r := by
      unfold comparisonLogSlope
      exact div_mul_cancel₀ _ hg.ne'
    rw [heq] at hprod
    nlinarith

theorem highOnly_strength_band_scale_general {d lam xs W z C : ℝ}
    (hd : 0 < d) (hlam : 0 < lam) (hxs : 0 < xs)
    (hz : 0 < z) (hz1 : z≤1) (hxsW : xs≤W) (hC : 1≤C) (hzW : z≤C*W) :
    laplaceComparisonStrength d lam xs*xs^2≤C*laplaceComparisonStrength d lam z*W^2 := by
  have hg := (laplaceComparisonStrength_pos d hlam z).le
  by_cases hzs : z≤xs
  · have He := highOnly_strength_antitone_nonnegative hd hlam hz.le hxs.le hzs
    have Hsq := (sq_le_sq₀ hxs.le (hxs.le.trans hxsW)).mpr hxsW
    have H := mul_le_mul He Hsq (sq_nonneg xs) hg
    have HC := mul_le_mul_of_nonneg_right hC (mul_nonneg hg (sq_nonneg W))
    exact H.trans (by simpa only [one_mul,mul_assoc] using HC)
  · have hsz : xs≤z := (lt_of_not_ge hzs).le
    have hmono := laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀:=0) le_rfl
    have H := hmono.2 ⟨hxs.le,hsz.trans hz1⟩ ⟨hz.le,hz1⟩ hsz
    have H1 := mul_le_mul_of_nonneg_right H hxs.le
    have H2 := mul_le_mul_of_nonneg_left hzW hg
    have H3 := mul_le_mul H2 hxsW hxs.le (mul_nonneg hg (hz.le.trans hzW))
    calc
      _ = (laplaceComparisonStrength d lam xs*xs)*xs := by ring
      _ ≤ (laplaceComparisonStrength d lam z*z)*xs := H1
      _ ≤ (laplaceComparisonStrength d lam z*(C*W))*W := H3
      _ = _ := by ring

theorem actual_high_only_minimum_cavity_radius_smooth_general_polynomial_bound_along
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D C ca : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hC : 1 ≤ C) (hca : 0 < ca)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcutoff : ∀n,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (W a z : ℕ → ℝ) (ha : ∀n,0 < a n) (haz : ∀n,a n ≤ z n) (hz : ∀n,z n ≤ 1)
    (hxsW : ∀n,(M n).xs ≤ W n)
    (hsize : ∀n,z n ≤ C*W n)
    (houter : ∀n,ca*W n ≤ (M n).alpha.val.val (a n))
    (dphys : ℕ → ℕ) (_e : ∀n,Fin (dphys n+1) ≃ FeatureIndex (dim n+1))
    (Kb Kh : ℕ → ℝ≥0)
    (hparent : ∀n,LipschitzOnWith (Kb n) (fun r=>(M n).b ((M n).alpha.val.val r)) (Icc (a n) (z n)))
    (hfield : ∀n,LipschitzOnWith (Kh n) (fun r=>(M n).h ((M n).alpha.val.val r)) (Icc (a n) (z n))) :
    ∀ᶠn:ℕ in atTop,(M n).cavityRadiusDefect (a n) (z n)/(W n)^3≤
      ((dim n+1:ℕ):ℝ)^(-((3/2)*min (delta/64) (1/16))) := by
  obtain ⟨B,hB,Hbudget⟩ := eventually_actual_high_only_cavity_radius_budget
    Bclock hm hdelta (by linarith) hcl hcu hAz hC0 hCt
  have hbudget := hdim.eventually Hbudget
  let x := W
  let N := fun n=>(M n).data.N
  let y := fun n=>(M n).xs+(M n).alpha.val.val (z n)
  let L := fun n=>z n-a n
  let S := fun n r=>orderedPathS (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r)
  let inc := fun n=>S n (z n)-S n (a n)
  let g := fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (z n)
  let F := fun n=>N n*(((1/3)/Real.log (N n))*g n)
  let V := fun tau n=>4*inc n/((M n).alpha.val.val (a n)*(tau*x n)^2*(M n).data.k (z n)*F n)
  let T := fun n=>8*inc n/((M n).alpha.val.val (a n)^2*F n)
  let CY := 1+cu*(C+Az)
  let Cs := B*CY
  let p := 1/((Ct+1)*C)
  let gamma := 1/C0
  have hCY : 0 ≤ CY := by dsimp only [CY]; positivity
  have hCs : 0 ≤ Cs := mul_nonneg hB.le hCY
  have hp : 0 < p := by dsimp only [p]; positivity
  have hgamm : 0 < gamma := one_div_pos.mpr hC0
  have hx n : 0 < x n := (M n).hxs.trans_le (hxsW n)
  have hN n : 0 < N n := (M n).data.hN
  have hzpos n : 0 < z n := (ha n).trans_le (haz n)
  have hy n : 0 ≤ y n := by
    dsimp only [y]
    exact add_nonneg (M n).hxs.le ((M n).alpha.val.property.1 (z n)).1
  have hL n : 0 ≤ L n := sub_nonneg.mpr (haz n)
  have hlength n : L n ≤ C*x n := by dsimp only [L];linarith [hsize n,ha n]
  have hmass n : y n ≤ CY*x n := by
    let t := max (z n) (M n).z
    have ht : t ∈ Icc (M n).z 1 := ⟨le_max_right _ _,max_le (hz n) (M n).hz.2⟩
    have hzsmall : (M n).z ≤ Az*x n :=
      (M n).hzxs.trans (mul_le_mul_of_nonneg_left (hxsW n) hAz)
    have htbound : t ≤ (C+Az)*x n := by
      apply max_le
      · nlinarith [hsize n,mul_nonneg hAz (hx n).le]
      · nlinarith [hzsmall,mul_nonneg (by linarith : 0 ≤ C) (hx n).le]
    have hup := ((M n).alpha.val.property.2 (le_max_left (z n) (M n).z)).trans ((M n).regular t ht).2
    have hmul := mul_le_mul_of_nonneg_left htbound hcu.le
    dsimp only [y,CY]
    linarith [hxsW n]
  have hmom n:=(M n).radius_moments
  have hinc n : 0 ≤ inc n := sub_nonneg.mpr ((hmom n).1
    ⟨(ha n).le,(haz n).trans (hz n)⟩ ⟨(hzpos n).le,hz n⟩ (haz n))
  have hD n : 0 ≤ (M n).cavityRadiusDefect (a n) (z n) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact sub_nonneg.mpr ((hmom n).2.2 r ⟨(ha n).le.trans hr.1.le,hr.2.le.trans (hz n)⟩).2.1
  have hlog n : 0 ≤ Real.log (N n) := Real.log_nonneg (by
    dsimp only [N,ActualHighOnlyComparisonData.N]; exact_mod_cast Nat.succ_pos (dim n))
  have hV n tau : 0 ≤ V tau n := by
    have hi := hinc n
    have hA := ((M n).alpha.val.property.1 (a n)).1
    have hg := (laplaceComparisonStrength_pos (M n).data.d (M n).hlam (z n)).le
    have hk := comparisonFloor_pos (δ:=delta) (M n).data.hN (M n).data.hU (hzpos n).le
    have hl := hlog n
    dsimp only [V,F,g]; positivity
  have hT n : 0 ≤ T n := by
    have hi := hinc n
    have hg := (laplaceComparisonStrength_pos (M n).data.d (M n).hlam (z n)).le
    have hl := hlog n
    dsimp only [T,F,g]; positivity
  have hbound : ∀ᶠn : ℕ in atTop,inc n ≤ Cs*x n := by
    filter_upwards [hbudget] with n hn
    have H := (hn (M n) (hcutoff n).1 (hcutoff n).2 (a n) (z n) (ha n) (haz n) (hz n)
      (dphys n) (_e n) (Kb n) (Kh n) (hparent n) (hfield n)).1
    have hmul := mul_le_mul_of_nonneg_left (hmass n) hB.le
    dsimp only [inc,S,y,Cs] at *
    linarith
  have hupper n : (M n).data.E ≤ (M n).data.d^2/Real.sqrt (N n) := by
    exact (le_div_iff₀ (Real.sqrt_pos.mpr (hN n))).mpr (by simpa only [N,mul_comm] using (M n).hupper)
  have hlower n : gamma*(N n)^(-(2:ℝ)/3+m)*(M n).data.d ≤ (M n).data.E := by
    have H : ((N n)^(-(2:ℝ)/3+m)*(M n).data.d)/C0 ≤ (M n).data.E :=
      (div_le_iff₀ hC0).mpr (by simpa only [N,mul_comm] using (M n).hlower)
    simpa only [gamma,N,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hax n : Real.sqrt (N n)*(M n).data.E/(M n).data.d ≤ x n :=
    (M n).hscale.trans (hxsW n)
  have hstrength n : p*N n*(M n).data.E^2 ≤ g n*(x n)^2 := by
    have H := highOnly_strength_band_scale_general (M n).data.hd (M n).hlam
      (M n).hxs (hzpos n) (hz n) (hxsW n) hC (hsize n)
    have H' := mul_le_mul_of_nonneg_left H hCt
    have hc : 0 < (Ct+1)*C := by positivity
    have H'' : N n*(M n).data.E^2 ≤ ((Ct+1)*C)*(g n*(x n)^2) := by
      have hg := (laplaceComparisonStrength_pos (M n).data.d (M n).hlam (z n)).le
      dsimp only [g,x,N] at *
      nlinarith [(M n).htest,mul_nonneg hg (sq_nonneg (W n))]
    have hd : (N n*(M n).data.E^2)/((Ct+1)*C) ≤ g n*(x n)^2 :=
      (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using H'')
    simpa only [p,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using hd
  have hshift : Tendsto (fun n:ℕ=>dim n+1) atTop atTop :=
    (tendsto_add_atTop_nat 1).comp hdim
  have hlogevent : ∀ᶠn : ℕ in atTop,1 ≤ Real.log (N n) := by
    simpa only [N,ActualHighOnlyComparisonData.N,Function.comp_def] using
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hshift).eventually (eventually_ge_atTop 1)
  have hshiftbound : ∀ᶠn : ℕ in atTop,(N n)^(2*delta)*comparisonSmallMass (N n) (M n).data.E ≤ x n := by
    filter_upwards [hshift.eventually (comparison_radius_floor_shift_eventually hgamm hmargin)] with n hn
    exact hn (M n).data.d (M n).data.E (x n) (M n).data.hd (hlower n) (hupper n) (hax n)
  have hVupper : ∀ᶠn:ℕ in atTop,∀tau:ℝ,0<tau→V tau n/(x n)^2≤
      (12*Cs*(C+1)^2/(ca*tau^2*p))*Real.log (N n)/(N n)^delta := by
    filter_upwards [hbound,hlogevent,hshiftbound] with n hninc hnlog hnshift
    intro tau htau
    have hxp := hx n
    have hNp := hN n
    have hUp := (M n).data.hU
    have hzp := hzpos n
    have hinc0 := hinc n
    have hg : 0 < g n := laplaceComparisonStrength_pos (M n).data.d (M n).hlam (z n)
    have hkC : 0 < comparisonFloor (N n) delta (comparisonSmallMass (N n) (M n).data.E) (C*x n) :=
      comparisonFloor_pos (δ:=delta) (M n).data.hN (M n).data.hU (mul_nonneg (by linarith) (hx n).le)
    have hF : 0 < F n := by dsimp only [F];positivity
    have hA : 0 < (M n).alpha.val.val (a n) := (mul_pos hca hxp).trans_le (houter n)
    have hkz : comparisonFloor (N n) delta (comparisonSmallMass (N n) (M n).data.E) (C*x n) ≤
        (M n).data.k (z n) := by
      have hden : 0 < z n+(N n)^(2*delta)*(M n).data.U := by positivity
      unfold ActualHighOnlyComparisonData.k comparisonFloor
      exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hden)
        (pow_le_pow_left₀ hden.le (by linarith [hsize n]) 2)
    have hdenC : 0 < (M n).alpha.val.val (a n)*(tau*x n)^2*
        comparisonFloor (N n) delta (comparisonSmallMass (N n) (M n).data.E) (C*x n)*F n := by
      positivity
    have hmono : V tau n ≤ 4*inc n/((M n).alpha.val.val (a n)*(tau*x n)^2*
        comparisonFloor (N n) delta (comparisonSmallMass (N n) (M n).data.E) (C*x n)*F n) := by
      apply div_le_div_of_nonneg_left (by positivity) hdenC
      gcongr
    have H := comparison_radius_variance_budget_normalized (hN n) (M n).data.hE hg
      (hx n) (by linarith : 0 ≤ C) htau hca hCs hp (hlog n) (hinc n) hninc
      (houter n) hnshift (hstrength n)
    exact (div_le_div_of_nonneg_right hmono (sq_nonneg (x n))).trans H
  have hTupper : ∀ᶠn:ℕ in atTop,T n/(x n)^3≤
      ((24*Cs/(ca^2*p))/gamma^6)*Real.log (N n)/(N n)^(6*m) := by
    filter_upwards [hbound] with n hninc
    have hg : 0 < g n := laplaceComparisonStrength_pos (M n).data.d (M n).hlam (z n)
    have H := comparison_radius_covariance_budget_normalized (hN n) (M n).data.hE hg
      (hx n) hca hCs hp (hlog n) (hinc n) hninc (houter n) (hstrength n)
    have hr := comparison_radius_small_mass_ratio (hN n) hgamm (M n).data.hd (hlower n) (hupper n) (hax n)
    have H' := comparison_radius_ratio_log_power_bound (hN n) hgamm (by positivity : 0 ≤ 24*Cs/(ca^2*p))
      (hlog n) (div_nonneg (comparisonSmallMass_pos (hN n) (M n).data.hE).le (hx n).le) hr
    exact H.trans H'

  let t:=(3/2)*min (delta/64) (1/16)
  let s:=fun n=>(N n)^(-t)
  let CV:=12*Cs*(C+1)^2/(ca*p)
  let CT:=(24*Cs/(ca^2*p))/gamma^6
  have ht : 0<t := mul_pos (by norm_num) (lt_min (by positivity) (by norm_num))
  have ht64 : 64*t≤(3/2)*delta := by
    have H:=min_le_left (delta/64) (1/16)
    dsimp only [t]
    linarith
  have hvroom : 0<delta-32*t := by linarith
  have htroom : 0<6*m-64*t := by linarith
  have hs n : 0<s n := Real.rpow_pos_of_pos (hN n) _
  have hs1 n : s n≤1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by dsimp only [N,ActualHighOnlyComparisonData.N]; exact_mod_cast Nat.succ_pos (dim n)) (by linarith)
  have hspow n (k:ℕ) : (s n)^k=(N n)^(-t*(k:ℝ)) := by
    exact (Real.rpow_mul_natCast (hN n).le (-t) k).symm
  have hVlog : ∀ᶠn:ℕ in atTop,CV*Real.log (N n)≤(N n)^(delta-32*t) := by
    simpa only [N,ActualHighOnlyComparisonData.N,Function.comp_def] using
      hshift.eventually (radius_log_power_absorbed hvroom CV)
  have hTlog : ∀ᶠn:ℕ in atTop,CT*Real.log (N n)≤(N n)^(6*m-64*t) := by
    simpa only [N,ActualHighOnlyComparisonData.N,Function.comp_def] using
      hshift.eventually (radius_log_power_absorbed htroom CT)
  have hsmall : ∀ᶠn:ℕ in atTop,radiusPolynomialLedgerConstant B C CY*(N n)^(-2*t)≤(N n)^(-t) := by
    simpa only [N,ActualHighOnlyComparisonData.N,Function.comp_def,one_mul] using
      hshift.eventually (eventually_coefficient_rpow_le (c:=radiusPolynomialLedgerConstant B C CY)
        (d:=1) (q:= -2*t) (r:= -t) (by norm_num) (by linarith))
  filter_upwards [hbudget,hVupper,hTupper,hVlog,hTlog,hsmall] with n hn hnv hnt hnvlog hntlog hnsmall
  have hs8:=pow_pos (hs n) 8
  have hVp : V ((s n)^8) n/(x n)^2≤(s n)^16 := by
    have H:=hnv ((s n)^8) hs8
    have he : (12*Cs*(C+1)^2/(ca*((s n)^8)^2*p))*Real.log (N n)/(N n)^delta=
        (CV*Real.log (N n))/(N n)^(delta-16*t) := by
      dsimp only [CV]
      rw [←pow_mul,hspow n 16]
      norm_num only [Nat.cast_ofNat]
      rw [show -t*(16:ℝ)=-(16*t) by ring]
      rw [Real.rpow_sub (hN n),Real.rpow_neg (hN n).le]
      field_simp
    rw [he] at H
    have Hlog:=div_le_div_of_nonneg_right hnvlog (Real.rpow_nonneg (hN n).le (delta-16*t))
    have he' : (N n)^(delta-32*t)/(N n)^(delta-16*t)=(s n)^16 := by
      rw [←Real.rpow_sub (hN n),hspow n 16]
      congr 1
      norm_num only [Nat.cast_ofNat]
      ring
    rw [he'] at Hlog
    exact H.trans Hlog
  have hTp : T n/(x n)^3≤(s n)^64 := by
    have Hlog:=div_le_div_of_nonneg_right hntlog (Real.rpow_nonneg (hN n).le (6*m))
    have he : (N n)^(6*m-64*t)/(N n)^(6*m)=(s n)^64 := by
      rw [←Real.rpow_sub (hN n),hspow n 64]
      congr 1
      norm_num only [Nat.cast_ofNat]
      ring
    rw [he] at Hlog
    exact hnt.trans Hlog
  let bins:=⌈1/s n⌉₊
  obtain ⟨hbpos,hblo,hbhi⟩:=radius_polynomial_bins_geometry (hs n) (hs1 n)
  have Hledger:=(hn (M n) (hcutoff n).1 (hcutoff n).2 (a n) (z n) (ha n) (haz n) (hz n)
    (dphys n) (_e n) (Kb n) (Kh n) (hparent n) (hfield n)).2 bins hbpos
    ((s n)^8*x n) (mul_pos hs8 (hx n))
  have Hnormalized:=comparisonRadiusMeanSquareBudget_normalized_le bins hbpos (hx n)
    (hL n) (hlength n) (hy n) (hmass n) hs8 hB.le (hV n ((s n)^8)) (hT n)
  have Hledger' : (M n).cavityRadiusDefect (a n) (z n)/(x n)^3≤
      comparisonRadiusMeanSquareBudget bins C ((s n)^8) CY B (B*CY/(bins:ℝ))
        (V ((s n)^8) n/(x n)^2) (T n/(x n)^3) (2*(s n)^8) := by
    apply (div_le_div_of_nonneg_right Hledger (pow_nonneg (hx n).le 3)).trans
    simpa only [x,N,ActualHighOnlyComparisonData.N,y,L,S,inc,F,g,V,T,Nat.cast_add,Nat.cast_one,mul_assoc] using Hnormalized
  have Hpoly:=comparisonRadiusMeanSquareBudget_polynomial_le bins (hs n) (hs1 n) hB.le
    (by linarith : 0≤C) hCY hblo hbhi
    (div_nonneg (hV n ((s n)^8)) (sq_nonneg (x n))) hVp
    (div_nonneg (hT n) (pow_nonneg (hx n).le 3)) hTp
  apply (Hledger'.trans Hpoly).trans
  have he : (s n)^2=(N n)^(-2*t) := by
    rw [hspow n 2]
    congr 1
    norm_num only [Nat.cast_ofNat]
    ring
  rw [he]
  exact hnsmall

theorem actual_high_only_minimum_cavity_radius_smooth_general_eventually_polynomial_bound_along
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D C ca : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hC : 1 ≤ C) (hca : 0 < ca)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (W a z : ℕ→ℝ)
    (Hgeometry : ∀ᶠn in atTop,
      0 < a n ∧ a n ≤ z n ∧ z n ≤ 1 ∧ (M n).xs ≤ W n ∧
      z n ≤ C*W n ∧ ca*W n ≤ (M n).alpha.val.val (a n) ∧
      ∃Kb Kh : ℝ≥0,
        LipschitzOnWith Kb (fun r=>(M n).b ((M n).alpha.val.val r)) (Icc (a n) (z n)) ∧
        LipschitzOnWith Kh (fun r=>(M n).h ((M n).alpha.val.val r)) (Icc (a n) (z n))) :
    ∀ᶠn in atTop,(M n).cavityRadiusDefect (a n) (z n)/(W n)^3 ≤
      ((dim n+1:ℕ):ℝ)^(-((3/2)*min (delta/64) (1/16))) := by
  obtain ⟨n0,Hn0⟩:=eventually_atTop.mp (Hgeometry.and Hcutoff)
  have Hg n:=(Hn0 (n+n0) (Nat.le_add_left n0 n)).1
  have Hc n:=(Hn0 (n+n0) (Nat.le_add_left n0 n)).2
  choose Kb Kh hparent hfield using fun n=>(Hg n).2.2.2.2.2.2
  have H := actual_high_only_minimum_cavity_radius_smooth_general_polynomial_bound_along
    Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt hC hca
    (fun n=>dim (n+n0)) (hdim.comp (tendsto_add_atTop_nat n0))
    (fun n=>M (n+n0)) Hc (fun n=>W (n+n0)) (fun n=>a (n+n0)) (fun n=>z (n+n0))
    (fun n=>(Hg n).1) (fun n=>(Hg n).2.1) (fun n=>(Hg n).2.2.1)
    (fun n=>(Hg n).2.2.2.1) (fun n=>(Hg n).2.2.2.2.1)
    (fun n=>(Hg n).2.2.2.2.2.1)
    (fun n=>Fintype.card (FeatureIndex (dim (n+n0)+1))-1)
    (fun n=>cavityCanonicalFeatureEquiv (dim (n+n0))) Kb Kh hparent hfield
  obtain ⟨n1,Hn1⟩ := eventually_atTop.mp H
  filter_upwards [eventually_ge_atTop (n0+n1)] with n hn
  have he : n-n0+n0=n := Nat.sub_add_cancel (by omega)
  obtain ⟨k,rfl⟩ : ∃k,n=k+n0 := ⟨n-n0,he.symm⟩
  exact Hn1 k (by omega)

end OAI.SKFluctuations.LaplaceWindowFormalization
