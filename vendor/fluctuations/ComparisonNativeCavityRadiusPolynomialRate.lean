module

public import ComparisonNativeCavityRadiusPolynomialLedger

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable

theorem radius_log_power_absorbed {q : ℝ} (hq : 0<q) (C : ℝ) :
    ∀ᶠn:ℕ in atTop,C*Real.log (n:ℝ)≤(n:ℝ)^q := by
  have Hlim:=(comparison_radius_log_power_tendsto hq).const_mul C
  simp only [mul_zero] at Hlim
  have H:=Hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,eventually_gt_atTop (0:ℕ)] with n hn hnpos
  have hnp : 0<(n:ℝ) := by exact_mod_cast hnpos
  have H': C*Real.log (n:ℝ)/(n:ℝ)^q<1 := by simpa only [mul_div_assoc] using hn
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hnp q)).mp H').le.trans_eq (one_mul _)

theorem actual_minimum_cavity_radius_band_polynomial_bound
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D C ca : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hC : 1 ≤ C) (hca : 0 < ca)
    (M : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W a z : ℕ → ℝ) (ha : ∀n,0 < a n) (haz : ∀n,a n ≤ z n) (hz : ∀n,z n ≤ 1)
    (hxsW : ∀n,(M n).xs ≤ W n) (hWz : ∀n,W n ≤ z n)
    (hsize : ∀n,z n ≤ C*W n)
    (houter : ∀n,ca*W n ≤ (M n).alpha.val.val (a n))
    (dphys : ℕ → ℕ) (_e : ∀n,Fin (dphys n+1) ≃ FeatureIndex (n+1))
    (Kb Kh : ℕ → ℝ≥0)
    (hparent : ∀n,LipschitzOnWith (Kb n) (fun r=>(M n).b ((M n).alpha.val.val r)) (Icc (a n) (z n)))
    (hfield : ∀n,LipschitzOnWith (Kh n) (fun r=>(M n).h ((M n).alpha.val.val r)) (Icc (a n) (z n))) :
    ∀ᶠn:ℕ in atTop,(M n).cavityRadiusDefect (a n) (z n)/(W n)^3≤
      ((n+1:ℕ):ℝ)^(-min (delta/64) (1/16)) := by
  obtain ⟨B,hB,hbudget⟩ := eventually_actual_minimum_cavity_radius_budget
    Bclock hm hdelta (by linarith) hcl hcu hAz hC0 hCt
  let x := W
  let N := fun n=>(M n).context.N
  let y := fun n=>(M n).xs+(M n).alpha.val.val (z n)
  let L := fun n=>z n-a n
  let S := fun n r=>orderedPathS (n+1) (M n).bf (M n).hf ((M n).alpha.val.val r)
  let inc := fun n=>S n (z n)-S n (a n)
  let g := fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (z n)
  let F := fun n=>N n*(((1/3)/Real.log (N n))*g n)
  let V := fun tau n=>4*inc n/((M n).alpha.val.val (a n)*(tau*x n)^2*(M n).context.k (z n)*F n)
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
  have hN n : 0 < N n := (M n).context.hN
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
  have hmom n := comparisonVariableEndpoint_radius_moments (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (n+1) (by omega)
    (M n).b (M n).h (M n).context.hd.ne' (M n).hlam.le (M n).hlb
    (M n).hb (M n).hh (M n).hh0 (M n).alpha
  have hinc n : 0 ≤ inc n := sub_nonneg.mpr ((hmom n).1
    ⟨(ha n).le,(haz n).trans (hz n)⟩ ⟨(hzpos n).le,hz n⟩ (haz n))
  have hD n : 0 ≤ (M n).cavityRadiusDefect (a n) (z n) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact sub_nonneg.mpr ((hmom n).2.2 r ⟨(ha n).le.trans hr.1.le,hr.2.le.trans (hz n)⟩).2.1
  have hlog n : 0 ≤ Real.log (N n) := Real.log_nonneg (by
    dsimp only [N,NativeOverlapContext.N]; exact_mod_cast Nat.succ_pos n)
  have hV n tau : 0 ≤ V tau n := by
    have hi := hinc n
    have hA := ((M n).alpha.val.property.1 (a n)).1
    have hg := (laplaceComparisonStrength_pos (M n).context.d (M n).hlam (z n)).le
    have hk := comparisonFloor_pos (δ:=delta) (M n).context.hN (M n).context.hU (hzpos n).le
    have hl := hlog n
    dsimp only [V,F,g]; positivity
  have hT n : 0 ≤ T n := by
    have hi := hinc n
    have hg := (laplaceComparisonStrength_pos (M n).context.d (M n).hlam (z n)).le
    have hl := hlog n
    dsimp only [T,F,g]; positivity
  have hbound : ∀ᶠn : ℕ in atTop,inc n ≤ Cs*x n := by
    filter_upwards [hbudget] with n hn
    have H := (hn (M n) (a n) (z n) (ha n) (haz n) (hz n)
      (dphys n) (_e n) (Kb n) (Kh n) (hparent n) (hfield n)).1
    have hmul := mul_le_mul_of_nonneg_left (hmass n) hB.le
    dsimp only [inc,S,y,Cs] at *
    linarith
  have hupper n : (M n).context.E ≤ (M n).context.d^2/Real.sqrt (N n) := by
    exact (le_div_iff₀ (Real.sqrt_pos.mpr (hN n))).mpr (by simpa only [N,mul_comm] using (M n).hupper)
  have hlower n : gamma*(N n)^(-(2:ℝ)/3+m)*(M n).context.d ≤ (M n).context.E := by
    have H : ((N n)^(-(2:ℝ)/3+m)*(M n).context.d)/C0 ≤ (M n).context.E :=
      (div_le_iff₀ hC0).mpr (by simpa only [N,mul_comm] using (M n).hlower)
    simpa only [gamma,N,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have hax n : Real.sqrt (N n)*(M n).context.E/(M n).context.d ≤ x n :=
    (M n).hscale.trans (hxsW n)
  have hstrength n : p*N n*(M n).context.E^2 ≤ g n*(x n)^2 := by
    have H := cavity_strength_band_scale (M n).context.hd (M n).hlam
      (M n).hxs (hzpos n) (hz n) (hxsW n) (hWz n) (hsize n)
    have H' := mul_le_mul_of_nonneg_left H hCt
    have hc : 0 < (Ct+1)*C := by positivity
    have H'' : N n*(M n).context.E^2 ≤ ((Ct+1)*C)*(g n*(x n)^2) := by
      have hg := (laplaceComparisonStrength_pos (M n).context.d (M n).hlam (z n)).le
      dsimp only [g,x,N] at *
      nlinarith [(M n).htest,mul_nonneg hg (sq_nonneg (W n))]
    have hd : (N n*(M n).context.E^2)/((Ct+1)*C) ≤ g n*(x n)^2 :=
      (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using H'')
    simpa only [p,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using hd
  have hshift : Tendsto (fun n:ℕ=>n+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro k
    filter_upwards [eventually_ge_atTop k] with n hn
    omega
  have hlogevent : ∀ᶠn : ℕ in atTop,1 ≤ Real.log (N n) := by
    simpa only [N,NativeOverlapContext.N,Function.comp_def] using
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hshift).eventually (eventually_ge_atTop 1)
  have hshiftbound : ∀ᶠn : ℕ in atTop,(N n)^(2*delta)*comparisonSmallMass (N n) (M n).context.E ≤ x n := by
    filter_upwards [hshift.eventually (comparison_radius_floor_shift_eventually hgamm hmargin)] with n hn
    exact hn (M n).context.d (M n).context.E (x n) (M n).context.hd (hlower n) (hupper n) (hax n)
  have hVupper : ∀ᶠn:ℕ in atTop,∀tau:ℝ,0<tau→V tau n/(x n)^2≤
      (12*Cs*(C+1)^2/(ca*tau^2*p))*Real.log (N n)/(N n)^delta := by
    filter_upwards [hbound,hlogevent,hshiftbound] with n hninc hnlog hnshift
    intro tau htau
    have hxp := hx n
    have hNp := hN n
    have hUp := (M n).context.hU
    have hzp := hzpos n
    have hinc0 := hinc n
    have hg : 0 < g n := laplaceComparisonStrength_pos (M n).context.d (M n).hlam (z n)
    have hkC : 0 < comparisonFloor (N n) delta (comparisonSmallMass (N n) (M n).context.E) (C*x n) :=
      comparisonFloor_pos (δ:=delta) (M n).context.hN (M n).context.hU (mul_nonneg (by linarith) (hx n).le)
    have hF : 0 < F n := by dsimp only [F];positivity
    have hA : 0 < (M n).alpha.val.val (a n) := (mul_pos hca hxp).trans_le (houter n)
    have hkz : comparisonFloor (N n) delta (comparisonSmallMass (N n) (M n).context.E) (C*x n) ≤
        (M n).context.k (z n) := by
      have hden : 0 < z n+(N n)^(2*delta)*(M n).context.U := by positivity
      unfold NativeOverlapContext.k comparisonFloor
      exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hden)
        (pow_le_pow_left₀ hden.le (by linarith [hsize n]) 2)
    have hdenC : 0 < (M n).alpha.val.val (a n)*(tau*x n)^2*
        comparisonFloor (N n) delta (comparisonSmallMass (N n) (M n).context.E) (C*x n)*F n := by
      positivity
    have hmono : V tau n ≤ 4*inc n/((M n).alpha.val.val (a n)*(tau*x n)^2*
        comparisonFloor (N n) delta (comparisonSmallMass (N n) (M n).context.E) (C*x n)*F n) := by
      apply div_le_div_of_nonneg_left (by positivity) hdenC
      gcongr
    have H := comparison_radius_variance_budget_normalized (hN n) (M n).context.hE hg
      (hx n) (by linarith : 0 ≤ C) htau hca hCs hp (hlog n) (hinc n) hninc
      (houter n) hnshift (hstrength n)
    exact (div_le_div_of_nonneg_right hmono (sq_nonneg (x n))).trans H
  have hTupper : ∀ᶠn:ℕ in atTop,T n/(x n)^3≤
      ((24*Cs/(ca^2*p))/gamma^6)*Real.log (N n)/(N n)^(6*m) := by
    filter_upwards [hbound] with n hninc
    have hg : 0 < g n := laplaceComparisonStrength_pos (M n).context.d (M n).hlam (z n)
    have H := comparison_radius_covariance_budget_normalized (hN n) (M n).context.hE hg
      (hx n) hca hCs hp (hlog n) (hinc n) hninc (houter n) (hstrength n)
    have hr := comparison_radius_small_mass_ratio (hN n) hgamm (M n).context.hd (hlower n) (hupper n) (hax n)
    have H' := comparison_radius_ratio_log_power_bound (hN n) hgamm (by positivity : 0 ≤ 24*Cs/(ca^2*p))
      (hlog n) (div_nonneg (comparisonSmallMass_pos (hN n) (M n).context.hE).le (hx n).le) hr
    exact H.trans H'

  let t:=min (delta/64) (1/16)
  let s:=fun n=>(N n)^(-t)
  let CV:=12*Cs*(C+1)^2/(ca*p)
  let CT:=(24*Cs/(ca^2*p))/gamma^6
  have ht : 0<t := lt_min (by positivity) (by norm_num)
  have ht64 : 64*t≤delta := by
    have H:=min_le_left (delta/64) (1/16)
    dsimp only [t]
    linarith
  have hvroom : 0<delta-32*t := by linarith
  have htroom : 0<6*m-64*t := by linarith
  have hs n : 0<s n := Real.rpow_pos_of_pos (hN n) _
  have hs1 n : s n≤1 := Real.rpow_le_one_of_one_le_of_nonpos
    (by dsimp only [N,NativeOverlapContext.N]; exact_mod_cast Nat.succ_pos n) (by linarith)
  have hspow n (k:ℕ) : (s n)^k=(N n)^(-t*(k:ℝ)) := by
    exact (Real.rpow_mul_natCast (hN n).le (-t) k).symm
  have hVlog : ∀ᶠn:ℕ in atTop,CV*Real.log (N n)≤(N n)^(delta-32*t) := by
    simpa only [N,NativeOverlapContext.N,Function.comp_def] using
      hshift.eventually (radius_log_power_absorbed hvroom CV)
  have hTlog : ∀ᶠn:ℕ in atTop,CT*Real.log (N n)≤(N n)^(6*m-64*t) := by
    simpa only [N,NativeOverlapContext.N,Function.comp_def] using
      hshift.eventually (radius_log_power_absorbed htroom CT)
  have hsmall : ∀ᶠn:ℕ in atTop,radiusPolynomialLedgerConstant B C CY*(N n)^(-2*t)≤(N n)^(-t) := by
    simpa only [N,NativeOverlapContext.N,Function.comp_def,one_mul] using
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
  have Hledger:=(hn (M n) (a n) (z n) (ha n) (haz n) (hz n)
    (dphys n) (_e n) (Kb n) (Kh n) (hparent n) (hfield n)).2 bins hbpos
    ((s n)^8*x n) (mul_pos hs8 (hx n))
  have Hnormalized:=comparisonRadiusMeanSquareBudget_normalized_le bins hbpos (hx n)
    (hL n) (hlength n) (hy n) (hmass n) hs8 hB.le (hV n ((s n)^8)) (hT n)
  have Hledger' : (M n).cavityRadiusDefect (a n) (z n)/(x n)^3≤
      comparisonRadiusMeanSquareBudget bins C ((s n)^8) CY B (B*CY/(bins:ℝ))
        (V ((s n)^8) n/(x n)^2) (T n/(x n)^3) (2*(s n)^8) := by
    apply (div_le_div_of_nonneg_right Hledger (pow_nonneg (hx n).le 3)).trans
    simpa only [x,N,NativeOverlapContext.N,y,L,S,inc,F,g,V,T,Nat.cast_add,Nat.cast_one,mul_assoc] using Hnormalized
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

theorem actual_minimum_cavity_radius_band_constant_clocks_polynomial_bound
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D C ca : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hC : 1 ≤ C) (hca : 0 < ca)
    (M : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W a z : ℕ → ℝ) (ha : ∀n,0 < a n) (haz : ∀n,a n ≤ z n) (hz : ∀n,z n ≤ 1)
    (hxsW : ∀n,(M n).xs ≤ W n) (hWz : ∀n,W n ≤ z n)
    (hsize : ∀n,z n ≤ C*W n)
    (houter : ∀n,ca*W n ≤ (M n).alpha.val.val (a n))
    (T H : ℕ → ℝ) (hb_const : ∀n u,(M n).b u=T n) (hh_const : ∀n u,(M n).h u=H n) :
    ∀ᶠn:ℕ in atTop,(M n).cavityRadiusDefect (a n) (z n)/(W n)^3≤
      ((n+1:ℕ):ℝ)^(-min (delta/64) (1/16)) := by
  exact actual_minimum_cavity_radius_band_polynomial_bound Bclock hm hdelta hmargin hcl hcu
    hAz hC0 hCt hC hca M W a z ha haz hz hxsW hWz hsize houter
    (fun n=>Fintype.card (FeatureIndex (n+1))-1) cavityCanonicalFeatureEquiv
    (fun _=>0) (fun _=>0)
    (fun n=>cavity_constant_clock_lipschitz (hb_const n))
    (fun n=>cavity_constant_clock_lipschitz (hh_const n))

theorem actual_minimum_cavity_radius_band_bare_SK_polynomial_bound
    (Bclock T : ℝ) {m delta cl cu Az C0 Ct D C ca : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hC : 1 ≤ C) (hca : 0 < ca)
    (M : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W a z : ℕ → ℝ) (ha : ∀n,0 < a n) (haz : ∀n,a n ≤ z n) (hz : ∀n,z n ≤ 1)
    (hxsW : ∀n,(M n).xs ≤ W n) (hWz : ∀n,W n ≤ z n)
    (hsize : ∀n,z n ≤ C*W n)
    (houter : ∀n,ca*W n ≤ (M n).alpha.val.val (a n))
    (hb_const : ∀n u,(M n).b u=T) (hh_zero : ∀n u,(M n).h u=0) :
    ∀ᶠn:ℕ in atTop,(M n).cavityRadiusDefect (a n) (z n)/(W n)^3≤
      ((n+1:ℕ):ℝ)^(-min (delta/64) (1/16)) :=
  actual_minimum_cavity_radius_band_constant_clocks_polynomial_bound Bclock hm hdelta hmargin
    hcl hcu hAz hC0 hCt hC hca M W a z ha haz hz hxsW hWz hsize houter
    (fun _=>T) (fun _=>0) hb_const hh_zero

theorem actual_minimum_bare_SK_half_band_polynomial_bound
    (Bclock T : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW1 : ∀n,W n≤1) (hband : ∀n,max 1 (2*Az)*(M n).xs≤W n)
    (hb_const : ∀n u,(M n).b u=T) (hh_zero : ∀n u,(M n).h u=0) :
    ∀ᶠn:ℕ in atTop,(M n).cavityRadiusDefect (W n/2) (W n)/(W n)^3≤
      ((n+1:ℕ):ℝ)^(-min (delta/64) (1/16)) := by
  have hxsW n : (M n).xs≤W n := by
    have H:=mul_le_mul_of_nonneg_right (le_max_left 1 (2*Az)) (M n).hxs.le
    nlinarith [hband n]
  have hWp n : 0<W n := (M n).hxs.trans_le (hxsW n)
  have hthreshold n : (M n).z≤W n/2 := by
    have H:=mul_le_mul_of_nonneg_right (le_max_right 1 (2*Az)) (M n).hxs.le
    nlinarith [(M n).hzxs,hband n]
  have houter n : (cl/2)*W n≤(M n).alpha.val.val (W n/2) := by
    have H:=((M n).regular (W n/2) ⟨hthreshold n,by linarith [hW1 n,hWp n]⟩).1
    nlinarith only [H]
  exact actual_minimum_cavity_radius_band_bare_SK_polynomial_bound
    (C:=1) (ca:=cl/2) Bclock T hm hdelta hmargin hcl hcu hAz hC0 hCt
    (by norm_num) (by positivity) M W (fun n=>W n/2) W
    (fun n=>div_pos (hWp n) (by norm_num)) (fun n=>by linarith [hWp n]) hW1 hxsW
    (fun _=>le_rfl) (fun n=>by simp) houter hb_const hh_zero

end OAI.SKFluctuations.LaplaceWindowFormalization
