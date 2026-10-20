module

public import ComparisonNativeCavityConcentrationRadius
public import ComparisonRadiusLedgerNormalization

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 8000000
attribute [local instance] Classical.propDecidable

theorem cavity_strength_comparable_endpoint {d lam x z C : ℝ}
    (hd : 0 < d) (hlam : 0 < lam) (hx : 0 < x) (hx1 : x ≤ 1)
    (hz : 0 < z) (hz1 : z ≤ 1) (hC : 1 ≤ C) (hzx : z ≤ C*x) :
    laplaceComparisonStrength d lam x ≤ C*laplaceComparisonStrength d lam z := by
  have hmono := laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀:=0) le_rfl
  have hg := (laplaceComparisonStrength_pos d hlam z).le
  by_cases hzx' : z ≤ x
  · exact (hmono.1 ⟨hz.le,hz1⟩ ⟨hx.le,hx1⟩ hzx').trans (by nlinarith)
  · have H := hmono.2 ⟨hx.le,hx1⟩ ⟨hz.le,hz1⟩ (le_of_not_ge hzx')
    have H' : laplaceComparisonStrength d lam x*x ≤ (C*laplaceComparisonStrength d lam z)*x := by
      calc
        _ ≤ laplaceComparisonStrength d lam z*z := H
        _ ≤ laplaceComparisonStrength d lam z*(C*x) := mul_le_mul_of_nonneg_left hzx hg
        _ = _ := by ring
    exact (mul_le_mul_iff_right₀ hx).mp (by simpa only [mul_comm] using H')

theorem actual_minimum_cavity_radius_Eq19_tendsto_zero
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D C ca : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hC : 1 ≤ C) (hca : 0 < ca)
    (M : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (a z : ℕ → ℝ) (ha : ∀n,0 < a n) (haz : ∀n,a n ≤ z n) (hz : ∀n,z n ≤ 1)
    (hxs1 : ∀n,(M n).xs ≤ 1) (hsize : ∀n,z n ≤ C*(M n).xs)
    (houter : ∀n,ca*(M n).xs ≤ (M n).alpha.val.val (a n))
    (dphys : ℕ → ℕ) (_e : ∀n,Fin (dphys n+1) ≃ FeatureIndex (n+1))
    (Kb Kh : ℕ → ℝ≥0)
    (hparent : ∀n,LipschitzOnWith (Kb n) (fun r=>(M n).b ((M n).alpha.val.val r)) (Icc (a n) (z n)))
    (hfield : ∀n,LipschitzOnWith (Kh n) (fun r=>(M n).h ((M n).alpha.val.val r)) (Icc (a n) (z n))) :
    Tendsto (fun n=>(M n).cavityRadiusDefect (a n) (z n)/(M n).xs^3) atTop (𝓝 0) := by
  obtain ⟨B,hB,hbudget⟩ := eventually_actual_minimum_cavity_radius_budget
    Bclock hm hdelta (by linarith) hcl hcu hAz hC0 hCt
  let x := fun n=>(M n).xs
  let N := fun n=>(M n).context.N
  let y := fun n=>x n+(M n).alpha.val.val (z n)
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
  have hx n : 0 < x n := (M n).hxs
  have hN n : 0 < N n := (M n).context.hN
  have hzpos n : 0 < z n := (ha n).trans_le (haz n)
  have hy n : 0 ≤ y n := by
    dsimp only [y]
    exact add_nonneg (hx n).le ((M n).alpha.val.property.1 (z n)).1
  have hL n : 0 ≤ L n := sub_nonneg.mpr (haz n)
  have hlength n : L n ≤ C*x n := by dsimp only [L];linarith [hsize n,ha n]
  have hmass n : y n ≤ CY*x n := by
    let t := max (z n) (M n).z
    have ht : t ∈ Icc (M n).z 1 := ⟨le_max_right _ _,max_le (hz n) (M n).hz.2⟩
    have htbound : t ≤ (C+Az)*x n := by
      apply max_le
      · nlinarith [hsize n,mul_nonneg hAz (hx n).le]
      · nlinarith [(M n).hzxs,mul_nonneg (by linarith : 0 ≤ C) (hx n).le]
    have hup := ((M n).alpha.val.property.2 (le_max_left (z n) (M n).z)).trans ((M n).regular t ht).2
    have hmul := mul_le_mul_of_nonneg_left htbound hcu.le
    dsimp only [y,CY]
    linarith
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
  have hax n : Real.sqrt (N n)*(M n).context.E/(M n).context.d ≤ x n := (M n).hscale
  have hstrength n : p*N n*(M n).context.E^2 ≤ g n*(x n)^2 := by
    have H := cavity_strength_comparable_endpoint (M n).context.hd (M n).hlam (hx n)
      (hxs1 n) (hzpos n) (hz n) hC (hsize n)
    have H' := mul_le_mul_of_nonneg_right H (mul_nonneg hCt (sq_nonneg (x n)))
    have hc : 0 < (Ct+1)*C := by positivity
    have H'' : N n*(M n).context.E^2 ≤ ((Ct+1)*C)*(g n*(x n)^2) := by
      have hg := (laplaceComparisonStrength_pos (M n).context.d (M n).hlam (z n)).le
      dsimp only [g,x,N] at *
      nlinarith [(M n).htest,mul_nonneg hg (sq_nonneg (M n).xs)]
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
  have hVlim tau (htau : 0 < tau) : Tendsto (fun n=>V tau n/(x n)^2) atTop (𝓝 0) := by
    have hupperV : ∀ᶠn : ℕ in atTop,V tau n/(x n)^2 ≤
        (12*Cs*(C+1)^2/(ca*tau^2*p))*Real.log (N n)/(N n)^delta := by
      filter_upwards [hbound,hlogevent,hshiftbound] with n hninc hnlog hnshift
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
    exact squeeze_zero' (Eventually.of_forall (fun n=>div_nonneg (hV n tau) (sq_nonneg (x n)))) hupperV
      (by simpa only [N,NativeOverlapContext.N,Function.comp_def,mul_zero,←mul_div_assoc] using
        (((comparison_radius_log_power_tendsto hdelta).comp hshift).const_mul (12*Cs*(C+1)^2/(ca*tau^2*p))))
  have hTlim : Tendsto (fun n=>T n/(x n)^3) atTop (𝓝 0) := by
    have hupperT : ∀ᶠn : ℕ in atTop,T n/(x n)^3 ≤
        ((24*Cs/(ca^2*p))/gamma^6)*Real.log (N n)/(N n)^(6*m) := by
      filter_upwards [hbound] with n hninc
      have hg : 0 < g n := laplaceComparisonStrength_pos (M n).context.d (M n).hlam (z n)
      have H := comparison_radius_covariance_budget_normalized (hN n) (M n).context.hE hg
        (hx n) hca hCs hp (hlog n) (hinc n) hninc (houter n) (hstrength n)
      have hr := comparison_radius_small_mass_ratio (hN n) hgamm (M n).context.hd (hlower n) (hupper n) (hax n)
      have H' := comparison_radius_ratio_log_power_bound (hN n) hgamm (by positivity : 0 ≤ 24*Cs/(ca^2*p))
        (hlog n) (div_nonneg (comparisonSmallMass_pos (hN n) (M n).context.hE).le (hx n).le) hr
      exact H.trans H'
    exact squeeze_zero' (Eventually.of_forall (fun n=>div_nonneg (hT n) (pow_nonneg (hx n).le 3))) hupperT
      (by simpa only [N,NativeOverlapContext.N,Function.comp_def,mul_zero,←mul_div_assoc] using
        (((comparison_radius_log_power_tendsto (by positivity : 0 < 6*m)).comp hshift).const_mul ((24*Cs/(ca^2*p))/gamma^6)))
  apply comparisonRadiusOrderedDefect_tendsto_zero x L y
    (fun n=>(M n).cavityRadiusDefect (a n) (z n)) T V hB.le (by linarith : 0 ≤ C) hCY
    hx hL hlength hy hmass hD hT (fun tau _ n=>hV n tau) hVlim hTlim
  intro bins hbins tau htau
  filter_upwards [hbudget] with n hn
  have H := (hn (M n) (a n) (z n) (ha n) (haz n) (hz n)
    (dphys n) (_e n) (Kb n) (Kh n) (hparent n) (hfield n)).2 bins hbins (tau*x n) (mul_pos htau (hx n))
  simpa only [x,N,NativeOverlapContext.N,y,L,S,inc,F,g,V,T,Nat.cast_add,Nat.cast_one,mul_assoc] using H

end OAI.SKFluctuations.LaplaceWindowFormalization
