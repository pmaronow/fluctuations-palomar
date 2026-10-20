module

public import ComparisonNativeActualChildClockIncrementProducer

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}

theorem eventually_actual_child_positive_band_increments
    (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) {eta Cmass : ℝ}
    (heta : 0 < eta) (heta1 : eta ≤ 1) (hCmass : 0 ≤ Cmass)
    (hmargin : 0 < 9*m-298*delta) :
    ∀ᶠn : ℕ in atTop,
      ∀(P : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (x : ℝ),
      x∈Ioc (0:ℝ) 1 → comparisonConditionalScale P.context.N delta P.context.E P.lam ≤ x →
      laplaceComparisonStrength P.context.d P.lam x ≤ (eta*c0)^3*x^2 → P.z ≤ Az*x →
      ∀y : ℝ,actualChildCutoff (n+1) delta c0 P.context.d P.lam x ≤ y →
      ∀u∈Icc (0:ℝ) (min (Cmass*y) 1),
        laplaceComparisonStrength P.context.d P.lam (P.R u) ≤ eta^2*y^2 ∧
        laplaceComparisonStrength P.context.d P.lam (P.R u)*P.R u ≤
          max 1 (Az+Cmass/cl)*eta^2*y^3 := by
  let C:=max 1 (Az+Cmass/cl)
  have hC : 1 ≤ C:=le_max_left _ _
  have hC0' : 0 ≤ C:=zero_le_one.trans hC
  filter_upwards [eventually_actual_child_clock_increments_from_target
    (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    hdelta hC0 hc0 hc01 heta heta1 hC hmargin] with n hn
  intro P x hx htarget hweak hz y hay u hu
  let a:=actualChildCutoff (n+1) delta c0 P.context.d P.lam x
  have ha : 0 < a:=(actual_child_cutoff_pos_le_radius P.context.hN hc0 P.hlam hx.1).1
  have hy : 0 < y:=ha.trans_le hay
  have hu1 : u∈Icc (0:ℝ) 1:=⟨hu.1,hu.2.trans (min_le_right _ _)⟩
  have huCy : u ≤ Cmass*y:=hu.2.trans (min_le_left _ _)
  have hr:=comparisonSweepQuantile_bounds P.context.hc P.context.hk P.context.hkc
    P.context.hm P.context.hM P.alpha u
  have Hzero:=hn P x hx htarget hweak 0 (by norm_num) (mul_nonneg hC0' hx.1.le)
  have hlam : P.lam ≤ eta^2*a^2 := by
    simpa only [laplaceComparisonStrength,comparisonStrength,laplaceComparisonShape,
      mul_zero,zero_div,ite_eq_left (by norm_num : (0:ℝ) ≤ 1),mul_one] using Hzero.1
  have Hg : laplaceComparisonStrength P.context.d P.lam (P.R u) ≤ eta^2*y^2 :=
    (laplaceComparisonStrength_le P.context.d P.hlam.le _).trans
      (hlam.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hay 2) (sq_nonneg eta)))
  refine ⟨Hg,?_⟩
  have Hr : P.R u ≤ Az*x+(Cmass/cl)*y := by
    have H:=P.inverse_radius_le_regular_cap hcl hu1
    have Hdiv : u/cl ≤ (Cmass/cl)*y := by
      convert div_le_div_of_nonneg_right huCy hcl.le using 1
      ring
    linarith only [H,Hdiv,hz]
  by_cases hyx : y ≤ x
  · have HrCx : P.R u ≤ C*x := by
      have H:=mul_le_mul_of_nonneg_left hyx (div_nonneg hCmass hcl.le)
      have H':=mul_le_mul_of_nonneg_right (le_max_right 1 (Az+Cmass/cl)) hx.1.le
      nlinarith only [Hr,H,H']
    have HH:=(hn P x hx htarget hweak (P.R u) hr HrCx).2
    have Hpow:=pow_le_pow_left₀ ha.le hay 3
    have Het : eta^3 ≤ eta^2 := by
      have H:=mul_le_mul_of_nonneg_left heta1 (sq_nonneg eta)
      nlinarith only [H]
    have H1:=mul_le_mul_of_nonneg_left Hpow (mul_nonneg hC0' (pow_nonneg heta.le 3))
    have H2:=mul_le_mul_of_nonneg_left Het (mul_nonneg hC0' (pow_nonneg hy.le 3))
    change laplaceComparisonStrength P.context.d P.lam (P.R u)*P.R u ≤ C*eta^2*y^3
    nlinarith only [HH,H1,H2]
  · have HrCy : P.R u ≤ C*y := by
      have H:=mul_le_mul_of_nonneg_left (le_of_not_ge hyx) hAz
      have H':=mul_le_mul_of_nonneg_right (le_max_right 1 (Az+Cmass/cl)) hy.le
      nlinarith only [Hr,H,H']
    have H:=mul_le_mul Hg HrCy hr.1 (by positivity : 0 ≤ eta^2*y^2)
    change laplaceComparisonStrength P.context.d P.lam (P.R u)*P.R u ≤ C*eta^2*y^3
    nlinarith only [H]

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
