module

public import ComparisonNativeStarCapSaving
public import ComparisonNativeOverlapRawAmplitude

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4000000

namespace NativeOverlapMinimum

theorem direct_test_strength_square
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hCt : 0 ≤ Ct) {v : ℝ} (hxv : M.xs ≤ v) (hv1 : v ≤ 1) :
    (1/(Ct+1))*(n:ℝ)*M.context.E^2 ≤
      laplaceComparisonStrength M.context.d M.lam v*v^2 := by
  have hv : 0 < v := M.hxs.trans_le hxv
  have hm := (laplaceComparisonStrength_monotonicities M.context.hd.ne' M.hlam
    (r₀:=0) le_rfl).2 ⟨M.hxs.le,hxv.trans hv1⟩ ⟨hv.le,hv1⟩ hxv
  have hg := laplaceComparisonStrength_pos M.context.d M.hlam v
  have hmul := mul_le_mul_of_nonneg_right hm M.hxs.le
  have hscale : laplaceComparisonStrength M.context.d M.lam M.xs*M.xs^2 ≤
      laplaceComparisonStrength M.context.d M.lam v*v^2 := by
    have hsecond := mul_le_mul_of_nonneg_left hxv (mul_nonneg hg.le hv.le)
    nlinarith
  have hbound : (n:ℝ)*M.context.E^2 ≤
      (Ct+1)*(laplaceComparisonStrength M.context.d M.lam v*v^2) := by
    have hfirst := mul_le_mul_of_nonneg_left hscale hCt
    nlinarith [M.htest,mul_nonneg hg.le (sq_nonneg v)]
  have H : ((n:ℝ)*M.context.E^2)/(Ct+1) ≤
      laplaceComparisonStrength M.context.d M.lam v*v^2 :=
    (div_le_iff₀ (by linarith : 0 < Ct+1)).mpr (by simpa only [mul_comm] using hbound)
  simpa only [div_eq_mul_inv,one_mul,mul_comm,mul_left_comm,mul_assoc] using H

end NativeOverlapMinimum

theorem eventually_actual_minimum_star_cap_saving
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D Cprof : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hCprof : 0 ≤ Cprof) :
    ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀v : ℝ,M.xs ≤ v → v ≤ 1 →
      M.context.M (Cprof*v)/
        ((n:ℝ)*laplaceComparisonStrength M.context.d M.lam v*v^4) ≤
      ((2*(Cprof+1)+(Cprof+1)^2)/((1/(Ct+1))*(1/C0)^3))*
        (n:ℝ)^(-(3*m-delta)) := by
  filter_upwards [eventually_comparison_star_cap_saving
    hm (by positivity : 0 < 1/C0) hCprof (by positivity : 0 < 1/(Ct+1))]
    with n hn
  intro M v hxv hv1
  have hlo : (1/C0)*(n:ℝ)^(-(2:ℝ)/3+m)*M.context.d ≤ M.context.E := by
    have H : ((n:ℝ)^(-(2:ℝ)/3+m)*M.context.d)/C0 ≤ M.context.E :=
      (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using M.hlower)
    simpa only [div_eq_mul_inv,one_mul,mul_comm,mul_left_comm,mul_assoc] using H
  have hup : M.context.E ≤ M.context.d^2/Real.sqrt (n:ℝ) := by
    apply (le_div_iff₀ (Real.sqrt_pos.mpr M.context.hN)).mpr
    simpa only [mul_comm] using M.hupper
  exact hn M.context.d M.context.E v (laplaceComparisonStrength M.context.d M.lam v)
    M.context.hd M.context.hE hlo hup (M.hscale.trans hxv)
    (M.direct_test_strength_square hCt hxv hv1)

end OAI.SKFluctuations.LaplaceWindowFormalization
