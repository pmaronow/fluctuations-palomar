module

public import ChildStrengthZero
public import ComparisonNativeActualMinimumCapGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 3000000

 theorem actual_comparison_parameter_tendsto_zero_of_weak_bounded_call
    {d lam x : ℕ→ℝ}
    (hdata : ∀ᶠn in atTop,0 < d n ∧ 0 ≤ lam n ∧ 0 < x n ∧
      x n ≤ 1 ∧ lam n ≤ (d n)^2)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (d n) (lam n) (x n)/(x n)^2)
      atTop (𝓝 0)) : Tendsto lam atTop (𝓝 0) := by
  have Hnorm := actual_zero_strength_small_of_working_strength
    (hdata.mono (fun n hn=>⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.2⟩)) hweak
  have he0 (n : ℕ) : laplaceComparisonStrength (d n) (lam n) 0=lam n := by
    simp [laplaceComparisonStrength,comparisonStrength,laplaceComparisonShape]
  simp_rw [he0] at Hnorm
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hdata] with n hn
    exact ha.trans_le hn.2.1
  · intro a ha
    filter_upwards [hdata,Hnorm.eventually (gt_mem_nhds ha)] with n hn hnq
    have hx2 : (x n)^2 ≤ 1 := by nlinarith only [hn.2.2.1,hn.2.2.2.1]
    have Hmul := mul_le_mul_of_nonneg_left hx2 hn.2.1
    have Hle : lam n ≤ lam n/(x n)^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hn.2.2.1)).mpr
      simpa only [mul_one] using Hmul
    exact Hle.trans_lt hnq

namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ} {N : ℕ→ℕ}

theorem comparison_parameter_tendsto_zero_of_weak_bounded_call
    (P : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ→ℝ) (hx : ∀n,0 < x n) (hxunit : ∀ᶠn in atTop,x n ≤ 1)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (P n).context.d (P n).lam (x n)/(x n)^2)
      atTop (𝓝 0)) : Tendsto (fun n=>(P n).lam) atTop (𝓝 0) :=
  actual_comparison_parameter_tendsto_zero_of_weak_bounded_call
    (hxunit.mono (fun n hn=>⟨(P n).context.hd,(P n).hlam.le,hx n,hn,(P n).hld⟩)) hweak

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
