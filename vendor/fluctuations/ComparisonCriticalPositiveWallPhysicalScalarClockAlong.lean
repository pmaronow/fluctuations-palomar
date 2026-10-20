module

public import ComparisonCriticalPositiveWallPhysicalScalarClock

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology

theorem eventually_actual_positive_wall_scaled_radius_scalar_clock_exact
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hrmin : Tendsto (fun n=>(M n).data.rmin/(M n).xs) atTop (𝓝 0))
    {a b : ℝ} (ha : 0 < a) :
    ∀ᶠn in atTop,∀t∈Icc a b,
      actualMixedClock (dim n+1) (M n).bf (M n).hf
        ((M n).alpha.val.val ((M n).xs*t)) =
      comparisonNativeScalarClock 0 (M n).data.T
        ((M n).data.g ((M n).xs*t)) ((M n).xs*t)
        ((M n).radiusS ((M n).xs*t)) := by
  have Hlow : ∀ᶠn in atTop,(M n).data.rmin < (M n).xs*a := by
    filter_upwards [hrmin.eventually (gt_mem_nhds ha)] with n hn
    simpa only [mul_comm] using (div_lt_iff₀ (M n).hxs).mp hn
  have Hhigh : ∀ᶠn in atTop,(M n).xs*b ≤ 1 := by
    have H : Tendsto (fun n=>(M n).xs*b) atTop (𝓝 0) := by
      simpa only [zero_mul] using hx.mul_const b
    exact H.eventually (eventually_le_nhds zero_lt_one)
  filter_upwards [Hlow,Hhigh] with n hnlow hnhigh t ht
  apply (M n).actual_positive_wall_radius_scalar_clock_exact
  exact ⟨hnlow.le.trans (mul_le_mul_of_nonneg_left ht.1 (M n).hxs.le),
    (mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hnhigh⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
