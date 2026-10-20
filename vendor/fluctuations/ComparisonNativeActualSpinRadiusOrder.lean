module

public import ComparisonNativeActualMeanRawUpper

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ} {n : ℕ}

theorem mass_mean_le_radius_mean_of_radius_le
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u r : ℝ} (hu : u∈Icc (0:ℝ) 1) (hur : M.R u ≤ r) :
    orderedPathS (n+1) M.bf M.hf u ≤ orderedPathS (n+1) M.bf M.hf (M.alpha.val.val r) := by
  have H := M.alpha.val.property.2 hur
  rw [comparisonSweepQuantile_spec M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha hu] at H
  exact M.mass_mean_monotone hu (M.alpha.val.property.1 r) H

theorem radius_mean_le_mass_mean_of_le_radius
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u r : ℝ} (hu : u∈Icc (0:ℝ) 1) (hur : r ≤ M.R u) :
    orderedPathS (n+1) M.bf M.hf (M.alpha.val.val r) ≤ orderedPathS (n+1) M.bf M.hf u := by
  have H := M.alpha.val.property.2 hur
  rw [comparisonSweepQuantile_spec M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha hu] at H
  exact M.mass_mean_monotone (M.alpha.val.property.1 r) hu H

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
