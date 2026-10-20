module

public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQPairedFarSchedule
public import SKProof.Port.OriginalQHighOnlyBridge

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ} {n : ℕ}
theorem high_mass_of_radius_pos
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hR : M.data.rmin<M.sweepRadius u) : M.data.s≤u := by
  exact (M.radius_high_mass hR).le
theorem mass_mean_le_radius_mean_of_radius_le
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u r : ℝ} (hu : u∈Icc (0:ℝ) 1) (hur : M.sweepRadius u≤r) :
    orderedPathS (n+1) M.sweepBf M.sweepHf u≤orderedPathS (n+1) M.sweepBf M.sweepHf (M.alpha.val.val r) := by
  have H : u≤M.alpha.val.val r := by
    by_cases hs : M.data.s≤u
    · have HH:=M.alpha.val.property.2 hur
      rw [M.sweepRadius_spec ⟨hs,hu.2⟩] at HH

      exact HH
    · have hr0 : M.data.rmin≤r := (M.sweepRadius_bounds u).1.trans hur
      have HH:=M.alpha.val.property.2 hr0
      rw [M.alpha.property.1] at HH
      exact (le_of_not_ge hs).trans HH
  exact M.mass_mean_monotone hu (M.alpha.val.property.1 r) H
theorem radius_mean_le_mass_mean_of_le_radius
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u r : ℝ} (hu : u∈Icc (0:ℝ) 1) (hhigh : M.data.s≤u) (hur : r≤M.sweepRadius u) :
    orderedPathS (n+1) M.sweepBf M.sweepHf (M.alpha.val.val r)≤orderedPathS (n+1) M.sweepBf M.sweepHf u := by
  have H:=M.alpha.val.property.2 hur
  rw [M.sweepRadius_spec ⟨hhigh,hu.2⟩] at H

  exact M.mass_mean_monotone (M.alpha.val.property.1 r) hu H
end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
