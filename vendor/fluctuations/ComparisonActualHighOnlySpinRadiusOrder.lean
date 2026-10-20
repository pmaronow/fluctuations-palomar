module

public import ComparisonActualHighOnlyAnalyticBasics
public import ComparisonActualHighOnlyPairedFarSchedule

@[expose] public section
noncomputable section
set_option autoImplicit false
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ} {n : ℕ}
theorem high_mass_of_radius_pos
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hR : 0<M.R u) : M.data.s≤u := by
  by_contra h
  have H:=M.R_monotone (le_of_not_ge h)
  have Hl:=omittedSweepQuantile_left zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
    M.context.hc M.context.hk M.context.hkc M.context.hm M.context.hM M.alpha
  change M.R M.data.s=0 at Hl
  linarith
theorem mass_mean_le_radius_mean_of_radius_le
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u r : ℝ} (hu : u∈Icc (0:ℝ) 1) (hur : M.R u≤r) :
    orderedPathS (n+1) M.bf M.hf u≤orderedPathS (n+1) M.bf M.hf (M.alpha.val.val r) := by
  have H : u≤M.alpha.val.val r := by
    by_cases hs : M.data.s≤u
    · have HH:=M.alpha.val.property.2 hur
      rw [omittedSweepQuantile_spec zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
        M.context.hc M.context.hk M.context.hkc M.context.hm M.context.hM M.alpha ⟨hs,hu.2⟩] at HH
      exact HH
    · have hr0 : 0≤r := (M.R_bounds u).1.trans hur
      have HH:=M.alpha.val.property.2 hr0
      rw [M.alpha.property.1] at HH
      exact (le_of_not_ge hs).trans HH
  exact M.mass_mean_monotone hu (M.alpha.val.property.1 r) H
theorem radius_mean_le_mass_mean_of_le_radius
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u r : ℝ} (hu : u∈Icc (0:ℝ) 1) (hhigh : M.data.s≤u) (hur : r≤M.R u) :
    orderedPathS (n+1) M.bf M.hf (M.alpha.val.val r)≤orderedPathS (n+1) M.bf M.hf u := by
  have H:=M.alpha.val.property.2 hur
  rw [omittedSweepQuantile_spec zero_le_one ⟨M.data.hs.1,M.data.hs1⟩
    M.context.hc M.context.hk M.context.hkc M.context.hm M.context.hM M.alpha ⟨hhigh,hu.2⟩] at H
  exact M.mass_mean_monotone (M.alpha.val.property.1 r) hu H
end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
