module

public import ComparisonActualHighWallBarePullback
public import ComparisonNativeActualRegularChildSelection

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 14000000
namespace ActualHighWallData
variable {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta)

theorem changed_pullback_on_native_child_profile (alpha : a.Profile)
    {N : ℕ} {deltaChild : ℝ} (child : NativeChildBarrierParameters N deltaChild)
    (beta : child.Profile) :
    NativePullbackClockRegularity beta.val.val (a.b alpha) (a.h alpha) 0 1 := by
  let cut := child.R beta a.s
  have Hcut : cut ∈ Icc (0 : ℝ) 1 := comparisonSweepQuantile_bounds
    child.hc child.hk child.hkc child.hm child.hM beta a.s
  have Hspec : beta.val.val cut = a.s := comparisonSweepQuantile_spec
    child.hc child.hk child.hkc child.hm child.hM beta ⟨a.hs.1.le,a.hs1⟩
  have Halpha := inverseIntegralConstraints_lipschitz child.hm child.hM beta.property
  refine Or.inr ⟨cut,?_⟩
  intro l r hl hlr hr hside
  have Hl : l ∈ Icc (0 : ℝ) 1 := ⟨hl,hlr.trans hr⟩
  have Hr : r ∈ Icc (0 : ℝ) 1 := ⟨hl.trans hlr,hr⟩
  have Hside : beta.val.val r < a.s ∨ a.s ≤ beta.val.val l := by
    rcases hside with Hleft|Hright
    · have H := inverseConstraint_strictMonoOn child.hc child.hk child.hkc beta.property Hr Hcut Hleft
      exact Or.inl (by simpa only [Hspec] using H)
    · exact Or.inr (by simpa only [Hspec] using beta.val.property.2 Hright)
  obtain ⟨Kb,Kh,Hb,Hh⟩ := a.changed_clocks_mass_cut_branches alpha (beta.val.val l) (beta.val.val r)
    (beta.val.property.1 l).1 (beta.val.property.2 hlr) (beta.val.property.1 r).2 Hside
  have Hmap : MapsTo beta.val.val (Icc l r) (Icc (beta.val.val l) (beta.val.val r)) := by
    intro x hx
    exact ⟨beta.val.property.2 hx.1,beta.val.property.2 hx.2⟩
  have Ha := Halpha.mono (Icc_subset_Icc hl hr)
  have HB := Hb.comp Ha Hmap
  have HH := Hh.comp Ha Hmap
  refine ⟨Kb*⟨child.M 1,child.hM⟩,Kh*⟨child.M 1,child.hM⟩,?_,?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [←(a.clock_coe alpha (beta.val.property.1 x)).1,
      ←(a.clock_coe alpha (beta.val.property.1 y)).1]
    exact HB.dist_le_mul x hx y hy
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [←(a.clock_coe alpha (beta.val.property.1 x)).2,
      ←(a.clock_coe alpha (beta.val.property.1 y)).2]
    exact HH.dist_le_mul x hx y hy

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
