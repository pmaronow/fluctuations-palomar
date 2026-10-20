module

public import ComparisonActualHighOnlyWallHistoryContext
public import ComparisonActualHighWallNativeChildPullback

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option maxHeartbeats 14000000
set_option linter.unusedVariables false
namespace ActualHighWallData
variable {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta)

theorem changed_pullback_on_zero_origin_high_only (alpha : a.Profile)
    {N : ℕ} {m deltac cl cu Az C0 Ct D Bclock : ℝ}
    (Q : ActualHighOnlyOverlapMinimum N m deltac cl cu Az C0 Ct D Bclock)
    (hzero : Q.data.s = 0) :
    NativePullbackClockRegularity Q.alpha.val.val (a.b alpha) (a.h alpha) 0 1 := by
  let cut := Q.R a.s
  have Hcut : cut ∈ Icc (0 : ℝ) 1 := omittedSweepQuantile_bounds zero_le_one ⟨Q.data.hs.1,Q.data.hs1⟩
    Q.data.hc Q.data.hk Q.data.hkc Q.data.hm Q.data.hM Q.alpha a.s
  have Hspec : Q.alpha.val.val cut = a.s := omittedSweepQuantile_spec zero_le_one ⟨Q.data.hs.1,Q.data.hs1⟩
    Q.data.hc Q.data.hk Q.data.hkc Q.data.hm Q.data.hM Q.alpha ⟨by rw [hzero]; exact a.hs.1.le,a.hs1⟩
  have Halpha := inverseIntegralConstraints_lipschitz Q.data.hm Q.data.hM Q.alpha.property
  refine Or.inr ⟨cut,?_⟩
  intro l r hl hlr hr hside
  have Hl : l ∈ Icc (0 : ℝ) 1 := ⟨hl,hlr.trans hr⟩
  have Hr : r ∈ Icc (0 : ℝ) 1 := ⟨hl.trans hlr,hr⟩
  have Hside : Q.alpha.val.val r < a.s ∨ a.s ≤ Q.alpha.val.val l := by
    rcases hside with Hleft|Hright
    · have H := inverseConstraint_strictMonoOn Q.data.hc Q.data.hk Q.data.hkc Q.alpha.property Hr Hcut Hleft
      exact Or.inl (by simpa only [Hspec] using H)
    · exact Or.inr (by simpa only [Hspec] using Q.alpha.val.property.2 Hright)
  obtain ⟨Kb,Kh,Hb,Hh⟩ := a.changed_clocks_mass_cut_branches alpha (Q.alpha.val.val l) (Q.alpha.val.val r)
    (Q.alpha.val.property.1 l).1 (Q.alpha.val.property.2 hlr) (Q.alpha.val.property.1 r).2 Hside
  have Hmap : MapsTo Q.alpha.val.val (Icc l r) (Icc (Q.alpha.val.val l) (Q.alpha.val.val r)) := by
    intro x hx
    exact ⟨Q.alpha.val.property.2 hx.1,Q.alpha.val.property.2 hx.2⟩
  have Ha := Halpha.mono (Icc_subset_Icc hl hr)
  have HB := Hb.comp Ha Hmap
  have HH := Hh.comp Ha Hmap
  refine ⟨Kb*⟨Q.data.M 1,Q.data.hM⟩,Kh*⟨Q.data.M 1,Q.data.hM⟩,?_,?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [←(a.clock_coe alpha (Q.alpha.val.property.1 x)).1,
      ←(a.clock_coe alpha (Q.alpha.val.property.1 y)).1]
    exact HB.dist_le_mul x hx y hy
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [←(a.clock_coe alpha (Q.alpha.val.property.1 x)).2,
      ←(a.clock_coe alpha (Q.alpha.val.property.1 y)).2]
    exact HH.dist_le_mul x hx y hy

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
