module

public import ComparisonActualHighWallThetaZeroHighOnlyChildPullback

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal

namespace ActualThetaZeroOverlapMinimum
variable {n N : ℕ} {m delta cl cu Az C0 Ct D Bclock deltaChild : ℝ}

theorem changed_pullback_on_zero_mass_high_only_profile_original_q
    (M : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (child : ActualHighOnlyComparisonData N deltaChild)
    (beta : child.Profile) (hzero : child.s = 0) :
    NativePullbackClockRegularity beta.val.val
      M.changedBare M.changedField 0 1 := by
  let cut := child.R beta M.data.s
  have Hcut : cut ∈ Icc (0:ℝ) 1 :=
    omittedSweepQuantile_bounds zero_le_one
      ⟨child.hs.1,child.hs1⟩ child.hc child.hk child.hkc
      child.hm child.hM beta M.data.s
  have Hspec : beta.val.val cut = M.data.s :=
    omittedSweepQuantile_spec zero_le_one
      ⟨child.hs.1,child.hs1⟩ child.hc child.hk child.hkc
      child.hm child.hM beta
      ⟨by rw [hzero]; exact M.data.hs.1.le,M.data.hs1⟩
  have Hbeta := inverseIntegralConstraints_lipschitz child.hm child.hM
    beta.property
  refine Or.inr ⟨cut,?_⟩
  intro l r hl hlr hr hside
  have Hl : l∈Icc (0:ℝ) 1 := ⟨hl,hlr.trans hr⟩
  have Hr : r∈Icc (0:ℝ) 1 := ⟨hl.trans hlr,hr⟩
  have Hside : beta.val.val r < M.data.s ∨
      M.data.s ≤ beta.val.val l := by
    rcases hside with Hleft | Hright
    · have H := inverseConstraint_strictMonoOn child.hc child.hk
        child.hkc beta.property Hr Hcut Hleft
      exact Or.inl (by simpa only [Hspec] using H)
    · exact Or.inr (by simpa only [Hspec] using
        beta.val.property.2 Hright)
  obtain ⟨Kb,Kh,Hb,Hh⟩ := M.changed_clocks_mass_cut_branches
    (beta.val.val l) (beta.val.val r) (beta.val.property.1 l).1
    (beta.val.property.2 hlr) (beta.val.property.1 r).2 Hside
  have Hmap : MapsTo beta.val.val (Icc l r)
      (Icc (beta.val.val l) (beta.val.val r)) := by
    intro x hx
    exact ⟨beta.val.property.2 hx.1,beta.val.property.2 hx.2⟩
  have Ha := Hbeta.mono (Icc_subset_Icc hl hr)
  exact ⟨Kb*⟨child.M 1,child.hM⟩,Kh*⟨child.M 1,child.hM⟩,
    Hb.comp Ha Hmap,Hh.comp Ha Hmap⟩

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
