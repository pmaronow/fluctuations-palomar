module

public import ComparisonActualHighWallThetaZeroNativeChildPullback
public import ComparisonActualHighWallThetaZeroMacroscopicAllMassExclusion
public import ComparisonActualHighOnlyOverlapMinimum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace ActualThetaZeroOverlapMinimum
variable {n N : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {m' delta' cl' cu' Az' C0' Ct' D' Bclock' : ℝ}

theorem changed_pullback_on_high_only_profile
    (M : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (a : ActualHighOnlyComparisonData N delta') (alpha : a.Profile)
    (hsame : a.s = M.data.s) :
    NativePullbackClockRegularity alpha.val.val M.changedBare M.changedField 0 1 := by
  obtain ⟨Kb,Kh,Hb,Hh⟩ := M.changed_clocks_mass_cut_branches
    M.data.s 1 M.data.hs.1.le M.data.hs1 le_rfl (Or.inr le_rfl)
  have Ha := inverseIntegralConstraints_lipschitz a.hm a.hM alpha.property
  have Hmap : MapsTo alpha.val.val (Icc (0 : ℝ) 1) (Icc M.data.s 1) := by
    intro r hr
    refine ⟨?_,(alpha.val.property.1 r).2⟩
    have H := alpha.val.property.2 hr.1
    rw [alpha.property.1,hsame] at H
    exact H
  have HB := Hb.comp Ha Hmap
  have HH := Hh.comp Ha Hmap
  refine Or.inl ⟨Kb * ⟨a.M 1,a.hM⟩,
    Kh * ⟨a.M 1,a.hM⟩,?_,?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro r hr t ht
    exact HB.dist_le_mul r hr t ht
  · apply LipschitzOnWith.of_dist_le_mul
    intro r hr t ht
    exact HH.dist_le_mul r hr t ht

theorem changed_pullback_on_high_only_child_profile
    (M : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (Q : ActualHighOnlyOverlapMinimum N m' delta' cl' cu' Az' C0' Ct' D' Bclock')
    (hsame : Q.data.s = M.data.s) :
    NativePullbackClockRegularity Q.alpha.val.val M.changedBare M.changedField 0 1 :=
  M.changed_pullback_on_high_only_profile Q.data Q.alpha hsame

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
