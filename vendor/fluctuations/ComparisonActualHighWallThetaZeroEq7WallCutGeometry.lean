module

public import ComparisonActualHighWallThetaZeroWholeCapSamplerPositiveOrigin
public import ComparisonActualHighWallThetaZeroInitialCapCases

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 9000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

def eq7WallCutMass : ℝ :=
  Q.data.s+comparisonSmallMass Q.data.N Q.data.E

def eq7WallCutRadius : ℝ := Q.shiftedNativeModel.R Q.eq7WallCutMass

theorem eq7_wall_cut_past_one_strip
    (h : 1 ≤ Q.eq7WallCutMass) :
    1 ≤ Q.data.s+2*comparisonSmallMass Q.data.N Q.data.E := by
  dsimp only [eq7WallCutMass] at h
  linarith only [h, Q.data.hU]

theorem eq7_wall_cut_radius_strict
    (hcut1 : Q.eq7WallCutMass ≤ 1) :
    Q.data.rmin < Q.eq7WallCutRadius := by
  have hsb : Q.data.s < Q.eq7WallCutMass := by
    dsimp only [eq7WallCutMass]
    linarith only [Q.data.hU]
  have hs : Q.data.s ∈ Icc Q.data.s 1 := ⟨le_rfl, Q.data.hs1⟩
  have hb : Q.eq7WallCutMass ∈ Icc Q.data.s 1 :=
    ⟨hsb.le, hcut1⟩
  have H := Q.shiftedNativeModel.R_strictMonoOn hs hb hsb
  rw [Q.shiftedNativeModel.R_left] at H
  exact H

theorem eq7_wall_crossing_cap_unique
    {P : Q.Potential} {ι : Type*}
    (c : ι → ShiftedCapInterval Q P)
    (hd : Pairwise (fun i j => Disjoint
      (Ioo (c i).left (c i).right) (Ioo (c j).left (c j).right)))
    {i j : ι}
    (hi : Q.eq7WallCutRadius ∈ Ioo (c i).left (c i).right)
    (hj : Q.eq7WallCutRadius ∈ Ioo (c j).left (c j).right) :
    i = j := by
  by_contra hne
  exact Set.disjoint_left.mp (hd hne) hi hj

theorem eq7_wall_cap_above_cut_cases
    {P : Q.Potential} {ι : Type*}
    (c : ι → ShiftedCapInterval Q P)
    {i : ι} {r : ℝ}
    (hr : r ∈ Ioo (c i).left (c i).right)
    (hcut : Q.eq7WallCutRadius < r) :
    Q.eq7WallCutRadius ∈ Ioo (c i).left (c i).right ∨
      Q.eq7WallCutRadius ≤ (c i).left := by
  by_cases hleft : (c i).left < Q.eq7WallCutRadius
  · exact Or.inl ⟨hleft, hcut.trans hr.2⟩
  · exact Or.inr (le_of_not_gt hleft)

theorem eq7_wall_crossing_cap_moderate_or_broad
    {P : Q.Potential} (cap : ShiftedCapInterval Q P)
    (hcut1 : Q.eq7WallCutMass ≤ 1)
    (hleft : cap.left ≤ Q.eq7WallCutRadius) :
    Q.alpha.val.val cap.right ≤ 8*Q.eq7WallCutMass ∨
      Nonempty (PositiveOriginWholeCapBroadSampler cap) := by
  have hb : Q.eq7WallCutMass ∈ Icc Q.data.s 1 := by
    dsimp only [eq7WallCutMass]
    exact ⟨by linarith [Q.data.hU], hcut1⟩
  have hαleft : Q.alpha.val.val cap.left ≤ Q.eq7WallCutMass := by
    have H := Q.alpha.val.property.2 hleft
    change Q.alpha.val.val cap.left ≤
      Q.shiftedNativeModel.alpha.val.val (Q.shiftedNativeModel.R Q.eq7WallCutMass) at H
    rw [Q.shiftedNativeModel.R_spec hb] at H
    exact H
  have hbase : Q.positiveOriginMassCoverBase ≤ Q.eq7WallCutMass := by
    dsimp only [positiveOriginMassCoverBase,eq7WallCutMass]
    exact max_le (by linarith [Q.data.hs.1]) (by linarith [Q.data.hU])
  by_cases hbroad :
      8*max (Q.alpha.val.val cap.left) Q.positiveOriginMassCoverBase <
        Q.alpha.val.val cap.right
  · exact Or.inr (exists_critical_whole_cap_broad_sampler cap hbroad)
  · have H : max (Q.alpha.val.val cap.left)
        Q.positiveOriginMassCoverBase ≤ Q.eq7WallCutMass :=
      max_le hαleft hbase
    exact Or.inl (by linarith only [le_of_not_gt hbroad, H])

theorem eq7_wall_moderate_retained_width
    {P : Q.Potential} (cap : ShiftedCapInterval Q P)
    (hfar : Q.data.s+2*comparisonSmallMass Q.data.N Q.data.E <
      Q.alpha.val.val cap.right) :
    comparisonSmallMass Q.data.N Q.data.E <
      Q.alpha.val.val cap.right-Q.eq7WallCutMass := by
  dsimp only [eq7WallCutMass]
  linarith only [hfar]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
