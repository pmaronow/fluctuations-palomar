module

public import ComparisonActualHighWallThetaZeroEq7FiniteMaskDefs
public import ComparisonActualHighWallThetaZeroBroadBudgets

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem eq7_inner_dyad_common_scalar_geometry_draft
    {h C : ℝ} (j : Eq7InnerDyad Q h)
    (hC : 0 ≤ C)
    (hvA : Q.eq7InnerDyadMass j.val ≤ C*Q.xs) :
    let v := Q.eq7InnerDyadMass j.val
    let u := Q.eq7InnerDyadRight j.val
    let y := Q.xs+u
    comparisonSmallMass Q.data.N Q.data.E ≤ v ∧
    comparisonSmallMass Q.data.N Q.data.E ≤ 16*v ∧
    u ∈ Set.Icc (0:ℝ) 1 ∧
    u ≤ 16*C*Q.xs ∧
    0 < y ∧ y ≤ (1+16*C)*Q.xs := by
  let v := Q.eq7InnerDyadMass j.val
  let u := Q.eq7InnerDyadRight j.val
  let y := Q.xs+u
  have hv := comparison_mass_dyadic_scale Q.data.hU j.val
  have hvp : 0 < v := hv.1
  have hU : comparisonSmallMass Q.data.N Q.data.E ≤ v := hv.2.1
  have hU16 : comparisonSmallMass Q.data.N Q.data.E ≤ 16*v := by
    linarith only [hU,hvp]
  have hu0 : 0 ≤ u := by
    dsimp only [u,eq7InnerDyadRight]
    exact le_min
      (mul_nonneg (by norm_num) hv.1.le) zero_le_one
  have hu1 : u ≤ 1 := by
    dsimp only [u,eq7InnerDyadRight]
    exact min_le_right _ _
  have huV : u ≤ 16*v := by
    dsimp only [u,eq7InnerDyadRight]
    exact min_le_left _ _
  have huA : u ≤ 16*C*Q.xs := by
    have H := mul_le_mul_of_nonneg_left hvA (by norm_num : (0:ℝ) ≤ 16)
    linarith only [huV,H]
  have hy0 : 0 < y := by dsimp only [y]; linarith only [Q.hxs,hu0]
  have hyA : y ≤ (1+16*C)*Q.xs := by
    dsimp only [y]
    nlinarith only [huA]
  exact ⟨hU,hU16,⟨hu0,hu1⟩,huA,hy0,hyA⟩

theorem eq7_inner_low_mass_le_carrier_draft
    {h C : ℝ} (j : Eq7InnerLowDyad Q h)
    (hC : 2 ≤ C) :
    Q.eq7InnerDyadMass j.val.val ≤ C*Q.xs := by
  have H1 : Q.eq7InnerDyadMass j.val.val ≤ 2*Q.xs :=
    (j.property.2.1).trans
      (mul_le_mul_of_nonneg_left Q.hsxs (by norm_num))
  have H2 := mul_le_mul_of_nonneg_right hC Q.hxs.le
  nlinarith only [H1,H2]

theorem eq7_inner_post_mass_le_carrier_draft
    {h C : ℝ} (j : Eq7InnerPostDyad Q h)
    (hh : h ≤ C*Q.xs) :
    Q.eq7InnerDyadMass j.val.val ≤ C*Q.xs :=
  j.val.property.trans hh

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
