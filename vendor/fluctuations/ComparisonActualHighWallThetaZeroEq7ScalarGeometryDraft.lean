module

public import ComparisonActualHighWallThetaZeroEq7FiniteMaskDefs
public import ComparisonActualHighWallThetaZeroBroadBudgets

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
variable {P : Q.Potential}

theorem eq7_inner_low_band_mass_le_thirty_two_wall_draft
    {h : ℝ} (j : Eq7InnerLowDyad Q h) :
    16*Q.eq7InnerDyadMass j.val.val ≤ 32*Q.data.s := by
  linarith only [j.property.2.1]

theorem eq7_inner_post_band_mass_le_sixteen_start_draft
    {h : ℝ} (j : Eq7InnerPostDyad Q h) :
    16*Q.eq7InnerDyadMass j.val.val ≤
      16*Q.eq7InnerWallStart j.val.val := by
  dsimp only [eq7InnerWallStart]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num)

theorem eq7_inner_relevant_broad_scale_bounds_draft
    {ι : Type*} (c : ι → ShiftedCapInterval Q P)
    {h : ℝ} (hhi : h ≤ 1)
    (p : Eq7InnerRelevantBroadSlice c h) :
    comparisonSmallMass Q.data.N Q.data.E ≤
      (eq7InnerBroadSampler c p.val.1).scale p.val.2 ∧
    (eq7InnerBroadSampler c p.val.1).scale p.val.2 ≤ 2*h := by
  let f := eq7InnerBroadSampler c p.val.1
  let i := p.val.2
  obtain ⟨u,hu,hr⟩ := p.property
  have hm : u ∈ Icc Q.data.s 1 := ⟨hu.1,hu.2.trans hhi⟩
  have hspec := Q.shiftedNativeModel.R_spec hm
  have hnodes := f.nodes_mem i
  have hprofile := Q.shiftedNativeModel.massSlice_profile_mem
    hnodes.1 hnodes.2 hr
  have hg := f.geometry i
  constructor
  · exact (le_max_left _ _).trans hg.1
  · rw [hspec] at hprofile
    linarith only [hg.2.2.1,hprofile.1,hu.2]

theorem eq7_inner_broad_budget_native_expansion_draft
    (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Qraw Lside cut v width : ℝ) :
    let loss := (32:ℝ)^2+
      Q.criticalBroadTraceLoss 4 v (min (4*v) 1)+1
    let power := Q.criticalBroadMassPower v
    let diam := Q.criticalBroadMassDiameter
    let rev := Q.criticalBroadMassReverse ell Qraw v
    Q.criticalBroadMassBudget ell Qraw Lside cut v width =
      48*(108*loss*(Real.log Q.data.N)^2/(power*(v/4))*
        Real.log (width/cut))+
      (76+64*Lside)*width*diam^2+32*width*rev+
      (66+64*Lside+65536*(1+Lside)^2)*
        (54*loss*(Real.log Q.data.N)^2*width/(power*(v/4)^2))+
      16*cut := by
  simp only [criticalBroadMassBudget,nativeConditionalLedgerBudget,Nat.cast_one,mul_one]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
