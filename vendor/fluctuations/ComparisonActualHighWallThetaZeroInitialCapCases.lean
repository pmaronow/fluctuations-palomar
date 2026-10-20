module

public import ComparisonActualHighWallThetaZeroWholeCapSamplerPositiveOrigin

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal
set_option autoImplicit false
namespace ActualThetaZeroOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : Q.Potential} (c : ShiftedCapInterval Q P)

theorem initial_cap_analytic_cases (hinitial : c.left=Q.data.rmin) :
    Q.alpha.val.val c.right-Q.data.s≤comparisonSmallMass Q.data.N Q.data.E ∨
    (comparisonSmallMass Q.data.N Q.data.E≤Q.alpha.val.val c.right-Q.alpha.val.val c.left ∧
      Q.alpha.val.val c.right≤8*Q.positiveOriginMassCoverBase) ∨
    Nonempty (PositiveOriginWholeCapBroadSampler c) := by
  let U:=comparisonSmallMass Q.data.N Q.data.E
  let base:=Q.positiveOriginMassCoverBase
  have hleft : Q.alpha.val.val c.left=Q.data.s:=by
    rw [hinitial]
    exact Q.alpha.property.1
  by_cases hshort : Q.alpha.val.val c.right-Q.data.s≤U
  · exact Or.inl hshort
  · have hU : U≤Q.alpha.val.val c.right-Q.alpha.val.val c.left:=by
      rw [hleft]
      exact le_of_lt (lt_of_not_ge hshort)
    by_cases hmoderate : Q.alpha.val.val c.right≤8*base
    · exact Or.inr (Or.inl ⟨hU,hmoderate⟩)
    · have hbroad : 8*max (Q.alpha.val.val c.left) Q.positiveOriginMassCoverBase<
          Q.alpha.val.val c.right:=by
        have hsbase : Q.data.s ≤ Q.positiveOriginMassCoverBase := by
          exact le_max_right _ _
        rw [hleft,max_eq_right hsbase]
        exact lt_of_not_ge hmoderate
      exact Or.inr (Or.inr (exists_critical_whole_cap_broad_sampler c hbroad))

end ActualThetaZeroOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
