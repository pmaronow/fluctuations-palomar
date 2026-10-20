module

public import ComparisonActualHighWallThetaZeroMacroscopicAllMassExclusion

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}

theorem exists_all_mass_child_budget_exact_original_q
    (Q : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hc0 : 0 < c0)
    (hroom : (c0*Q.xs)^2 ≤
      (Q.data.thetaZeroShiftedParentData Q.lam Q.hlam Q.hld).b 0-
      (Q.data.thetaZeroShiftedParentData Q.lam Q.hlam Q.hld).coefficient
        Q.alpha 0) :
    ∃a : ActualShiftedAllMassParentChildCall n delta,
      a.context = Q.data.thetaZeroShiftedParentData Q.lam Q.hlam Q.hld ∧
      HEq a.optimizer Q.shiftedMinimum ∧
      a.R = Q.data.wallRadius Q.alpha ∧
      a.childRadius = c0*Q.xs ∧
      a.childLam = (c0*Q.xs)^2 ∧
      a.childData.E = actualChildErrorBudget n delta c0
        Q.data.d Q.lam Q.xs ∧
      (∀u, a.context.b u-a.coefficient u = Q.changedBare u) ∧
      (∀u, a.context.h u+a.coefficient u*a.R u = Q.changedField u) ∧
      a.err = Q.allMassChildSweepCost hc0 := by
  let P := Q.data.thetaZeroShiftedParentData Q.lam Q.hlam Q.hld
  let child := Q.allMassChildNumerics hc0
  have had := P.clockAdmissible Q.alpha
  obtain ⟨beta,hbeta,_⟩ := variableEndpointComparisonSweepMinimum_attained
    child.hc child.hk child.hkc child.hm child.hM n Q.data.hn
    (fun u => P.b u-P.coefficient Q.alpha u)
    (fun u => P.h u+P.coefficient Q.alpha u*P.R Q.alpha u)
    child.hd.ne' (sq_pos_of_pos (mul_pos hc0 Q.hxs)).le hroom
    had.1 had.2.1 (had.2.2.2 0 ⟨le_rfl,zero_le_one⟩)
    (comparisonCap_continuous _ _ _ _ _ _) (child.profile_nonempty Q.data.hq)
  let a : ActualShiftedAllMassParentChildCall n delta := {
    context := P
    optimizer := Q.shiftedMinimum
    childData := child
    childLam := (c0*Q.xs)^2
    hchildLam := sq_pos_of_pos (mul_pos hc0 Q.hxs)
    hchildLd := le_rfl
    childAlpha := beta
    matrixRoom := hroom
    attained := hbeta }
  refine ⟨a,rfl,HEq.rfl,rfl,rfl,rfl,rfl,?_,?_,rfl⟩
  · intro u
    rfl
  · intro u
    rfl

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
