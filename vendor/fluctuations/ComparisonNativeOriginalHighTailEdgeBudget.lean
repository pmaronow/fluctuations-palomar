module

public import ComparisonNativeOriginalLowErrorEdgeBudget
public import ComparisonSignedCavityActualLowErrorDensity

@[expose] public section

noncomputable section
set_option maxHeartbeats 13000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem native_edgeBudget_eq_cells_add_terminal (a : ℝ) (as : List PositiveMass) (f : ℕ→ℝ) :
    ClockTree.edgeBudget a as f=massCellSum as a f+(1-partitionEnd a as)*f as.length := by
  induction as generalizing a f with
  | nil=>simp only [ClockTree.edgeBudget,massCellSum,partitionEnd,List.length_nil,zero_add]
  | cons b bs ih=>
    simp only [ClockTree.edgeBudget,massCellSum,partitionEnd,List.length_cons,ih]
    rw [Nat.add_comm 1 bs.length]
    simp only [Nat.add_comm,add_assoc]

theorem native_high_edgeBudget_eq_tail_integral {as : List PositiveMass}
    (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1) (U : ℕ) (hU : U≤as.length)
    (f : ℕ→ℝ) :
    ClockTree.edgeBudget 0 as (fun j=>if j<U then 0 else f j)=
      (∫u in partitionPoint 0 as U..1,massStepFunction as f u) := by
  have Hfunc : (fun j=>(if j<U then 0 else f j)+(if j<U then f j else 0))=f := by
    funext j
    split_ifs <;> simp only [zero_add,add_zero]
  have Hbudget:=Cavity.actual_low_edgeBudget_linear as 0 1 1
    (fun j=>if j<U then 0 else f j) (fun j=>if j<U then f j else 0)
  simp only [one_mul] at Hbudget
  rw [Hfunc,native_low_edgeBudget_eq_prefix_integral ho U hU,
    native_edgeBudget_eq_cells_add_terminal,he,sub_self,zero_mul,add_zero,
    massCellSum_eq_integral as ho f,he] at Hbudget
  have Hints:=intervalIntegral.integral_add_adjacent_intervals
    (massStepFunction_intervalIntegrable as f 0 (partitionPoint 0 as U))
    (massStepFunction_intervalIntegrable as f (partitionPoint 0 as U) 1)
  linarith only [Hbudget,Hints]

theorem native_original_high_second_edgeBudget_eq_integral (n : ℕ) (b h : ℝ→ℝ≥0)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    (U : ℕ) (hU : U≤as.length) :
    ClockTree.edgeBudget 0 as
      (fun j=>if j<U then 0 else (nativeOriginalCutLowErrorRadius n b h as j)^2)=
      (∫u in partitionPoint 0 as U..1,physicalSampledCutLowErrorSecond n b h as ho u) := by
  have Hsquare j : (nativeOriginalCutLowErrorRadius n b h as j)^2=
      nativeOriginalCutLowErrorSecond n b h as j := by
    exact Real.sq_sqrt (nativeOriginalCutLowErrorSecond_nonneg n b h ho j)
  simp_rw [Hsquare]
  rw [native_high_edgeBudget_eq_tail_integral ho he U hU]
  apply intervalIntegral.integral_congr
  intro u _
  exact (physicalSampledCutLowErrorSecond_eq_massStepFunction n b h as ho u).symm

end OAI.SKFluctuations.LaplaceWindowFormalization
