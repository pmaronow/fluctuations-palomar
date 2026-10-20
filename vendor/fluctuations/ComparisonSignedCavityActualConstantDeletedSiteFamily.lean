module

public import ComparisonSignedCavityActualHistoryDeletedSiteForestAlong
public import ComparisonSignedCavityActualConstantSourceChildrenTerminalAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem actual_constant_deleted_site_category_family_abs_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp : ℝ}
    {as : List PositiveMass} {star U : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (ho : MassOrdered 0 as) (hs : star < U) (hU : U ≤ as.length)
    (W B : ℝ) (depth : ℕ) (hB : 0 ≤ B)
    (H : ∀Q∈nativeActualConstantSourceChildren M as star U hs hU,
      |nativeActualFourOtherCategorySum M U W
        (nativeActualMinimumFourCenteredForest M hs hU W depth [Q]) .deletedSite| ≤
        |Q.term.coefficient| *B) :
    |nativeActualFourOtherCategorySum M U W
      (nativeActualMinimumFourCenteredForest M hs hU W depth
        (nativeActualConstantSourceChildren M as star U hs hU)) .deletedSite| ≤ 6*B := by
  let xs:=nativeActualConstantSourceChildren M as star U hs hU
  let F:=fun (Q : NativeActualResourceState (Spin n×Bool) as 0 star)=>
    nativeActualFourOtherCategorySum M U W
      (nativeActualMinimumFourCenteredForest M hs hU W depth [Q]) .deletedSite
  have HD : nativeActualMinimumFourCenteredForest M hs hU W depth xs=
      xs.flatMap (fun Q=>nativeActualMinimumFourCenteredForest M hs hU W depth [Q]):=by
    unfold nativeActualMinimumFourCenteredForest
    exact nativeActualFourCenteredForest_eq_flatMap_singletons _ _ _ _ _ _
  unfold nativeActualFourOtherCategorySum
  rw [HD,List.map_flatMap,native_sum_flatMap]
  apply (native_abs_sum_map_le xs F).trans
  apply (List.sum_le_sum H).trans
  rw [List.sum_map_mul_right]
  exact mul_le_mul_of_nonneg_right
    (nativeActualConstantSourceChildren_coefficient_variation M htotal ho hs hU) hB

end OAI.SKFluctuations.Cavity
