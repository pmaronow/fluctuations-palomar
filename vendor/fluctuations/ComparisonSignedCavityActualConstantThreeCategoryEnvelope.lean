module

public import ComparisonSignedCavityActualConstantPostLongitudinalEnvelope

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 6000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ} {as : List PositiveMass} {star U : ℕ}

def nativeActualSavedJointSourceCategories : List NativeActualOtherSourceCategory :=
  [.gammaRetained,.jointLowRestoration,.jointLowTwoHigh,.fourGLowRestoration]

def nativeActualFinalThreeSourceCategories : List NativeActualOtherSourceCategory :=
  [.gammaHighRestoration,.gammaLowRestoration,.secondLow]

theorem native_actual_post_longitudinal_categories_perm_saved_joint :
    nativeActualPostLongitudinalOtherSourceCategories.Perm
      (nativeActualFinalThreeSourceCategories++nativeActualSavedJointSourceCategories) := by
  decide

def nativeActualConstantSourceThreeCategoryEnvelope
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ) : ℝ :=
  let children:=nativeActualConstantSourceChildren M as star U hs hU
  ((List.range depth).map (fun j=>
    (nativeActualFinalThreeSourceCategories.map (fun cat=>
      |nativeActualFourOtherCategorySum M U W
        (nativeActualMinimumFourCenteredForest M hs hU W j children) cat|)).sum/
      (Real.exp (-4*Temp)*cK*W))).sum

theorem actual_constant_source_post_longitudinal_envelope_joint_paid
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ)
    (err : ℕ→ℝ)
    (H : ∀j < depth,∀cat∈nativeActualSavedJointSourceCategories,
      |nativeActualFourOtherCategorySum M U W
        (nativeActualMinimumFourCenteredForest M hs hU W j
          (nativeActualConstantSourceChildren M as star U hs hU)) cat|/
        (Real.exp (-4*Temp)*cK*W) ≤ err j*M.xs^2) :
    nativeActualConstantSourcePostLongitudinalCategoryEnvelope M hs hU W Temp cK depth ≤
      nativeActualConstantSourceThreeCategoryEnvelope M hs hU W Temp cK depth+
        4*((List.range depth).map err).sum*M.xs^2 := by
  unfold nativeActualConstantSourcePostLongitudinalCategoryEnvelope nativeActualConstantSourceThreeCategoryEnvelope
  have Hrow j (hj : j∈List.range depth) :
      (nativeActualPostLongitudinalOtherSourceCategories.map (fun cat=>
        |nativeActualFourOtherCategorySum M U W
          (nativeActualMinimumFourCenteredForest M hs hU W j
            (nativeActualConstantSourceChildren M as star U hs hU)) cat|)).sum/
        (Real.exp (-4*Temp)*cK*W) ≤
      (nativeActualFinalThreeSourceCategories.map (fun cat=>
        |nativeActualFourOtherCategorySum M U W
          (nativeActualMinimumFourCenteredForest M hs hU W j
            (nativeActualConstantSourceChildren M as star U hs hU)) cat|)).sum/
        (Real.exp (-4*Temp)*cK*W)+4*err j*M.xs^2 := by
    rw [(native_actual_post_longitudinal_categories_perm_saved_joint.map _).sum_eq]
    simp only [List.map_append,List.sum_append,add_div]
    apply add_le_add le_rfl
    have HH:=List.sum_le_sum (fun cat hcat=>H j (List.mem_range.mp hj) cat hcat)
    simp only [nativeActualSavedJointSourceCategories,List.map_cons,List.map_nil,List.sum_cons,
      List.sum_nil,add_zero,add_div] at HH ⊢
    linarith only [HH]
  have HH:=List.sum_le_sum Hrow
  simp only [List.sum_map_add,List.sum_map_mul_right,List.sum_map_mul_left] at HH
  exact HH

end OAI.SKFluctuations.Cavity
