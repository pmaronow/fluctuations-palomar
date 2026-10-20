module

public import ComparisonSignedCavityActualConstantPostTaylorEnvelope
public import ComparisonSignedCavityActualFourLongitudinalRestorationReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 6000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ} {as : List PositiveMass} {star U : ℕ}

def nativeActualPostLongitudinalOtherSourceCategories : List NativeActualOtherSourceCategory :=
  nativeActualPostTaylorOtherSourceCategories.erase .longitudinalLeft |>.erase .longitudinalRight

theorem native_actual_post_Taylor_categories_perm_longitudinal :
    nativeActualPostTaylorOtherSourceCategories.Perm
      (.longitudinalLeft :: .longitudinalRight :: nativeActualPostLongitudinalOtherSourceCategories) := by
  decide

def nativeActualConstantSourcePostLongitudinalCategoryEnvelope
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ) : ℝ :=
  let children:=nativeActualConstantSourceChildren M as star U hs hU
  ((List.range depth).map (fun j=>
    (nativeActualPostLongitudinalOtherSourceCategories.map (fun cat=>
      |nativeActualFourOtherCategorySum M U W
        (nativeActualMinimumFourCenteredForest M hs hU W j children) cat|)).sum/
      (Real.exp (-4*Temp)*cK*W))).sum

theorem actual_constant_source_post_Taylor_envelope_longitudinal_paid
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ)
    (err : ℕ→ℝ)
    (H : ∀j < depth,∀right : Bool,
      |nativeActualFourOtherCategorySum M U W
        (nativeActualMinimumFourCenteredForest M hs hU W j
          (nativeActualConstantSourceChildren M as star U hs hU)) (nativeActualLongitudinalCategory right)|/
        (Real.exp (-4*Temp)*cK*W) ≤ err j*M.xs^2) :
    nativeActualConstantSourcePostTaylorCategoryEnvelope M hs hU W Temp cK depth ≤
      nativeActualConstantSourcePostLongitudinalCategoryEnvelope M hs hU W Temp cK depth+
        2*((List.range depth).map err).sum*M.xs^2 := by
  have HE : nativeActualConstantSourcePostTaylorCategoryEnvelope M hs hU W Temp cK depth=
      nativeActualConstantSourcePostLongitudinalCategoryEnvelope M hs hU W Temp cK depth+
        ((List.range depth).map (fun j=>
          (|nativeActualFourOtherCategorySum M U W
            (nativeActualMinimumFourCenteredForest M hs hU W j
              (nativeActualConstantSourceChildren M as star U hs hU)) .longitudinalLeft|+
           |nativeActualFourOtherCategorySum M U W
            (nativeActualMinimumFourCenteredForest M hs hU W j
              (nativeActualConstantSourceChildren M as star U hs hU)) .longitudinalRight|)/
            (Real.exp (-4*Temp)*cK*W))).sum := by
    unfold nativeActualConstantSourcePostTaylorCategoryEnvelope nativeActualConstantSourcePostLongitudinalCategoryEnvelope
    rw [←List.sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j _
    rw [(native_actual_post_Taylor_categories_perm_longitudinal.map _).sum_eq]
    simp only [List.map_cons,List.sum_cons,add_div]
    ring
  rw [HE]
  apply add_le_add le_rfl
  have Hrow j (hj : j∈List.range depth) := add_le_add (H j (List.mem_range.mp hj) false)
    (H j (List.mem_range.mp hj) true)
  simp only [nativeActualLongitudinalCategory,Bool.false_eq_true,ite_false,ite_true] at Hrow
  have Hsum:=List.sum_le_sum Hrow
  simp only [List.sum_map_add,List.sum_map_mul_right] at Hsum
  simp only [add_div,List.sum_map_add]
  exact Hsum.trans_eq (by ring)

end OAI.SKFluctuations.Cavity
