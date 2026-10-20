module

public import ComparisonSignedCavityActualConstantPendingCategoryEnvelope

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 4000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ} {as : List PositiveMass} {star U : ℕ}

def nativeActualPostTaylorOtherSourceCategories : List NativeActualOtherSourceCategory :=
  nativeActualPendingOtherSourceCategories.erase .higherTaylor

theorem native_actual_pending_categories_perm_higher_Taylor :
    nativeActualPendingOtherSourceCategories.Perm
      (.higherTaylor :: nativeActualPostTaylorOtherSourceCategories) := by
  decide

def nativeActualConstantSourcePostTaylorCategoryEnvelope
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ) : ℝ :=
  let children:=nativeActualConstantSourceChildren M as star U hs hU
  ((List.range depth).map (fun j=>
    (nativeActualPostTaylorOtherSourceCategories.map (fun cat=>
      |nativeActualFourOtherCategorySum M U W
        (nativeActualMinimumFourCenteredForest M hs hU W j children) cat|)).sum/
      (Real.exp (-4*Temp)*cK*W))).sum

theorem actual_constant_source_pending_envelope_higher_Taylor_paid
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ)
    (err : ℕ→ℝ)
    (H : ∀j < depth,
      |nativeActualFourOtherCategorySum M U W
        (nativeActualMinimumFourCenteredForest M hs hU W j
          (nativeActualConstantSourceChildren M as star U hs hU)) .higherTaylor|/
        (Real.exp (-4*Temp)*cK*W) ≤ err j*M.xs^2) :
    nativeActualConstantSourcePendingCategoryEnvelope M hs hU W Temp cK depth ≤
      nativeActualConstantSourcePostTaylorCategoryEnvelope M hs hU W Temp cK depth+
        ((List.range depth).map err).sum*M.xs^2 := by
  have HE : nativeActualConstantSourcePendingCategoryEnvelope M hs hU W Temp cK depth=
      nativeActualConstantSourcePostTaylorCategoryEnvelope M hs hU W Temp cK depth+
        ((List.range depth).map (fun j=>
          |nativeActualFourOtherCategorySum M U W
            (nativeActualMinimumFourCenteredForest M hs hU W j
              (nativeActualConstantSourceChildren M as star U hs hU)) .higherTaylor|/
            (Real.exp (-4*Temp)*cK*W))).sum := by
    unfold nativeActualConstantSourcePendingCategoryEnvelope nativeActualConstantSourcePostTaylorCategoryEnvelope
    rw [←List.sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j _
    rw [(native_actual_pending_categories_perm_higher_Taylor.map _).sum_eq]
    simp only [List.map_cons,List.sum_cons,add_div]
    ring
  rw [HE]
  apply add_le_add le_rfl
  apply (List.sum_le_sum (fun j hj=>H j (List.mem_range.mp hj))).trans_eq
  exact List.sum_map_mul_right _ _ _

theorem actual_saved_denominator_upper_transfer
    {a d W R B err x : ℝ} (hd : 0 < d) (hW : 0 < W) (hB : 0 < B)
    (herr : 0 ≤ err) (hdu : d ≤ R*W) (H : |a|/d ≤ err*x^2) :
    |a|/(B*W) ≤ (R/B*err)*x^2 := by
  have Hmul : |a| ≤ err*x^2*d:=(div_le_iff₀ hd).mp H
  have Hu:=Hmul.trans (mul_le_mul_of_nonneg_left hdu (mul_nonneg herr (sq_nonneg x)))
  apply (div_le_div_of_nonneg_right Hu (mul_pos hB hW).le).trans_eq
  field_simp

end OAI.SKFluctuations.Cavity
