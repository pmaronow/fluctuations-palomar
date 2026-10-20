module

public import ComparisonSignedCavityActualConstantDeletedSiteOnCutsAlong
public import ComparisonSignedCavityActualConstantSourceCategoryEnvelope

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ} {as : List PositiveMass} {star U : ℕ}

def nativeActualPendingOtherSourceCategories : List NativeActualOtherSourceCategory :=
  nativeActualOtherSourceCategories.erase .deletedSite

theorem native_actual_other_source_categories_split_deleted :
    nativeActualOtherSourceCategories=nativeActualPendingOtherSourceCategories++[.deletedSite] := by
  rfl

def nativeActualConstantSourcePendingCategoryEnvelope
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ) : ℝ :=
  let children:=nativeActualConstantSourceChildren M as star U hs hU
  ((List.range depth).map (fun j=>
    (nativeActualPendingOtherSourceCategories.map (fun cat=>
      |nativeActualFourOtherCategorySum M U W
        (nativeActualMinimumFourCenteredForest M hs hU W j children) cat|)).sum/
      (Real.exp (-4*Temp)*cK*W))).sum

theorem actual_constant_source_remaining_envelope_deleted_site_paid
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W Temp cK : ℝ) (depth : ℕ)
    (hW : 0 < W) (hcK : 0 < cK) (C : ℕ→ℝ)
    (H : ∀j < depth,
      |nativeActualFourOtherCategorySum M U W
        (nativeActualMinimumFourCenteredForest M hs hU W j
          (nativeActualConstantSourceChildren M as star U hs hU)) .deletedSite| ≤
        C j*((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(W*M.xs^2)) :
    nativeActualConstantSourceRemainingCategoryEnvelope M hs hU W Temp cK depth ≤
      nativeActualConstantSourcePendingCategoryEnvelope M hs hU W Temp cK depth+
        (((List.range depth).map C).sum/(Real.exp (-4*Temp)*cK))*
          ((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*M.xs^2 := by
  let children:=nativeActualConstantSourceChildren M as star U hs hU
  let D:=Real.exp (-4*Temp)*cK*W
  have hD : 0 < D:=by dsimp only [D];positivity
  have HD0 : Real.exp (-4*Temp)*cK≠0:=mul_ne_zero (Real.exp_ne_zero _) hcK.ne'
  have HE : nativeActualConstantSourceRemainingCategoryEnvelope M hs hU W Temp cK depth=
      nativeActualConstantSourcePendingCategoryEnvelope M hs hU W Temp cK depth+
        ((List.range depth).map (fun j=>
          |nativeActualFourOtherCategorySum M U W
            (nativeActualMinimumFourCenteredForest M hs hU W j children) .deletedSite|/D)).sum:=by
    unfold nativeActualConstantSourceRemainingCategoryEnvelope nativeActualConstantSourcePendingCategoryEnvelope
    rw [←List.sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro j _
    rw [native_actual_other_source_categories_split_deleted,List.map_append,List.sum_append]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,add_div]
    rfl
  rw [HE]
  apply add_le_add (le_refl _)
  have Hr j (hj : j∈List.range depth) :
      |nativeActualFourOtherCategorySum M U W
        (nativeActualMinimumFourCenteredForest M hs hU W j children) .deletedSite|/D ≤
        (C j/(Real.exp (-4*Temp)*cK))*((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*M.xs^2:=by
    apply (div_le_div_of_nonneg_right (H j (List.mem_range.mp hj)) hD.le).trans_eq
    dsimp only [D]
    field_simp [HD0,hW.ne']
  apply (List.sum_le_sum Hr).trans_eq
  simp only [div_eq_mul_inv,List.sum_map_mul_right]

end OAI.SKFluctuations.Cavity
