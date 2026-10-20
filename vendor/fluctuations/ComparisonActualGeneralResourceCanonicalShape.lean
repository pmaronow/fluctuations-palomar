module

public import ComparisonActualHighWallSourceMoments
public import ComparisonSignedCavityActualResourceCanonicalShape

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem actual_general_resource_canonical_product_eq_live
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hstar : star < as.length)
    (bf hf : ℝ→ℝ≥0) (σ : T.Assignment) :
    ((nativeActualResourceCanonicalShape P hi hstar).canonicalPhysicalSource bf hf
      (fun _=>NativeSourceFactorForm.centered)).product σ=
      P.test.value (fun u v=>deletedOverlap n (joinSpin u) (joinSpin v))
        (nativePhysicalResourceCenter n bf hf as) σ := by
  rw [P.value_eq_product_get]
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  apply Finset.prod_congr rfl
  intro e he
  simp only [ActualNaturalBoundaryShape.canonicalPhysicalSource,
    ActualNaturalBoundaryShape.sourceLowMass,nativeActualResourceCanonicalShape,
    NativeSourceFactorForm.intercept,NativeSourceFactorForm.slope,
    fullBoundaryAffineFactor,one_mul,nativePhysicalResourceCenter]
  rw [T.splitIndex_symm]
  ring

theorem actual_general_resource_canonical_rest_product_eq_live
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hstar : star < as.length)
    (bf hf : ℝ→ℝ≥0)
    (σ : T.cavityLeft.Assignment) :
    ((nativeActualResourceCanonicalShape P hi hstar).canonicalPhysicalSource bf hf
      (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      nativeRestGeneratedTestValue T P.test
        (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
        (nativePhysicalResourceCenter n bf hf as) σ := by
  let τ:=T.cavityAssignment.symm (σ,assignmentOfSlots T.cavityRight (fun _=>false))
  have ht : (T.cavityAssignment τ).1=σ:=by
    dsimp only [τ]
    rw [Equiv.apply_symm_apply]
  have H:=actual_general_resource_canonical_product_eq_live P hi hstar bf hf τ
  rw [ActualNaturalBoundaryShape.product_eq_restProduct,ht] at H
  rw [←ht,native_rest_generated_value_eq_full]
  rw [ht,H]
  unfold NativeGeneratedTest.value nativeGeneratedEdgeProduct
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  simp [deletedOverlap,joinSpin]

end OAI.SKFluctuations.Cavity
