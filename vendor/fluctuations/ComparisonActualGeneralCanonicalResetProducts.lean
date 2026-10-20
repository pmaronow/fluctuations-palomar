module

public import ComparisonActualHighWallSourceMoments
public import ComparisonSignedCavityGeneratedCompleteShape

@[expose] public section
noncomputable section
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem actual_general_generated_exterior_canonical_product (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hstar : star < as.length)
    (bf hf : ℝ→ℝ≥0) (σ : T.Assignment) :
    ((nativeGeneratedExteriorShape n P hP hi hstar).canonicalPhysicalSource bf hf
      (fun _=>NativeSourceFactorForm.centered)).product σ =
      nativeGeneratedEdgeProduct T (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) bf hf) (orderedOverlap (n+1))
          (partitionPoint 0 as j)) P.exterior σ := by
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  rw [←List.prod_ofFn]
  unfold nativeGeneratedEdgeProduct
  conv_rhs => rw [←List.ofFn_get P.exterior,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext e
  simp only [ActualNaturalBoundaryShape.canonicalPhysicalSource,
    ActualNaturalBoundaryShape.sourceLowMass,nativeGeneratedExteriorShape,
    NativeSourceFactorForm.intercept,NativeSourceFactorForm.slope,
    fullBoundaryAffineFactor,one_mul]
  rw [T.splitIndex_symm]
  dsimp only [Function.comp_apply]
  ring

theorem actual_general_generated_exterior_canonical_rest_product (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hstar : star < as.length)
    (bf hf : ℝ→ℝ≥0)
    (σ : T.cavityLeft.Assignment) :
    ((nativeGeneratedExteriorShape n P hP hi hstar).canonicalPhysicalSource bf hf
      (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      nativeRestGeneratedExteriorValue T P
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) bf hf) (orderedOverlap (n+1))
          (partitionPoint 0 as j)) σ := by
  let τ:=T.cavityAssignment.symm (σ,assignmentOfSlots T.cavityRight (fun _=>false))
  have ht : (T.cavityAssignment τ).1=σ := by
    dsimp only [τ]
    rw [Equiv.apply_symm_apply]
  have H:=actual_general_generated_exterior_canonical_product n P hP hi hstar bf hf τ
  rw [ActualNaturalBoundaryShape.product_eq_restProduct,ht] at H
  rw [←ht,native_rest_generated_exterior_value_eq_full]
  rw [ht,H]
  unfold nativeGeneratedEdgeProduct
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  simp [deletedOverlap,joinSpin]

theorem actual_general_generated_complete_canonical_product (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hstar : star < as.length)
    (bf hf : ℝ→ℝ≥0) (σ : T.Assignment) :
    ((nativeGeneratedCompleteShape n P hP hi hstar).canonicalPhysicalSource bf hf
      (fun _=>NativeSourceFactorForm.centered)).product σ =
      nativeGeneratedEdgeProduct T (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) bf hf) (orderedOverlap (n+1))
          (partitionPoint 0 as j)) P.edges σ := by
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  rw [←List.prod_ofFn]
  unfold nativeGeneratedEdgeProduct
  conv_rhs => rw [←List.ofFn_get P.edges,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext e
  simp only [ActualNaturalBoundaryShape.canonicalPhysicalSource,
    ActualNaturalBoundaryShape.sourceLowMass,nativeGeneratedCompleteShape,
    NativeSourceFactorForm.intercept,NativeSourceFactorForm.slope,
    fullBoundaryAffineFactor,one_mul]
  rw [T.splitIndex_symm]
  dsimp only [Function.comp_apply]
  ring

theorem actual_general_generated_complete_canonical_rest_product (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hstar : star < as.length)
    (bf hf : ℝ→ℝ≥0)
    (σ : T.cavityLeft.Assignment) :
    ((nativeGeneratedCompleteShape n P hP hi hstar).canonicalPhysicalSource bf hf
      (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      nativeRestGeneratedTestValue T P
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) bf hf) (orderedOverlap (n+1))
          (partitionPoint 0 as j)) σ := by
  let τ:=T.cavityAssignment.symm (σ,assignmentOfSlots T.cavityRight (fun _=>false))
  have ht : (T.cavityAssignment τ).1=σ := by
    dsimp only [τ]
    rw [Equiv.apply_symm_apply]
  have H:=actual_general_generated_complete_canonical_product n P hP hi hstar bf hf τ
  rw [ActualNaturalBoundaryShape.product_eq_restProduct,ht] at H
  rw [←ht,native_rest_generated_value_eq_full]
  rw [ht,H]
  unfold nativeGeneratedEdgeProduct
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  simp [deletedOverlap,joinSpin]

end OAI.SKFluctuations.Cavity
