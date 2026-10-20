module

public import ComparisonSignedCavityGeneratedCompleteShape
public import ComparisonSignedCavityActualFrozenResourceMoments
public import ComparisonSignedCavityActualInitialPairMoments

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
attribute [local instance] Classical.propDecidable

def nativeActualResourceCanonicalShape
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hstar : star < as.length) :
    ActualNaturalBoundaryShape n P.factors.length T where
  α:=fun _=>0
  β:=fun _=>1
  i:=fun e=>(P.factors.get e).2.2
  j:=fun e=>(P.factors.get e).2.1
  distinct:=fun e=>(P.factor_endpoints_distinct hi hstar e).symm
  lowInGrid:=fun _e=>T.splitIndex_le_clockLength _ _

def nativeActualResourceInitialFactors
    {S : Type} {as : List PositiveMass} {T : ClockTree S as} {i star : ℕ}
    (P : NativeResourceMonomial i star T) : Finset (Fin P.factors.length) :=
  Finset.univ.filter (fun e=>(P.factors.get e).1=.initial)

theorem native_actual_resource_canonical_product_eq_live
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hstar : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (σ : T.Assignment) :
    ((nativeActualResourceCanonicalShape P hi hstar).canonicalMinimumSource M
      (fun _=>NativeSourceFactorForm.centered)).product σ=
      P.test.value (fun u v=>deletedOverlap n (joinSpin u) (joinSpin v))
        (nativePhysicalResourceCenter n M.bf M.hf as) σ := by
  rw [P.value_eq_product_get]
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  apply Finset.prod_congr rfl
  intro e he
  simp only [ActualNaturalBoundaryShape.canonicalMinimumSource,
    ActualNaturalBoundaryShape.sourceLowMass,nativeActualResourceCanonicalShape,
    NativeSourceFactorForm.intercept,NativeSourceFactorForm.slope,
    fullBoundaryAffineFactor,one_mul,nativePhysicalResourceCenter]
  rw [T.splitIndex_symm]
  ring

theorem native_actual_resource_canonical_rest_product_eq_live
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hstar : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (σ : T.cavityLeft.Assignment) :
    ((nativeActualResourceCanonicalShape P hi hstar).canonicalMinimumSource M
      (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      nativeRestGeneratedTestValue T P.test
        (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
        (nativePhysicalResourceCenter n M.bf M.hf as) σ := by
  let τ:=T.cavityAssignment.symm (σ,assignmentOfSlots T.cavityRight (fun _=>false))
  have ht : (T.cavityAssignment τ).1=σ:=by
    dsimp only [τ]
    rw [Equiv.apply_symm_apply]
  have H:=native_actual_resource_canonical_product_eq_live P hi hstar M τ
  rw [ActualNaturalBoundaryShape.product_eq_restProduct,ht] at H
  rw [←ht,native_rest_generated_value_eq_full]
  rw [ht,H]
  unfold NativeGeneratedTest.value nativeGeneratedEdgeProduct
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  simp [deletedOverlap,joinSpin]

theorem native_actual_resource_canonical_source_mass
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hstar : star < as.length)
    (Cmass x W : ℝ) (hmi : partitionPoint 0 as i≤Cmass*x)
    (hms : partitionPoint 0 as star≤Cmass*W) (e : Fin P.factors.length) :
    (nativeActualResourceCanonicalShape P hi hstar).sourceLowMass e≤
      Cmass*sourceFactorScale x W (nativeActualResourceInitialFactors P) e := by
  have HC:=P.cuts (P.factors.get e) (List.get_mem _ e)
  simp only [ActualNaturalBoundaryShape.sourceLowMass,nativeActualResourceCanonicalShape]
  rw [T.splitIndex_symm,HC]
  cases ht : (P.factors.get e).1 with
  | initial=>
    simp only [List.get_eq_getElem] at ht
    simpa [NativeResourceMark.cut,sourceFactorScale,nativeActualResourceInitialFactors,ht] using hmi
  | oldStar=>
    simp only [List.get_eq_getElem] at ht
    simpa [NativeResourceMark.cut,sourceFactorScale,nativeActualResourceInitialFactors,ht] using hms
  | markedStar k=>
    simp only [List.get_eq_getElem] at ht
    simpa [NativeResourceMark.cut,sourceFactorScale,nativeActualResourceInitialFactors,ht] using hms

theorem native_actual_resource_live_scale_eq_annotations
    {S : Type} {as : List PositiveMass} {T : ClockTree S as} {i star : ℕ}
    (P : NativeResourceMonomial i star T) (x W : ℝ) :
    sourceMonomialScale x W (nativeActualResourceInitialFactors P)=
      nativeResourceScale x W 1 P.tags := by
  rw [←source_factor_scale_product,←List.prod_ofFn]
  unfold nativeResourceScale NativeResourceMonomial.tags
  rw [List.map_map]
  conv_rhs=>rw [←List.ofFn_get P.factors,List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext e
  change sourceFactorScale x W (nativeActualResourceInitialFactors P) e=
    (P.factors.get e).1.savedScale x W 1
  cases ht : (P.factors.get e).1 <;>
    simp only [List.get_eq_getElem] at ht <;>
    simp [sourceFactorScale,nativeActualResourceInitialFactors,ht,NativeResourceMark.savedScale]

end OAI.SKFluctuations.Cavity
