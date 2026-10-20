module

public import ComparisonSignedCavityGeneratedCompleteShape
public import ComparisonSignedCavityActualResourceCanonicalShape
public import ComparisonSignedCavityActualResourceHighTaylorReadout
public import ComparisonSignedCavityActualResourceJointHighRestorationReadout
public import ComparisonSignedCavityActualCanonicalHighTaylorProfile
public import ComparisonSignedCavityActualAllDegreeHighTaylorProfile
public import ComparisonSignedCavityActualResourceHighTaylorProfile
public import ComparisonSignedCavityInheritedWorkingScaleCTwoHighProfileProducer
public import ComparisonSignedCavityInheritedWorkingScaleBondedLowGRestoration
public import ComparisonSignedCavityInheritedWorkingScaleBondedLowGPairRestoration
public import ComparisonSignedCavityInheritedWorkingScaleFourGLowRestoration
public import ComparisonSignedCavityInheritedWorkingScaleJointHighRestorationProfilePrice
public import ComparisonSignedCavityActualWorkingScaleResourceJointHighRestorationFromMinimum
public import ComparisonSignedCavityActualFreshResourceHighTaylorReadout
public import ComparisonSignedCavityActualCenteredResourceJointHighRestorationReadout
public import ComparisonSignedCavityActualWorkingScaleCenteredResourceJointHighRestorationFromMinimum
public import ComparisonSignedCavityInheritedGRestorationHighCanonical
public import ComparisonSignedCavityInheritedGRestorationLowCanonical
public import ComparisonSignedCavityInheritedGWordRestorationCanonical
public import ComparisonSignedCavityActualResourceLongitudinalRestorationReadout
public import ComparisonSignedCavityActualCenteredResourceLongitudinalRestoration
public import ComparisonSignedCavityActualCurrentGRestorationCanonical
public import ComparisonSignedCavityActualResourceGRestorationSource
public import ComparisonSignedCavityActualResourceGRestorationNorm
public import ComparisonSignedCavityInheritedGRestorationOriginalBudget
public import ComparisonSignedCavityInheritedUnbondedLowGRestoration
public import ComparisonSignedCavityInheritedUnbondedLowGPairRestoration
public import ComparisonSignedCavityGProjectedRestorationSource
public import ComparisonSignedCavityInheritedGProjectedRestorationProfile
public import ComparisonSignedCavityActualResourceGRestorationProfile
public import ComparisonSignedCavityActualBoundedResourceGRestorationProfile
public import ComparisonSignedCavityActualResourceGRestorationFromMinimum
public import ComparisonSignedCavityActualBoundedResourceHighTaylorProfile
public import ComparisonSignedCavityActualResourceHighTaylorFromMinimum
public import ComparisonSignedCavityActualCenteredResourceHighTaylorFromMinimum
public import ComparisonSignedCavityActualFreshResourceHighTaylorFromMinimum
public import ComparisonSignedCavityInheritedJointHighRestorationProfilePrice
public import ComparisonSignedCavityActualResourceJointHighRestorationFromMinimum
public import ComparisonSignedCavityActualCenteredResourceJointHighRestorationFromMinimum
public import ComparisonSignedCavityInheritedGLongitudinalOriginalBudget
public import ComparisonSignedCavityInheritedLongitudinalProfileProducer
public import ComparisonSignedCavityActualFreshResourceJointHighRestorationReadout
public import ComparisonSignedCavityInheritedAllDegreeLongitudinalProfile
public import ComparisonSignedCavityInheritedBoundedDegreeLongitudinalProfile
public import ComparisonSignedCavityActualResourceLongitudinalRestorationFromMinimum
public import ComparisonSignedCavityActualFreshResourceLongitudinalRestorationProfile
public import ComparisonSignedCavityActualFreshResourceJointHighRestorationFromMinimum
public import ComparisonSignedCavityActualWorkingScaleFreshResourceJointHighRestorationFromMinimum
public import SKProof.Port.ComparisonActualOriginalQFourReadoutPrimitives
public import SKProof.Port.ComparisonActualOriginalQRawResourcePairBudget
public import SKProof.Port.ComparisonActualOriginalQPhysicalSourceProfiles
public import SKProof.Port.ComparisonActualOriginalQPhysicalTaylorProfiles
public import SKProof.Port.ComparisonActualOriginalQOriginalTaylorProfiles
public import SKProof.Port.ComparisonActualOriginalQNaturalSourceCalibration
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQResourceCanonicalPorts

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_generated_complete_canonical_product_original_q (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hstar : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (σ : T.Assignment) :
    ((nativeGeneratedCompleteShape n P hP hi hstar).canonicalOriginalQSource M
      (fun _=>NativeSourceFactorForm.centered)).product σ =
      nativeGeneratedEdgeProduct T (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1))
          (partitionPoint 0 as j)) P.edges σ := by
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  rw [←List.prod_ofFn]
  unfold nativeGeneratedEdgeProduct
  conv_rhs => rw [←List.ofFn_get P.edges,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext e
  simp only [ActualNaturalBoundaryShape.canonicalOriginalQSource,
    ActualNaturalBoundaryShape.sourceLowMass,nativeGeneratedCompleteShape,
    NativeSourceFactorForm.intercept,NativeSourceFactorForm.slope,
    fullBoundaryAffineFactor,one_mul]
  rw [T.splitIndex_symm]
  dsimp only [Function.comp_apply]
  ring

theorem native_generated_complete_canonical_rest_product_original_q (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hstar : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (σ : T.cavityLeft.Assignment) :
    ((nativeGeneratedCompleteShape n P hP hi hstar).canonicalOriginalQSource M
      (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      nativeRestGeneratedTestValue T P
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1))
          (partitionPoint 0 as j)) σ := by
  let τ:=T.cavityAssignment.symm (σ,assignmentOfSlots T.cavityRight (fun _=>false))
  have ht : (T.cavityAssignment τ).1=σ := by
    dsimp only [τ]
    rw [Equiv.apply_symm_apply]
  have H:=native_generated_complete_canonical_product_original_q n P hP hi hstar M τ
  rw [ActualNaturalBoundaryShape.product_eq_restProduct,ht] at H
  rw [←ht,native_rest_generated_value_eq_full]
  rw [ht,H]
  unfold nativeGeneratedEdgeProduct
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  simp [deletedOverlap,joinSpin]

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
attribute [local instance] Classical.propDecidable

theorem native_actual_resource_canonical_product_eq_live_original_q
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hstar : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (σ : T.Assignment) :
    ((nativeActualResourceCanonicalShape P hi hstar).canonicalOriginalQSource M
      (fun _=>NativeSourceFactorForm.centered)).product σ=
      P.test.value (fun u v=>deletedOverlap n (joinSpin u) (joinSpin v))
        (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) σ := by
  rw [P.value_eq_product_get]
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  apply Finset.prod_congr rfl
  intro e he
  simp only [ActualNaturalBoundaryShape.canonicalOriginalQSource,
    ActualNaturalBoundaryShape.sourceLowMass,nativeActualResourceCanonicalShape,
    NativeSourceFactorForm.intercept,NativeSourceFactorForm.slope,
    fullBoundaryAffineFactor,one_mul,nativePhysicalResourceCenter]
  rw [T.splitIndex_symm]
  ring

theorem native_actual_resource_canonical_rest_product_eq_live_original_q
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hstar : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (σ : T.cavityLeft.Assignment) :
    ((nativeActualResourceCanonicalShape P hi hstar).canonicalOriginalQSource M
      (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      nativeRestGeneratedTestValue T P.test
        (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
        (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) σ := by
  let τ:=T.cavityAssignment.symm (σ,assignmentOfSlots T.cavityRight (fun _=>false))
  have ht : (T.cavityAssignment τ).1=σ:=by
    dsimp only [τ]
    rw [Equiv.apply_symm_apply]
  have H:=native_actual_resource_canonical_product_eq_live_original_q P hi hstar M τ
  rw [ActualNaturalBoundaryShape.product_eq_restProduct,ht] at H
  rw [←ht,native_rest_generated_value_eq_full]
  rw [ht,H]
  unfold NativeGeneratedTest.value nativeGeneratedEdgeProduct
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  simp [deletedOverlap,joinSpin]

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

def nativeActualResourceHigherHighPart_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (part : Fin 3) (a z : T.Slot) (l t : ℝ) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  nativeActualHigherHighPart part n q U b h K T
    (P.value (fullWeight n) (fullFeature n) 0 qfull
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0) a z l t

def nativeActualOriginalCenteredResourceHigherHighPart_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (part : Fin 3) (a z : T.Slot) (l t : ℝ) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T
    (nativeActualResourceRestValue P 0 qfull 0 C)
  nativeActualHigherHighPart part n q U b h K T (fun σ=>Pc (T.cavityAssignment σ).1) a z l t

theorem native_actual_original_centered_resource_HIGH_part_eq_two_resources_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    (part : Fin 3) (a z : T.Slot) (l t : ℝ) :
    nativeActualOriginalCenteredResourceHigherHighPart_original_q M U P part a z l t=
      nativeActualResourceHigherHighPart_original_q M U P part a z l t+
      nativeActualResourceHigherHighPart_original_q M U P.freeze part a z l t := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have H:=actual_higher_HIGH_part_original_centered_resource_eq_two_terms P ho part q U b h K C a z l t
  dsimp only at H
  rw [HQ] at H
  exact H

theorem actual_resource_HIGH_part_normalized_profile_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hdepth : seed.length+k ≤ degree)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hs : star < as.length)
    (part : Fin 3) (a z : T.Slot) (l t : ℝ)
    {A x W price : ℝ} (hA : 1 ≤ A) (hx : M.xs ≤ x) (hxW : x ≤ W) (hprice : 0 ≤ price)
    (Hpair : P.PairMomentBudget (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as
        (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)) 1 1)
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) 0 A x W 1)
    (Hlive :
      let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
      let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      let G:=nativeActualResourceCanonicalShape P.live hi hs
      |nativeActualHigherHighPart part n q U b h K T
        (G.canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).product a z l t| ≤
        nativeResourceScale x W 1 P.live.tags*price) :
    |(W⁻¹)^k*nativeActualResourceHigherHighPart_original_q M U P part a z l t| ≤
      |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*price := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let G:=nativeActualResourceCanonicalShape P.live hi hs
  let scalar:=nativeActualResourceOriginalScalar_original_q M U P
  let F:=(G.canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).product
  have HE : nativeActualResourceHigherHighPart_original_q M U P part a z l t=
      scalar*nativeActualHigherHighPart part n q U b h K T F a z l t := by
    unfold nativeActualResourceHigherHighPart_original_q
    dsimp only
    have HP : P.value (fullWeight n) (fullFeature n) 0
        (finitePhysicalCavitySquareVariance n U as b h 1 1)
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
        (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) 0=(fun σ=>scalar*F σ):=by
      funext σ
      dsimp only [F,G]
      rw [native_actual_resource_canonical_product_eq_live_original_q]
      rfl
    rw [HP,native_actual_higher_HIGH_part_const_mul_test]
  have HS:=hP.normalized_original_scalar_times_live_raw_scale_le hdepth
    (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavitySquareVariance n U as b h 1 1) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as)
    A x W 1 hA (M.hxs.trans_le hx) ((M.hxs.trans_le hx).trans_le hxW)
    zero_lt_one le_rfl hi hs Hpair
  change |(W⁻¹)^k*scalar| *nativeResourceScale x W 1 P.live.tags ≤ _ at HS
  dsimp only at Hlive
  rw [HE,mul_assoc,←mul_assoc,abs_mul]
  apply (mul_le_mul_of_nonneg_left Hlive (abs_nonneg ((W⁻¹)^k*scalar))).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right HS hprice

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

def nativeActualResourceJointHighRestoration_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (kind : NativeJointHighRestorationKind) (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (a z : T.Slot) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  nativeJointHighRestorationSource kind n q U b h K C T (nativeActualResourceRestValue P 0 qfull 0 C) a z

theorem actual_resource_joint_HIGH_normalized_price_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (kind : NativeJointHighRestorationKind) (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hdepth : seed.length+k ≤ degree)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hstar : star<as.length)
    (a z : T.Slot)
    {A x W price : ℝ} (hA : 1 ≤ A) (hx : M.xs ≤ x) (hxW : x ≤ W) (hprice : 0 ≤ price)
    (Hpair : P.PairMomentBudget (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as
        (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)) 1 1)
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) 0 A x W 1)
    (Hlive :
      let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
      let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
      let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      let G:=nativeActualResourceCanonicalShape P.live hi hstar
      |nativeJointHighRestorationSource kind n q U b h K C T
        (G.canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).restProduct a z| ≤
        nativeResourceScale x W 1 P.live.tags*price) :
    |(W⁻¹)^k*nativeActualResourceJointHighRestoration_original_q kind M U P a z| ≤
      |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*price := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let G:=nativeActualResourceCanonicalShape P.live hi hstar
  let scalar:=nativeActualResourceOriginalScalar_original_q M U P
  let F:=(G.canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).restProduct
  have HE : nativeActualResourceJointHighRestoration_original_q kind M U P a z=
      scalar*nativeJointHighRestorationSource kind n q U b h K C T F a z := by
    have HP : nativeActualResourceRestValue P 0
        (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 C=(fun σ=>scalar*F σ):=by
      funext σ
      dsimp only [F,G]
      rw [native_actual_resource_canonical_rest_product_eq_live_original_q]
      unfold nativeActualResourceRestValue
      congr 1
      apply congrArg List.prod
      apply List.map_congr_left
      intro e he
      simp [deletedOverlap,joinSpin,C]
    have hbm : Monotone b:=comp_partitionPoint_monotone
      (fun u hu v hv huv=>show (M.sweepBf u:ℝ) ≤ M.sweepBf v from M.inherited_bf_monotone hu hv huv) as ho
    have hhm : Monotone h:=comp_partitionPoint_monotone
      (fun u hu v hv huv=>show (M.sweepHf u:ℝ) ≤ M.sweepHf v from M.inherited_hf_monotone hu hv huv) as ho
    have HK:=native_continuum_mixed_clock_nonneg n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho
    have HKm:=native_continuum_mixed_clock_monotone n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho
    unfold nativeActualResourceJointHighRestoration_original_q
    dsimp only
    rw [HP]
    have H:=native_joint_HIGH_restoration_source_test_linear kind n q U b h K C T ho F F a z scalar 0
      (by intro j x;cases x <;> exact NNReal.coe_nonneg _)
      (by intro x;cases x <;> first | exact hbm | exact hhm)
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) HK hbm hhm HKm
    simpa only [zero_mul,add_zero] using H

  have HS:=hP.normalized_original_scalar_times_live_raw_scale_le hdepth
    (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavitySquareVariance n U as b h 1 1) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C
    A x W 1 hA (M.hxs.trans_le hx) ((M.hxs.trans_le hx).trans_le hxW)
    zero_lt_one le_rfl hi hstar Hpair
  change |(W⁻¹)^k*scalar| *nativeResourceScale x W 1 P.live.tags ≤ _ at HS
  dsimp only at Hlive
  rw [HE,mul_assoc,←mul_assoc,abs_mul]
  apply (mul_le_mul_of_nonneg_left Hlive (abs_nonneg ((W⁻¹)^k*scalar))).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right HS hprice

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000

theorem eventually_actual_minimum_inherited_canonical_HIGH_parts_profile_original_q
    (aDegree rBound dOrder : ℕ) (ha : 0 < aDegree) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W → W ≤ 1 →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
          |nativeActualHigherHighPart part n q U b h K T (G.canonicalOriginalQSource M forms).product a z l t| ≤
            C*W*sourceMonomialScale x W initial*
              (T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
                W*(T.forkCost R+edgeBudget 0 as R)) := by
  have hLowOrder : 2*(p/(p-2)) ≤ ((2*dOrder:ℕ):ℝ):=by
    push_cast
    linarith
  obtain ⟨C₀,hC₀,H₀⟩:=eventually_actual_minimum_inherited_canonical_centered_fixed_low_two_one_high_budget_original_q
    (D:=D) aDegree rBound ha Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨C₁,hC₁,H₁⟩:=eventually_actual_minimum_inherited_canonical_centered_fixed_low_one_two_high_budget_original_q
    (D:=D) aDegree rBound dOrder dOrder ha hd hd p hp hOrder hLowOrder Bclock Temp Cf Cmass Ccut
    hTemp hCf hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨C₂,hC₂,H₂⟩:=eventually_actual_minimum_inherited_canonical_centered_transient_HIGH_budget_original_q
    (D:=D) aDegree rBound ha Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=C₀+C₁+C₂+1
  have hC : 0 < C:=by dsimp only [C];linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [H₀,H₁,H₂] with n hn₀ hn₁ hn₂
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn₀ M hs0 hsxs hsource hxs L us hus hret hmesh,
    hn₁ M hs0 hsxs hsource hxs L us hus hret hmesh,hn₂ M hs0 hsxs hsource hxs L us hus hret hmesh]
    with jGrid hj₀ hj₁ hj₂
  dsimp only at hj₀ hj₁ hj₂ ⊢
  intro U T hU hT G forms initial x W hx hxW hW₁ hcut hmass a z l t hl ht part
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
  let F₁:=T.forkCost R+edgeBudget 0 as R
  let F₂:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))
  let Z:=sourceMonomialScale x W initial
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 ≤ W:=((M.hxs.trans_le hx).trans_le hxW).le
  have hZ : 0 ≤ Z:=by
    dsimp only [Z]
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hx)
      ((M.hxs.trans_le hx).trans_le hxW) initial e).le
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hF₁ : 0 ≤ F₁:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hF₂ : 0 ≤ F₂:=add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
    (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
  have HP₀:=actual_minimum_inherited_current_high_profile_le_original_original_q M Temp Cf hTemp hCf hsource hxs
    T ho U (show (0:ℝ)∈Icc 0 1 by norm_num) ht (e:=1) (by norm_num)
  simp only [Real.rpow_one] at HP₀
  have HP₁:=actual_minimum_inherited_current_high_profile_le_original_original_q M Temp Cf hTemp hCf hsource hxs
    T ho U (show (0:ℝ)∈Icc 0 1 by norm_num) ht (e:=4/p) (by positivity)
  have HP₂:=actual_minimum_inherited_current_high_profile_le_original_original_q M Temp Cf hTemp hCf hsource hxs
    T ho U hl ht (e:=1) (by norm_num)
  simp only [Real.rpow_one] at HP₂
  fin_cases part
  · change |nativeCenteredFixedLowHigh n q U b h K T (G.canonicalOriginalQSource M forms).product a z 2 1 t| ≤ _
    have H:=hj₀ U T t hU ht hT G forms initial x W hx hxW hcut hmass a z
    apply (H.trans (mul_le_mul_of_nonneg_left HP₀ (by positivity))).trans
    exact actual_high_one_error_price_le hC.le (by dsimp only [C];linarith) hW hZ hF₁ hF₂
  · change |nativeCenteredFixedLowHigh n q U b h K T (G.canonicalOriginalQSource M forms).product a z 1 2 t| ≤ _
    have H:=hj₁ U T t hU ht hT G forms initial x W hx hxW hcut hmass a z
    apply (H.trans (mul_le_mul_of_nonneg_left HP₁ (by positivity))).trans
    exact actual_high_two_error_price_le hC.le (by dsimp only [C];linarith) hW hZ hF₁ hF₂
  · change |nativeCenteredTransientHighThird n q U b h K T (G.canonicalOriginalQSource M forms).product a z l t| ≤ _
    have H:=hj₂ U T l t hU hl ht hT G forms initial x W hx hxW hcut hmass a z
    apply (H.trans (mul_le_mul_of_nonneg_left HP₂ (by positivity))).trans
    exact actual_high_transient_price_le hC.le hC₂.le (by dsimp only [C];linarith) hW hW₁ hZ hF₁ hF₂

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

theorem eventually_actual_minimum_inherited_all_degree_HIGH_parts_profile_original_q
    (aDegree rBound dOrder : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W → W ≤ 1 →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
          |nativeActualHigherHighPart part n q U b h K T (G.canonicalOriginalQSource M forms).product a z l t| ≤
            C*W*sourceMonomialScale x W initial*
              (T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
                W*(T.forkCost R+edgeBudget 0 as R)) := by
  by_cases ha0 : aDegree=0
  · subst aDegree
    obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_constant_HIGH_parts_profile_original_q
      (D:=D) rBound dOrder hd p hp hOrder Bclock Temp Cf Ccut hTemp hCf hCcut
      hm hdelta hroom hcl hcu hAz hC0 hCt
    refine ⟨C,hC,?_⟩
    filter_upwards [H] with n hn
    intro M hs0 hsxs hsource hxs L us hus hret hmesh
    filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro U T hU hT G forms initial x W hx hxW hW1 hcut hmass a z l t hl ht part
    have HP : (G.canonicalOriginalQSource M forms).product=(fun _=>1):=by
      funext σ
      unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
      apply Finset.prod_eq_one
      intro e he
      exact Fin.elim0 e
    have HI : initial=∅:=by
      ext e
      exact Fin.elim0 e
    rw [HP,HI]
    simpa only [sourceMonomialScale,Finset.card_empty,pow_zero,Nat.sub_zero,mul_one] using
      hj U T hU hT W (hx.trans hxW) hW1 hcut a z l t hl ht part
  · exact eventually_actual_minimum_inherited_canonical_HIGH_parts_profile_original_q
      (D:=D) aDegree rBound dOrder (Nat.pos_of_ne_zero ha0) hd p hp hOrder
      Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut hm hdelta hroom hcl hcu hAz hC0 hCt

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 23000000

theorem eventually_actual_minimum_inherited_resource_HIGH_parts_profile_original_q
    (aDegree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k degree : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → P.live.factors.length=aDegree → seed.length+k ≤ degree →
        ∀A x W : ℝ,1 ≤ A → M.xs ≤ x → x ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        P.PairMomentBudget (fullWeight n) (fullFeature n) 0
          (finitePhysicalCavitySquareVariance n U as
            (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)) 1 1)
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) 0 A x W 1 →
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
          |(W⁻¹)^k*nativeActualResourceHigherHighPart_original_q M U P part a z l t| ≤
            |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*
              (C*W*(T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
                W*(T.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_all_degree_HIGH_parts_profile_original_q
    (D:=D) aDegree rBound dOrder hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k degree seed T P hP hi hs hU hT hlen hdepth A x W hA hx hxW hW1 hmi hms hcut Hpair
    a z l t hl ht part
  let as:=finiteCutMasses us jGrid
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hstar : star < as.length:=hs.trans_le hU
  let G:=nativeActualResourceCanonicalShape P.live hi hstar
  let I:=nativeActualResourceInitialFactors P.live
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
  let cost:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
    W*(T.forkCost R+edgeBudget 0 as R)
  have hW : 0 ≤ W:=((M.hxs.trans_le hx).trans_le hxW).le
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hF₁:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hF₂:=add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) (4/p)))
    (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) (4/p)))
  have hprice : 0 ≤ C*W*cost:=by dsimp only [cost];positivity
  apply actual_resource_HIGH_part_normalized_profile_le_original_q M hP hdepth ho hi hstar part a z l t
    hA hx hxW hprice Hpair
  have Hgrid:=hj
  rw [←hlen] at Hgrid
  have HL:=Hgrid U T hU hT G (fun _=>.centered) I x W hx hxW hW1 hcut
    (native_actual_resource_canonical_source_mass P.live hi hstar Cmass x W hmi hms) a z l t hl ht part
  rw [native_actual_resource_live_scale_eq_annotations] at HL
  apply HL.trans_eq
  ring

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 30000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_working_scale_C_two_high_profile_budget_original_q
    (aDegree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (pexp : ℝ) (hpExp : 2 < pexp) (hOrder : pexp/(pexp-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length→T.leaves ≤ rBound→
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (xScale W : ℝ),M.xs ≤ xScale → xScale ≤ W →partitionPoint 0 as U ≤ Cmass*W→
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale xScale W initial e)→
        ∀a z : T.Slot,T.splitIndex a z < U→
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
          let f:=fun j=>(R j)^(4/pexp)
          |nativeCenteredLowGammaHighSecondRemainder n q U b h K S T
            (G.canonicalOriginalQSource M forms).restProduct a z| ≤
            pairForkVariation (rBound+2)*pairForkVariation (rBound+4)*
              (Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Cp^(aDegree+1)*
                (W*sourceMonomialScale xScale W initial))*(2*Temp)^((pexp-2)/pexp)*(2*Temp)^((pexp-2)/pexp)*
              pairForkVariation rBound*(T.forkCost f+edgeBudget 0 as f) := by
  obtain ⟨Cp,hCp,H⟩:=eventually_actual_minimum_inherited_canonical_working_scale_two_high_low_factor_original_q
    (D:=D) aDegree dOrder (rBound+2) hd pexp hpExp hOrder Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs1 L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs1 L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT G forms initial xScale W hxsScale hxW hcut hmass a z haz
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
  let f:=fun j=>(R j)^(4/pexp)
  let Phi:=pairForkVariation (rBound+2)*pairForkVariation (rBound+4)*
    (Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Cp^(aDegree+1)*
      (W*sourceMonomialScale xScale W initial))*(2*Temp)^((pexp-2)/pexp)*(2*Temp)^((pexp-2)/pexp)
  let P:=(G.canonicalOriginalQSource M forms).restProduct
  let F:=fun (p : MarkedPlacement T) (r : MarkedPlacement p.tree)=>
    nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark*
      (∫t in (0:ℝ)..1,(1-t)*cutFrozenLowHighJet n q U b h K r.tree
        (fun σ=>insertedRestTest P (restCenteredLowKernel n U b S) p r (r.tree.cavityAssignment σ).1) 0 0 2 t)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 ≤ W:=M.hxs.le.trans (hxsScale.trans hxW)
  have hscale : 0 ≤ sourceMonomialScale xScale W initial := by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsScale) (M.hxs.trans_le (hxsScale.trans hxW)) initial e).le
  have hPhi : 0 ≤ Phi := by
    dsimp only [Phi]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (pairForkVariation_nonneg _)) (by positivity))
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _)
  have hR j : 0 ≤ R j := by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf j : 0 ≤ f j:=Real.rpow_nonneg (hR j) _
  have HF (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
      |F p r| ≤ 2*Phi*(r.tree.forkCost f+edgeBudget 0 as f) := by
    let Pi:=nativeLowScalarPairing r.tree U K (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark
    have hProfile : 0 ≤ r.tree.forkCost f+edgeBudget 0 as f:=
      add_nonneg (r.tree.forkCost_nonneg hf) (edgeBudget_nonneg ho hf)
    by_cases hPi : Pi=0
    · change |Pi*_| ≤ _
      rw [hPi,zero_mul,abs_zero]
      exact mul_nonneg (mul_nonneg (by norm_num) hPhi) hProfile
    · have hold : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed z))=T.splitIndex a z := by
        rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2]
      have hsplit : r.tree.splitIndex (r.embed p.mark) r.mark=T.splitIndex a z := by
        have H:=native_low_scalar_pairing_split_weight r.tree ho U K
          (fun j=>if j=T.splitIndex a z then (1:ℝ) else 0)
          (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark hU (by rwa [hold])
        rw [hold,ite_eq_left rfl,one_mul] at H
        by_contra hne
        rw [ite_eq_right hne,zero_mul] at H
        exact hPi H.symm
      have hlow : r.tree.splitIndex (r.embed p.mark) r.mark < U:=by rwa [hsplit]
      have hcd : r.embed p.mark≠r.mark := by
        intro H
        rw [H,r.tree.splitIndex_self] at hlow
        omega
      have hleaf : r.tree.leaves ≤ rBound+2 := by
        have H1:=T.markedAttach_leaves 0 p hp
        have H2:=p.tree.markedAttach_leaves 0 r hr
        omega
      let Gr:=(G.nativeCMarkedLift p hp).nativeCMarkedLift r hr
      have hGr e : Gr.sourceLowMass e ≤ Cmass*sourceFactorScale xScale W initial e := by
        simpa only [Gr,ActualNaturalBoundaryShape.nativeCMarkedLift_sourceLowMass] using hmass e
      have hnew : partitionPoint 0 as (r.tree.splitIndex (r.embed p.mark) r.mark) ≤ Cmass*W :=
        (partitionPoint_mono as ho hlow.le).trans hcut
      have Htest:=G.nativeC_inserted_canonical_low_test_original_q M forms U b S p hp r hr hlow
      have Hjet t (ht : t∈Icc (0:ℝ) 1) :
          |cutFrozenLowHighJet n q U b h K r.tree
            (fun σ=>insertedRestTest P (restCenteredLowKernel n U b S) p r (r.tree.cavityAssignment σ).1) 0 0 2 t|≤
          Phi*(r.tree.forkCost f+edgeBudget 0 as f) := by
        have Hraw:=hgrid U r.tree t ht hleaf Gr forms initial xScale W hxsScale hxW hGr (r.embed p.mark) r.mark hcd hnew
        have Hprof:=actual_minimum_inherited_current_high_profile_le_original_original_q M Temp Cf hTemp hCf hsource hxs1
          r.tree ho U (l:=0) (t:=t) (by norm_num) ht (e:=4/pexp)
            (div_nonneg (by norm_num) (by linarith))
        have HH:=mul_le_mul_of_nonneg_left Hprof hPhi
        rw [Htest]
        exact Hraw.trans HH
      have HI:=weighted_unit_integral_abs_le (mul_nonneg hPhi hProfile) Hjet 1
      have HPi:=native_low_scalar_pairing_abs_le_two r.tree ho U K
        (r.embed (p.embed a)) (r.embed (p.embed z)) (r.embed p.mark) r.mark
      change |Pi*_|≤_
      rw [abs_mul]
      have HH:=mul_le_mul HPi (by simpa only [pow_one] using HI) (abs_nonneg _) (by norm_num : (0:ℝ)≤2)
      nlinarith only [HH]
  have HT:=T.signedPair_abs_le_pairAbsSum F
  have HM:=(HT.trans (T.pairAbsSum_mono HF))
  rw [T.pairAbsSum_const_mul (2*Phi)] at HM
  have HB:=T.pairAbsSum_forkBudget_le ho hT hf (d:=0) (by norm_num)
  simp only [add_zero] at HB
  have HX:=HM.trans (mul_le_mul_of_nonneg_left HB (mul_nonneg (by norm_num : (0:ℝ)≤2) hPhi))
  change |_/2|≤_
  rw [abs_div,show |(2:ℝ)|=2 by norm_num]
  dsimp only [nativeCenteredLowGammaHighSecondRemainder,F,P,Phi,R,f,q,b,h,K,S,Mclock] at HX ⊢
  nlinarith only [HX]

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 30000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_minimum_inherited_working_scale_low_factor_G_restoration_original_q
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (p : ℝ) (hp : 2<p) (hOrder : p/(p-2)≤(dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Ch Cl Cq : ℝ,0<Ch ∧ 0<Cl ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U≤as.length → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (xScale W : ℝ),M.xs ≤ xScale → xScale ≤ W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale xScale W initial e) →
        ∀u z a c e f : T.Slot,u≠z → T.splitIndex u z<U → e≠f →
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
          let CH:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Ch^(aDegree+1)*
            (W*sourceMonomialScale xScale W initial)
          let CL:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cl^(aDegree+1)*
            (W*sourceMonomialScale xScale W initial)
          let J:=fun σ=>(G.canonicalOriginalQSource M forms).product σ*
            (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.atSlot σ u))
              (joinSpin (T.atSlot σ z))-S (T.splitIndex u z)))
          |nativeActualLawRestorationRemainder n q U b h K T
            (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ)|≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.pairForkVariation rBound*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
                (R (T.splitIndex e f))^(2/p)*
                (T.forkCost (fun j=>(R j)^(2/p))+ClockTree.edgeBudget 0 as (fun j=>(R j)^(2/p)))+
                ClockTree.absJetVariation rBound 1*CL*R (T.splitIndex e f)*(Cq*(1+Ccut)*W)) := by
  obtain ⟨Ch,hCh,HH⟩:=eventually_actual_minimum_inherited_working_scale_low_factor_G_high_profile_original_q
    (D:=D) aDegree dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cl,Cq,hCl,hCq,HL⟩:=eventually_actual_minimum_inherited_working_scale_low_factor_G_low_profile_original_q
    (D:=D) aDegree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [HH,HL] with n hnH hnL
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnH M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnL M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgridH hgridL
  dsimp only at hgridH hgridL ⊢
  intro U T hU hT G forms initial xScale W hxsScale hxW hcut hmass u z a c e f huz huzcut hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
  let CH:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Ch^(aDegree+1)*
    (W*sourceMonomialScale xScale W initial)
  let CL:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cl^(aDegree+1)*
    (W*sourceMonomialScale xScale W initial)
  let J:=fun σ=>(G.canonicalOriginalQSource M forms).product σ*
    (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.atSlot σ u))
      (joinSpin (T.atSlot σ z))-S (T.splitIndex u z)))
  let κ:=|(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f|
  let BH:=κ*(ClockTree.pairForkVariation rBound*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
    (R (T.splitIndex e f))^(2/p)*
    (T.forkCost (fun j=>(R j)^(2/p))+ClockTree.edgeBudget 0 as (fun j=>(R j)^(2/p))))
  let BL:=κ*(ClockTree.absJetVariation rBound 1*CL*R (T.splitIndex e f)*(Cq*(1+Ccut)*W))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    (M.sweep_bf_monotone) (M.sweep_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ)≤M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ)≤M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf
      (M.sweep_bf_monotone) (M.sweep_hf_monotone)) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have hW : 0≤W:=M.hxs.le.trans (hxsScale.trans hxW)
  have hscale : 0 ≤ sourceMonomialScale xScale W initial:=by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun i _=>(source_factor_scale_pos (M.hxs.trans_le hxsScale) (M.hxs.trans_le (hxsScale.trans hxW)) initial i).le
  have hCH : 0≤CH:=by dsimp [CH];positivity
  have hCL : 0≤CL:=by dsimp [CL];positivity
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hH (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      |cutMixedJet n q U b h K T (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ) 0 0 0 t|≤BH:=by
    rw [native_cutMixedJet_zero_eq_profile n q U b h K T ho _ 0
      (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
      (fun i=>by cases i <;> first | exact hbm | exact hhm)
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm (by norm_num) ht]
    have H:=hgridH U T 0 t hU (by norm_num) ht hT G forms initial xScale W hxsScale hxW hcut hmass u z a c e f huz huzcut hef
    apply H.trans
    have HR:=Real.rpow_le_rpow (nativeWholeLawErrorRadius_nonneg n as _ _ (T.splitIndex e f))
      (actual_minimum_inherited_current_high_error_radius_le_original_original_q (l:=0) (t:=t) M Temp Cf hTemp hCf hsource hxs ho U
        (by norm_num) ht (T.splitIndex e f) (T.splitIndex_le_clockLength e f)) (show 0≤2/p by positivity)
    have HC:=actual_minimum_inherited_current_high_profile_le_original_original_q (l:=0) (t:=t) M Temp Cf hTemp hCf hsource hxs T ho U
      (by norm_num) ht (show 0≤2/p by positivity)
    have Hprof:=native_whole_law_profile_cost_nonneg n ho
      (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) T (2/p)
    have Hpv:=ClockTree.pairForkVariation_nonneg rBound
    have HRj:=hR (T.splitIndex e f)
    dsimp only [BH,κ]
    gcongr
  have hL (l : ℝ) (hl : l∈Icc (0:ℝ) 1) :
      |cutLowJet n q U b h K T (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ) 0 1 l 1|≤BL:=by
    rw [cutLowJet_eq_profileJets n q U b h K T ho _ 0
      (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
      (fun i=>by cases i <;> first | exact hbm | exact hhm)
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm 1 hl (by norm_num)]
    simp only [List.replicate_one]
    have H:=hgridL U T l 1 hU hl (by norm_num) hT G forms initial xScale W hxsScale hxW hcut hmass u z a c e f huz huzcut hef
    apply H.trans
    have HR:=actual_minimum_inherited_current_high_error_radius_le_original_original_q (l:=l) (t:=1) M Temp Cf hTemp hCf hsource hxs ho U
      hl (by norm_num) (T.splitIndex e f) (T.splitIndex_le_clockLength e f)
    have Hav:=ClockTree.absJetVariation_nonneg rBound 1
    have HRj:=hR (T.splitIndex e f)
    dsimp only [BL,κ]
    gcongr
  have H:=native_actual_law_restoration_abs_le n q U b h K T
    (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ) BH BL hH hL
  convert H using 1
  dsimp only [BH,BL,κ,CH,CL,R,J,Mclock,K,b,h,S,q,as]
  ring

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 20000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_minimum_inherited_working_scale_low_factor_G_pair_restoration_original_q
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (p : ℝ) (hp : 2<p) (hOrder : p/(p-2)≤(dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Ch Cl Cq : ℝ,0<Ch ∧ 0<Cl ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U≤as.length → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (xScale W : ℝ),M.xs ≤ xScale → xScale ≤ W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale xScale W initial e) →
        ∀u z a c : T.Slot,u≠z → T.splitIndex u z<U →
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
          let f2:=fun j=>((R j)^(2/p))^2
          let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Ch^(aDegree+1)*
            (W*sourceMonomialScale xScale W initial)
          let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Cl^(aDegree+1)*
            (W*sourceMonomialScale xScale W initial)
          let AH:=pairForkVariation (rBound+2)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*((rBound:ℝ)+3)
          let AL:=absJetVariation (rBound+2) 1*CL*(Cq*(1+Ccut)*W)
          let J:=fun σ=>(G.canonicalOriginalQSource M forms).restProduct σ*
            (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot u),false))
              (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot z),false))-S (T.splitIndex u z)))
          |nativeOriginalHighPairRestoration n q U b h K S T J a c|≤
            AH*pairForkVariation rBound*(T.forkCost f2+edgeBudget 0 as f2)+
              AL*pairForkVariation rBound*(T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=eventually_actual_minimum_inherited_working_scale_low_factor_G_restoration_original_q
    (D:=D) aDegree dOrder (rBound+2) hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT G forms initial xScale W hxsScale hxW hcut hmass u z a c huz huzcut
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
  let f2:=fun j=>((R j)^(2/p))^2
  let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Ch^(aDegree+1)*
    (W*sourceMonomialScale xScale W initial)
  let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Cl^(aDegree+1)*
    (W*sourceMonomialScale xScale W initial)
  let AH0:=pairForkVariation (rBound+2)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)
  let AH:=AH0*((rBound:ℝ)+3)
  let AL:=absJetVariation (rBound+2) 1*CL*(Cq*(1+Ccut)*W)
  let J:=fun σ=>(G.canonicalOriginalQSource M forms).restProduct σ*
    (b (T.splitIndex u z)*(deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot u),false))
      (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot z),false))-S (T.splitIndex u z)))
  let F:=fun (p : MarkedPlacement T) (r : MarkedPlacement p.tree)=>
    nativeActualLawRestorationRemainder n q U b h K r.tree
      (fun σ=>J (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))*
        nativeOriginalHighGAtom r.tree U K b S (r.embed (p.embed a)) (r.embed (p.embed c))
          (r.embed p.mark) r.mark σ)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hscale : 0 ≤ sourceMonomialScale xScale W initial:=by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsScale) (M.hxs.trans_le (hxsScale.trans hxW)) initial e).le
  have hW : 0≤W:=M.hxs.le.trans (hxsScale.trans hxW)
  have hAH0 : 0≤AH0:=by
    dsimp only [AH0,CH]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (by positivity))
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _)
  have hAH : 0≤AH:=mul_nonneg hAH0 (by positivity)
  have hCL : 0≤CL:=by dsimp [CL];positivity
  have hAL : 0≤AL:=mul_nonneg (mul_nonneg (absJetVariation_nonneg _ _) hCL) (by positivity)
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf2 j : 0≤f2 j:=sq_nonneg _
  have HF (p0 : MarkedPlacement T) (hp0 : p0∈T.markedAttach 0)
      (r : MarkedPlacement p0.tree) (hr : r∈p0.tree.markedAttach 0) :
      |F p0 r|≤AH*(r.tree.forkCost f2+edgeBudget 0 as f2)+AL*(r.tree.forkCost R+edgeBudget 0 as R) := by
    by_cases hdiag : r.embed p0.mark=r.mark
    · have Hzero:=actual_minimum_original_G_diagonal_restoration_zero_original_q M r.tree ho U
        (fun σ=>J (p0.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1)))
        (r.embed (p0.embed a)) (r.embed (p0.embed c)) r.mark
      dsimp only [F]
      rw [hdiag,Hzero,abs_zero]
      exact add_nonneg (mul_nonneg hAH (add_nonneg (r.tree.forkCost_nonneg hf2) (edgeBudget_nonneg ho hf2)))
        (mul_nonneg hAL (add_nonneg (r.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
    · let Gr:=(G.nativeCMarkedLift p0 hp0).nativeCMarkedLift r hr
      have hGr e : Gr.sourceLowMass e≤Cmass*sourceFactorScale xScale W initial e:=by
        simpa only [Gr,ActualNaturalBoundaryShape.nativeCMarkedLift_sourceLowMass] using hmass e
      have hleaf : r.tree.leaves≤rBound+2:=by
        have H1:=T.markedAttach_leaves 0 p0 hp0
        have H2:=p0.tree.markedAttach_leaves 0 r hr
        omega
      have hlow : r.tree.splitIndex (r.embed (p0.embed u)) (r.embed (p0.embed z))<U:=by
        rwa [(p0.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p0 hp0).2]
      have hdistinct : r.embed (p0.embed u)≠r.embed (p0.embed z):=by
        intro HH
        exact huz ((T.markedAttach_embed_preserves 0 p0 hp0).1 ((p0.tree.markedAttach_embed_preserves 0 r hr).1 HH))
      have Hrest:=hgrid U r.tree hU hleaf Gr forms initial xScale W hxsScale hxW hcut hGr
        (r.embed (p0.embed u)) (r.embed (p0.embed z))
        (r.embed (p0.embed a)) (r.embed (p0.embed c)) (r.embed p0.mark) r.mark hdistinct hlow hdiag
      have Htest:=G.native_double_marked_low_pair_test_original_q M forms b S u z p0 hp0 r hr
      change |nativeActualLawRestorationRemainder n q U b h K r.tree _|≤_
      have Hleft:=congrArg (fun J0 : r.tree.Assignment→ℝ=>
        nativeActualLawRestorationRemainder n q U b h K r.tree
          (fun σ=>J0 σ*nativeOriginalHighGAtom r.tree U K b S (r.embed (p0.embed a))
            (r.embed (p0.embed c)) (r.embed p0.mark) r.mark σ)) Htest
      rw [Hleft]
      apply Hrest.trans
      let ff:=fun j=>(R j)^(2/p)
      have hff j : 0≤ff j:=Real.rpow_nonneg (hR j) _
      have HY:=native_distinct_pair_profile_product_le r.tree ho ff (r.embed p0.mark) r.mark hdiag
      have HS:=r.tree.split_le_forkCost hR (r.embed p0.mark) r.mark hdiag
      have HE:=edgeBudget_nonneg ho hR
      have HP:=add_nonneg (r.tree.forkCost_nonneg hf2) (edgeBudget_nonneg ho hf2)
      have hleafr : (r.tree.leaves:ℝ)+1≤(rBound:ℝ)+3:=by exact_mod_cast (by omega : r.tree.leaves+1≤rBound+3)
      have Hκ:=native_full_scalar_connected_four_abs_le_two r.tree ho U K
        (r.embed (p0.embed a)) (r.embed (p0.embed c)) (r.embed p0.mark) r.mark
      have Hκ' : |(1/2:ℝ)*fullScalarCutConnected4 r.tree U K
          (r.embed (p0.embed a)) (r.embed (p0.embed c)) (r.embed p0.mark) r.mark|≤1:=by
        rw [abs_mul]
        norm_num only [abs_of_nonneg (show (0:ℝ)≤1/2 by norm_num)]
        linarith
      have Hprod:=mul_le_mul_of_nonneg_left HY hAH0
      have Hleaf:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hleafr hAH0) HP
      have Hlow:=mul_le_mul_of_nonneg_left (HS.trans (le_add_of_nonneg_right HE)) hAL
      have Hnonneg : 0≤AH0*(ff (r.tree.splitIndex (r.embed p0.mark) r.mark)*
          (r.tree.forkCost ff+edgeBudget 0 as ff))+AL*R (r.tree.splitIndex (r.embed p0.mark) r.mark):=by
        exact add_nonneg (mul_nonneg hAH0 (mul_nonneg (hff _)
          (add_nonneg (r.tree.forkCost_nonneg hff) (edgeBudget_nonneg ho hff)))) (mul_nonneg hAL (hR _))
      have Hscalar:=mul_le_of_le_one_left Hnonneg Hκ'
      dsimp only [Gr,CH,CL,AH0,AH,AL,R,ff,f2,Mclock] at Hprod Hleaf Hlow Hscalar ⊢
      nlinarith only [Hprod,Hleaf,Hlow,Hscalar]
  have Hsum:=(T.signedPair_abs_le_pairAbsSum F).trans (T.pairAbsSum_mono HF)
  rw [T.pairAbsSum_add,T.pairAbsSum_const_mul AH,T.pairAbsSum_const_mul AL] at Hsum
  have HH:=T.pairAbsSum_forkBudget_le ho hT hf2 (d:=0) (by norm_num)
  have HL:=T.pairAbsSum_forkBudget_le ho hT hR (d:=0) (by norm_num)
  simp only [add_zero] at HH HL
  have HB:=add_le_add (mul_le_mul_of_nonneg_left HH hAH) (mul_le_mul_of_nonneg_left HL hAL)
  apply Hsum.trans
  convert HB using 1
  dsimp only [F,J,AH,AH0,AL,CH,CL,R,f2,q,b,h,K,S,Mclock,as,nativeOriginalHighPairRestoration]
  ring

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 22000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open Hierarchy.ClockTree
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_minimum_inherited_canonical_working_scale_four_G_low_restoration_original_q
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (p : ℝ) (hp : 2<p) (hOrder : p/(p-2)≤(dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Ch Cl Cq : ℝ,0<Ch ∧ 0<Cl ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U≤as.length → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (xScale W : ℝ),M.xs ≤ xScale → xScale ≤ W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale xScale W initial e) →
        ∀a z : T.Slot,
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
          let f2:=fun j=>((R j)^(2/p))^2
          let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Ch^(aDegree+1)*
            (W*sourceMonomialScale xScale W initial)
          let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Cl^(aDegree+1)*
            (W*sourceMonomialScale xScale W initial)
          let AH:=pairForkVariation (rBound+4)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*((rBound:ℝ)+5)*pairForkVariation (rBound+2)
          let AL:=absJetVariation (rBound+4) 1*CL*(Cq*(1+Ccut)*W)*pairForkVariation (rBound+2)
          |nativeOriginalGKernelLowRestoration n q U b h K S T
            (G.canonicalOriginalQSource M forms).restProduct a z (restCenteredLowKernel n U b S)|≤
            2*AH*pairForkVariation rBound*(T.forkCost f2+edgeBudget 0 as f2)+
              2*AL*pairForkVariation rBound*(T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=eventually_actual_minimum_inherited_working_scale_low_factor_G_pair_restoration_original_q
    (D:=D) aDegree dOrder (rBound+2) hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT G forms initial xScale W hxsScale hxW hcut hmass a z
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
  let f2:=fun j=>((R j)^(2/p))^2
  let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Ch^(aDegree+1)*
    (W*sourceMonomialScale xScale W initial)
  let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Cl^(aDegree+1)*
    (W*sourceMonomialScale xScale W initial)
  let AH:=pairForkVariation (rBound+4)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
    ((rBound:ℝ)+5)*pairForkVariation (rBound+2)
  let AL:=absJetVariation (rBound+4) 1*CL*(Cq*(1+Ccut)*W)*pairForkVariation (rBound+2)
  let P:=(G.canonicalOriginalQSource M forms).restProduct
  let A:=restCenteredLowKernel n U b S
  let F:=fun (p0 : MarkedPlacement T) (r : MarkedPlacement p0.tree)=>
    fullScalarCutGamma r.tree U K (r.embed (p0.embed z)) r.mark*
      nativeOriginalHighPairRestoration n q U b h K S r.tree (insertedRestTest P A p0 r)
        (r.embed (p0.embed a)) (r.embed p0.mark)+
    fullScalarCutGamma r.tree U K (r.embed (p0.embed z)) (r.embed p0.mark)*
      nativeOriginalHighPairRestoration n q U b h K S r.tree (insertedRestTest P A p0 r)
        (r.embed (p0.embed a)) r.mark+
    fullScalarCutGamma r.tree U K (r.embed (p0.embed a)) (r.embed p0.mark)*
      nativeOriginalHighPairRestoration n q U b h K S r.tree (insertedRestTest P A p0 r)
        (r.embed (p0.embed z)) r.mark+
    fullScalarCutGamma r.tree U K (r.embed (p0.embed a)) r.mark*
      nativeOriginalHighPairRestoration n q U b h K S r.tree (insertedRestTest P A p0 r)
        (r.embed (p0.embed z)) (r.embed p0.mark)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0≤W:=M.hxs.le.trans (hxsScale.trans hxW)
  have hscale : 0 ≤ sourceMonomialScale xScale W initial:=by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsScale) (M.hxs.trans_le (hxsScale.trans hxW)) initial e).le
  have hCH : 0≤CH:=by dsimp [CH];positivity
  have hCL : 0≤CL:=by dsimp [CL];positivity
  have hAH : 0≤AH:=by
    dsimp only [AH]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (pairForkVariation_nonneg _) hCH) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by positivity) _)) (by positivity)) (pairForkVariation_nonneg _)
  have hAL : 0≤AL:=mul_nonneg (mul_nonneg (mul_nonneg (absJetVariation_nonneg _ _) hCL)
    (by positivity)) (pairForkVariation_nonneg _)
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf2 j : 0≤f2 j:=sq_nonneg _
  have HF (p0 : MarkedPlacement T) (hp0 : p0∈T.markedAttach 0)
      (r : MarkedPlacement p0.tree) (hr : r∈p0.tree.markedAttach 0) :
      |F p0 r|≤4*AH*(r.tree.forkCost f2+edgeBudget 0 as f2)+4*AL*(r.tree.forkCost R+edgeBudget 0 as R) := by
    let B:=AH*(r.tree.forkCost f2+edgeBudget 0 as f2)+AL*(r.tree.forkCost R+edgeBudget 0 as R)
    have hB : 0≤B:=add_nonneg (mul_nonneg hAH (add_nonneg (r.tree.forkCost_nonneg hf2) (edgeBudget_nonneg ho hf2)))
      (mul_nonneg hAL (add_nonneg (r.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
    have Hpair (x y : r.tree.Slot) :
        |nativeOriginalHighPairRestoration n q U b h K S r.tree (insertedRestTest P A p0 r) x y|≤B:=by
      by_cases hlow : r.tree.splitIndex (r.embed p0.mark) r.mark<U
      · have hcd : r.embed p0.mark≠r.mark:=by
          intro HH
          rw [HH,r.tree.splitIndex_self] at hlow
          omega
        let Gr:=(G.nativeCMarkedLift p0 hp0).nativeCMarkedLift r hr
        have hGr e : Gr.sourceLowMass e≤Cmass*sourceFactorScale xScale W initial e:=by
          simpa only [Gr,ActualNaturalBoundaryShape.nativeCMarkedLift_sourceLowMass] using hmass e
        have hleaf : r.tree.leaves≤rBound+2:=by
          have H1:=T.markedAttach_leaves 0 p0 hp0
          have H2:=p0.tree.markedAttach_leaves 0 r hr
          omega
        rw [show insertedRestTest P A p0 r=_ from G.native_inserted_canonical_low_rest_test_original_q M forms U b S p0 hp0 r hr hlow]
        have Hinner:=hgrid U r.tree hU hleaf Gr forms initial xScale W hxsScale hxW hcut hGr
          (r.embed p0.mark) r.mark x y hcd hlow
        convert Hinner using 1
        dsimp only [B,AH,AL,CH,CL,R,f2,Mclock,Gr]
        push_cast
        ring
      · have Hzero : ∀σ,insertedRestTest P A p0 r σ=0:=by
          intro σ
          simp only [insertedRestTest,A,restCenteredLowKernel,hlow,ite_false,mul_zero]
        rw [actual_minimum_original_high_pair_restoration_zero_payload_original_q M r.tree ho U _ Hzero x y,abs_zero]
        exact hB
    have Hterm (x y x' y' : r.tree.Slot) :
        |fullScalarCutGamma r.tree U K x y*
          nativeOriginalHighPairRestoration n q U b h K S r.tree (insertedRestTest P A p0 r) x' y'|≤B:=by
      rw [abs_mul]
      have Hgam:=native_full_scalar_cut_moment_abs_le_one r.tree ho U K [x,y]
      exact (mul_le_mul Hgam (Hpair x' y') (abs_nonneg _) zero_le_one).trans_eq (one_mul B)
    have H1:=Hterm (r.embed (p0.embed z)) r.mark (r.embed (p0.embed a)) (r.embed p0.mark)
    have H2:=Hterm (r.embed (p0.embed z)) (r.embed p0.mark) (r.embed (p0.embed a)) r.mark
    have H3:=Hterm (r.embed (p0.embed a)) (r.embed p0.mark) (r.embed (p0.embed z)) r.mark
    have H4:=Hterm (r.embed (p0.embed a)) r.mark (r.embed (p0.embed z)) (r.embed p0.mark)
    have Hsum : |F p0 r|≤4*B:=by
      dsimp only [F]
      exact ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
        (add_le_add ((abs_add_le _ _).trans (add_le_add H1 H2)) H3)) H4)).trans_eq (by ring)
    simpa only [B,mul_add,mul_assoc] using Hsum
  have Hsum:=(T.signedPair_abs_le_pairAbsSum F).trans (T.pairAbsSum_mono HF)
  rw [T.pairAbsSum_add,T.pairAbsSum_const_mul (4*AH),T.pairAbsSum_const_mul (4*AL)] at Hsum
  have HH:=T.pairAbsSum_forkBudget_le ho hT hf2 (d:=0) (by norm_num)
  have HL:=T.pairAbsSum_forkBudget_le ho hT hR (d:=0) (by norm_num)
  simp only [add_zero] at HH HL
  have HX:=Hsum.trans (add_le_add (mul_le_mul_of_nonneg_left HH (mul_nonneg (by norm_num) hAH))
    (mul_le_mul_of_nonneg_left HL (mul_nonneg (by norm_num) hAL)))
  change |_/2|≤_
  rw [abs_div,show |(2:ℝ)|=2 by norm_num]
  change |((T.markedAttach 0).map (fun p0=>p0.coeff*
    ((p0.tree.markedAttach 0).map (fun r=>r.coeff*F p0 r)).sum)).sum|/2≤_
  dsimp only [AH,AL,CH,CL,R,f2,q,b,h,K,S,Mclock,as] at HX ⊢
  nlinarith only [HX]

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_minimum_inherited_canonical_working_scale_joint_HIGH_restoration_price_original_q
    (kind : NativeJointHighRestorationKind) (aDegree dOrder rBound : ℕ)
    (hd : 0 < dOrder) (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (xScale W : ℝ),M.xs ≤ xScale → xScale ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale xScale W initial e) →
        ∀a z : T.Slot,T.splitIndex a z<U →
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
          |nativeJointHighRestorationSource kind n q U b h K S T
            (G.canonicalOriginalQSource M forms).restProduct a z| ≤
            C*W*sourceMonomialScale xScale W initial*
              (T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
                W*(T.forkCost R+edgeBudget 0 as R)) := by
  cases kind with
  | lowTwoHigh=>
    let Cgeom:=max Cmass Ccut
    have hCgeom : 0 ≤ Cgeom:=hCmass.trans (le_max_left _ _)
    obtain ⟨Cp,hCp,H⟩:=eventually_actual_minimum_inherited_canonical_working_scale_C_two_high_profile_budget_original_q
      (D:=D) aDegree dOrder rBound hd p hp hOrder Bclock Temp Cf Cgeom hTemp hCf hCgeom
      hm hdelta hroom hcl hcu hAz hC0 hCt
    let base:=pairForkVariation (rBound+2)*pairForkVariation (rBound+4)*
      (Real.exp (wholeLawRowComparisonConstant (rBound+2)*(4*Cf+2*Temp))*Cp^(aDegree+1))*
      (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*pairForkVariation rBound
    have hbase : 0 ≤ base:=by
      have HV0:=pairForkVariation_nonneg (rBound+2)
      have HV1:=pairForkVariation_nonneg (rBound+4)
      have HV2:=pairForkVariation_nonneg rBound
      have HP:=Real.rpow_nonneg (show 0 ≤ 2*Temp by positivity) ((p-2)/p)
      dsimp only [base]
      positivity
    refine ⟨base+1,by positivity,?_⟩
    filter_upwards [H] with n hn
    intro M hs0 hsxs hsource hxs L us hus hret hmesh
    filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro U T hU hT G forms initial xScale W hxsScale hxW hcut hmass a z haz
    have hW : 0 ≤ W:=M.hxs.le.trans (hxsScale.trans hxW)
    have hmass' e : G.sourceLowMass e ≤ Cgeom*sourceFactorScale xScale W initial e:=
      (hmass e).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (source_factor_scale_pos (M.hxs.trans_le hxsScale) (M.hxs.trans_le (hxsScale.trans hxW)) initial e).le)
    have hcut' : partitionPoint 0 (finiteCutMasses us jGrid) U ≤ Cgeom*W:=
      hcut.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hW)
    have Hraw:=hj U T hU hT G forms initial xScale W hxsScale hxW hcut' hmass' a z haz
    let as:=finiteCutMasses us jGrid
    let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
    let Z:=sourceMonomialScale xScale W initial
    let A:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))
    let B:=T.forkCost R+edgeBudget 0 as R
    have ho:=finiteCutMasses_ordered us hus jGrid
    have hR j : 0 ≤ R j:=by
      dsimp only [R,nativeOriginalHighErrorEnvelope]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) (by
          dsimp only [nativeOriginalCutLowErrorRadius]
          positivity)
    have hA : 0 ≤ A:=add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
      (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
    have hB : 0 ≤ B:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
    have hZ : 0 ≤ Z:=by
      rw [show Z=∏e,sourceFactorScale xScale W initial e from (source_factor_scale_product _ _ _).symm]
      exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsScale) (M.hxs.trans_le (hxsScale.trans hxW)) initial e).le
    have Hmajor:=mul_le_mul_of_nonneg_right (show base ≤ base+1 by linarith)
      (show 0 ≤ W*Z*A by positivity)
    have Hprice : base*W*Z*A ≤ (base+1)*W*Z*(A+W*B):=by
      have Hplus : 0 ≤ (base+1)*W*Z*(W*B):=by positivity
      nlinarith only [Hmajor,Hplus]
    apply Hraw.trans
    convert Hprice using 1
    dsimp only [base,R,Z,A,B,as,nativeJointHighRestorationSource]
    ring
  | fourGLow=>
    obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=eventually_actual_minimum_inherited_canonical_working_scale_four_G_low_restoration_original_q
      (D:=D) aDegree dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
      hm hdelta hroom hcl hcu hAz hC0 hCt
    let bh:=2*pairForkVariation (rBound+4)*
      (Real.exp (wholeLawRowComparisonConstant (rBound+4)*(4*Cf+2*Temp))*Ch^(aDegree+1))*
      (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*((rBound:ℝ)+5)*pairForkVariation (rBound+2)*pairForkVariation rBound
    let bl:=2*absJetVariation (rBound+4) 1*
      (Real.exp (wholeLawRowComparisonConstant (rBound+4)*(4*Cf+2*Temp))*Cl^(aDegree+1))*
      (Cq*(1+Ccut))*pairForkVariation (rBound+2)*pairForkVariation rBound
    have hbh : 0 ≤ bh:=by
      have HV0:=pairForkVariation_nonneg (rBound+4)
      have HV1:=pairForkVariation_nonneg (rBound+2)
      have HV2:=pairForkVariation_nonneg rBound
      have HP:=Real.rpow_nonneg (show 0 ≤ 2*Temp by positivity) ((p-2)/p)
      dsimp only [bh]
      positivity
    have hbl : 0 ≤ bl:=by
      have HV0:=absJetVariation_nonneg (rBound+4) 1
      have HV1:=pairForkVariation_nonneg (rBound+2)
      have HV2:=pairForkVariation_nonneg rBound
      dsimp only [bl]
      positivity
    refine ⟨bh+bl+1,by positivity,?_⟩
    filter_upwards [H] with n hn
    intro M hs0 hsxs hsource hxs L us hus hret hmesh
    filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro U T hU hT G forms initial xScale W hxsScale hxW hcut hmass a z _haz
    have Hraw:=hj U T hU hT G forms initial xScale W hxsScale hxW hcut hmass a z
    let as:=finiteCutMasses us jGrid
    let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
    let Z:=sourceMonomialScale xScale W initial
    let A:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))
    let B:=T.forkCost R+edgeBudget 0 as R
    have ho:=finiteCutMasses_ordered us hus jGrid
    have hW : 0 ≤ W:=M.hxs.le.trans (hxsScale.trans hxW)
    have hR j : 0 ≤ R j:=by
      dsimp only [R,nativeOriginalHighErrorEnvelope]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) (by
          dsimp only [nativeOriginalCutLowErrorRadius]
          positivity)
    have Hpow : (fun j=>((R j)^(2/p))^2)=(fun j=>(R j)^(4/p)):=by
      funext j
      rw [wholeLaw_rpow_square_eq (hR j) (2/p)]
      congr 1
      ring
    change |nativeJointHighRestorationSource .fourGLow n _ U _ _ _ _ T _ a z| ≤ _ at Hraw
    rw [Hpow] at Hraw
    have hA : 0 ≤ A:=add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
      (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
    have hB : 0 ≤ B:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
    have hZ : 0 ≤ Z:=by
      rw [show Z=∏e,sourceFactorScale xScale W initial e from (source_factor_scale_product _ _ _).symm]
      exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsScale) (M.hxs.trans_le (hxsScale.trans hxW)) initial e).le
    have Hmajor:=add_le_add
      (mul_le_mul_of_nonneg_right (show bh ≤ bh+bl+1 by linarith) (show 0 ≤ W*Z*A by positivity))
      (mul_le_mul_of_nonneg_right (show bl ≤ bh+bl+1 by linarith) (show 0 ≤ W^2*Z*B by positivity))
    apply Hraw.trans
    convert Hmajor using 1 <;> (try dsimp only [bh,bl,R,Z,A,B,as]) <;> ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_minimum_inherited_working_scale_resource_joint_HIGH_restoration_from_minimum_original_q
    (kind : NativeJointHighRestorationKind) (degree dOrder rBound : ℕ)
    (hd : 0 < dOrder) (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ)) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        ∀xScale W : ℝ,M.xs ≤ xScale → xScale ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*xScale → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀a z : T.Slot,T.splitIndex a z<U →
        let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
        let cost:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
          W*(T.forkCost R+edgeBudget 0 as R)
        |(W⁻¹)^k*nativeActualResourceJointHighRestoration_original_q kind M U P a z| ≤
          |P.coefficient| *nativeResourceScale xScale W 1 seed*(C*W*cost) := by
  classical
  have HP (a : Fin (degree+1)):=eventually_actual_minimum_inherited_canonical_working_scale_joint_HIGH_restoration_price_original_q
    (D:=D) kind a.val dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  choose C hC HC using HP
  let Cmax:=1+∑a : Fin (degree+1),C a
  have hsum : 0 ≤ ∑a : Fin (degree+1),C a:=Finset.sum_nonneg (fun a _=>(hC a).le)
  have hCmax : 0 < Cmax:=by dsimp only [Cmax];linarith
  have hdom a : C a ≤ Cmax:=by
    have H:=Finset.single_le_sum (fun a _=>(hC a).le) (Finset.mem_univ a)
    dsimp only [Cmax]
    linarith
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget_original_q
    (D:=D) (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  refine ⟨Cmax*A^degree,by positivity,?_⟩
  filter_upwards [Filter.eventually_all.mpr HC,HA] with n hn hnA
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  have Hgrids a:=hn a M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr Hgrids,hnA M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj hjA
  dsimp only at hj hjA ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth xScale W hxsScale hxW hW1 hmi hms hcut aSlot z haz
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
  let cost:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
    W*(T.forkCost R+edgeBudget 0 as R)
  let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hU)
  let I:=nativeActualResourceInitialFactors P.live
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) (by
        dsimp only [nativeOriginalCutLowErrorRadius]
        positivity)
  have hcost : 0 ≤ cost:=add_nonneg
    (add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
      (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _)))
    (mul_nonneg (M.hxs.le.trans (hxsScale.trans hxW)) (add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
  have hW : 0 < W:=M.hxs.trans_le (hxsScale.trans hxW)
  have hprice : 0 ≤ Cmax*W*cost:=by positivity
  have Hdegree : P.resources.length ≤ degree+1:=by rw [hP.total_factor_depth];omega
  have Hpair:=hjA U i star T P Hdegree (hi.trans (hs.le.trans hU)) (hs.le.trans hU)
    xScale W hxsScale hxW hmi hms 1 1 (by norm_num) (by norm_num)
  have Hlive : P.live.factors.length ≤ degree:=by
    have Hlen:=hP.total_factor_depth
    simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,List.length_map] at Hlen
    omega
  let a : Fin (degree+1):=⟨P.live.factors.length,by omega⟩
  have HL:=hj a U T hU hT G (fun _=>.centered) I xScale W hxsScale hxW hcut
    (native_actual_resource_canonical_source_mass P.live hi (hs.trans_le hU) Cmass xScale W hmi hms) aSlot z haz
  rw [native_actual_resource_live_scale_eq_annotations] at HL
  have Hcenter : nativePhysicalResourceCenter n M.sweepBf M.sweepHf as=
      (fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)):=by
    funext j
    exact (native_ordered_source_center_eq_completed n M.sweepBf M.sweepHf
      M.inherited_bf_monotone M.inherited_hf_monotone (partitionPoint_mem as ho j)).symm
  rw [←Hcenter] at HL
  have HL' : |nativeJointHighRestorationSource kind n q U b h K (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) T
      (G.canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).restProduct aSlot z| ≤
      nativeResourceScale xScale W 1 P.live.tags*(Cmax*W*cost):=by
    apply HL.trans
    have Hdom:=mul_le_mul_of_nonneg_left (hdom a)
      (show 0 ≤ W*nativeResourceScale xScale W 1 P.live.tags*cost by
        exact mul_nonneg (mul_nonneg (M.hxs.le.trans (hxsScale.trans hxW)) (actual_resource_raw_scale_pos _ (M.hxs.trans_le hxsScale) (M.hxs.trans_le (hxsScale.trans hxW))).le) hcost)
    convert Hdom using 1 <;> ring
  have H:=actual_resource_joint_HIGH_normalized_price_le_original_q kind M hP hdepth ho hi (hs.trans_le hU)
    aSlot z hA hxsScale hxW hprice Hpair HL'
  apply H.trans_eq
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

theorem native_actual_original_fresh_resource_HIGH_part_eq_two_resources_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    (part : Fin 3) (l t : ℝ) :
    let g:=nativeFreshAtSlot T 0 P.live.test.target star
    nativeActualOriginalFreshResourceHigherHighPart_original_q M U P part l t=
      nativeActualResourceHigherHighPart_original_q M U (P.retarget 0) part (g.embed P.live.test.target) g.mark l t+
      nativeActualResourceHigherHighPart_original_q M U (P.retarget 0).freeze part (g.embed P.live.test.target) g.mark l t := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  have HQ : cutFullVariance n q U 1 1 b h K=qfull:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have HP : (fun σ=>Pc (g.restRestrict (g.tree.cavityAssignment σ).1))=
      fun σ=>(P.retarget 0).value (fullWeight n) (fullFeature n) 0 qfull
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0 σ+
        (P.retarget 0).freeze.value (fullWeight n) (fullFeature n) 0 qfull
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0 σ:=by
    funext σ
    have H:=native_actual_centered_fresh_resource_readout (U:=U) q b h K C T P ho σ
    dsimp only at H
    rw [HQ] at H
    exact H
  unfold nativeActualOriginalFreshResourceHigherHighPart_original_q nativeActualResourceHigherHighPart_original_q
  dsimp only
  change nativeActualHigherHighPart part n q U b h K g.tree
    (fun σ=>Pc (g.restRestrict (g.tree.cavityAssignment σ).1)) (g.embed P.live.test.target) g.mark l t=_
  rw [HP,native_actual_higher_HIGH_part_add_test]

theorem native_actual_original_fresh_resource_HIGH_part_eq_centered_retarget_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    (part : Fin 3) (l t : ℝ) :
    let g:=nativeFreshAtSlot T 0 P.live.test.target star
    nativeActualOriginalFreshResourceHigherHighPart_original_q M U P part l t=
      nativeActualOriginalCenteredResourceHigherHighPart_original_q M U (P.retarget 0) part
        (g.embed P.live.test.target) g.mark l t := by
  dsimp only
  rw [native_actual_original_fresh_resource_HIGH_part_eq_two_resources_original_q M U P ho,
    native_actual_original_centered_resource_HIGH_part_eq_two_resources_original_q M U (P.retarget 0) ho]

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

def nativeActualOriginalCenteredResourceJointHighRestoration_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (kind : NativeJointHighRestorationKind) (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (a z : T.Slot) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  nativeJointHighRestorationSource kind n q U b h K C T Pc a z

theorem native_actual_original_centered_resource_joint_HIGH_restoration_eq_two_resources_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (kind : NativeJointHighRestorationKind) (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    (a z : T.Slot) :
    nativeActualOriginalCenteredResourceJointHighRestoration_original_q kind M U P a z=
      nativeActualResourceJointHighRestoration_original_q kind M U P a z+
      nativeActualResourceJointHighRestoration_original_q kind M U P.freeze a z := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_resource_original_centered_rest_eq_two_resources (U:=U) q b h K C T P ho
  dsimp only at Hread
  rw [HQ] at Hread
  unfold nativeActualOriginalCenteredResourceJointHighRestoration_original_q nativeActualResourceJointHighRestoration_original_q
  dsimp only
  rw [Hread]
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ) ≤ M.sweepBf v from M.inherited_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ) ≤ M.sweepHf v from M.inherited_hf_monotone hu hv huv) as ho
  have HK:=native_continuum_mixed_clock_nonneg n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have HKm:=native_continuum_mixed_clock_monotone n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  simpa only [one_mul] using native_joint_HIGH_restoration_source_test_linear kind n q U b h K C T ho
    (nativeActualResourceRestValue P 0 (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 C)
    (nativeActualResourceRestValue P.freeze 0 (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 C) a z 1 1
    (by intro j x;cases x <;> exact NNReal.coe_nonneg _)
    (by intro x;cases x <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) HK hbm hhm HKm

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem eventually_actual_minimum_inherited_working_scale_centered_resource_joint_HIGH_restoration_from_minimum_original_q
    (kind : NativeJointHighRestorationKind) (degree dOrder rBound : ℕ)
    (hd : 0 < dOrder) (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ)) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        ∀xScale W : ℝ,M.xs ≤ xScale → xScale ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*xScale → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀a z : T.Slot,T.splitIndex a z<U →
        let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
        let cost:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
          W*(T.forkCost R+edgeBudget 0 as R)
        |(W⁻¹)^k*nativeActualOriginalCenteredResourceJointHighRestoration_original_q kind M U P a z| ≤
          |P.coefficient| *nativeResourceScale xScale W 1 seed*(C*W*cost) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_working_scale_resource_joint_HIGH_restoration_from_minimum_original_q
    (D:=D) kind degree dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth xScale W hxsScale hxW hW1 hmi hms hcut a z haz
  have ho:=finiteCutMasses_ordered us hus jGrid
  rw [native_actual_original_centered_resource_joint_HIGH_restoration_eq_two_resources_original_q kind M U P ho a z,mul_add]
  have HP:=hj i star U k seed T P hP hi hs hU hT hdepth xScale W hxsScale hxW hW1 hmi hms hcut a z haz
  have HF:=hj i star U k seed T P.freeze hP.freeze hi hs hU hT hdepth xScale W hxsScale hxW hW1 hmi hms hcut a z haz
  simp only [NativeResourceTerm.freeze,abs_neg] at HF
  apply ((abs_add_le _ _).trans (add_le_add HP HF)).trans_eq
  ring

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 15000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_G_high_restoration_original_q
    (aDegree dOrder rBound : ℕ) (ha : 0 < aDegree) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (t : ℝ),
          U ≤ as.length → t∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀a c e f : T.Slot,e≠f →
          let law:=cutFullVariance n q U 0 t b h K
          let high:=cutTSlope n U 0 b h K
          |cutMixedJet n q U b h K T (fun σ=>(G.canonicalOriginalQSource M forms).product σ*
            nativeOriginalHighGAtom T U K b S a c e f σ) 0 0 0 t| ≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.pairForkVariation rBound*
                (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                  sourceMonomialScale x W initial)*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
                (nativeWholeLawErrorRadius n as law high (T.splitIndex e f))^(2/p)*
                nativeWholeLawProfileCost n law high T (2/p)) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_continuum_square_even_moment_original_q
    (D:=D) aDegree dOrder rBound ha hd Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [HP] with n hnP
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T t hU ht hT G forms initial x W hxsx hxW hmass a c e f hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U 0 t b h K
  let high:=cutTSlope n U 0 b h K
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*
    (4*Cf+2*Temp))*Cp^aDegree*
      sourceMonomialScale x W initial
  let P:=(G.canonicalOriginalQSource M forms).product
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    (M.sweep_bf_monotone) (M.sweep_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ) ≤ M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ) ≤ M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf (M.sweep_bf_monotone) (M.sweep_hf_monotone)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have Hb j : b j ≤ Temp:=
    (hsource _ (partitionPoint_mem as ho j)).1
  have HC : 0 ≤ C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun i _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial i).le)
  have Hraw:=hgrid U T 0 t (by norm_num) ht hT G forms initial x W hxsx hxW hmass
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|P σ|^(2*(p/(p-2)))) 0 ≤ C^(2*(p/(p-2))) := by
    apply T.disorderExpect_rpow_moment_le (fullWeight_pos n) (fullFeature n) ho 0 law 0 P
      (by have Hq : 0 < p/(p-2):=div_pos (by linarith) (by linarith);positivity)
      (show 2*(p/(p-2)) ≤ ((2*dOrder:ℕ):ℝ) by push_cast;linarith) HC
    simpa only [Real.rpow_natCast,P,C,law,q,b,h,S,K,as] using Hraw
  have Hcap:=native_centered_high_kernel_abs_le n U b h S (fun _=>NNReal.coe_nonneg _) Hb HS
  have H:=native_original_G_profile_restoration_bound n U b h K S (fun _=>rfl)
    T ho hU hT law P a c e f hef high HC hp (by positivity) (by positivity) HPmoment Hcap Hcap
  rw [native_cutMixedJet_zero_eq_profile n q U b h K T ho _ 0
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm (by norm_num) ht]
  exact H

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 15000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_G_low_restoration_original_q
    (aDegree rBound : ℕ) (ha : 0 < aDegree)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Cq : ℝ,0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l : ℝ),
          U ≤ as.length → l∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀a c e f : T.Slot,e≠f →
          let law:=cutFullVariance n q U l 1 b h K
          let high:=cutTSlope n U 0 b h K
          |cutLowJet n q U b h K T (fun σ=>(G.canonicalOriginalQSource M forms).product σ*
            nativeOriginalHighGAtom T U K b S a c e f σ) 0 1 l 1| ≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.absJetVariation rBound 1*
                (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
                  sourceMonomialScale x W initial)*
                nativeWholeLawErrorRadius n as law high (T.splitIndex e f)*(Cq*W)) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_continuum_square_even_moment_original_q
    (D:=D) aDegree 2 rBound ha (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cq,hCq,HQ⟩:=eventually_actual_minimum_inherited_original_low_profile_fourth_original_q
    (D:=D) Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,Cq,hCq,?_⟩
  filter_upwards [HP,HQ] with n hnP hnQ
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnQ M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid hgridQ
  dsimp only at hgrid hgridQ ⊢
  intro U T l hU hl hT G forms initial x W hxsx hxW hcut hmass a c e f hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l 1 b h K
  let high:=cutTSlope n U 0 b h K
  let C:=Real.exp (wholeLawRowComparisonConstant rBound*
    (4*Cf+2*Temp))*Cp^aDegree*
      sourceMonomialScale x W initial
  let P:=(G.canonicalOriginalQSource M forms).product
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    (M.sweep_bf_monotone) (M.sweep_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ) ≤ M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ) ≤ M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf (M.sweep_bf_monotone) (M.sweep_hf_monotone)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HC : 0 ≤ C:=by
    dsimp only [C]
    rw [←source_factor_scale_product]
    exact mul_nonneg (by positivity) (Finset.prod_nonneg fun i _=>
      (source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial i).le)
  have Hraw:=hgrid U T l 1 hl (by norm_num) hT G forms initial x W hxsx hxW hmass
  have HPmoment : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|P σ|^4) 0 ≤ C^4:=Hraw
  have HQmoment:=hgridQ U l 1 1 W hU hl (by norm_num) (by norm_num) (hxsx.trans hxW) hcut
  have H:=native_original_G_raw_profile_restoration_bound n U b h K S (fun _=>rfl)
    T ho hU hT law P a c e f hef (cutLSlope n U 1 b h K) HC
    (mul_pos hCq ((M.hxs.trans_le hxsx).trans_le hxW)) HPmoment HQmoment
  rw [cutLowJet_eq_profileJets n q U b h K T ho _ 0
    (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
    (fun i=>by cases i <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm 1 hl (by norm_num)]
  simpa only [List.replicate_one] using H

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_G_word_high_restoration_original_q
    (aDegree dOrder rBound : ℕ) (ha : 0 < aDegree) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (t : ℝ),
          U ≤ as.length → t∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(g : NativeOriginalGMarkedWord T) (a : T.Slot),g.z.embed g.r.mark≠g.z.mark →
          let law:=cutFullVariance n q U 0 t b h K
          let high:=cutTSlope n U 0 b h K
          |cutMixedJet n q U b h K g.tree
            (g.originalRestorationTest U K b S (G.canonicalOriginalQSource M forms).product a) 0 0 0 t| ≤
            |(1/2:ℝ)*fullScalarCutConnected4 g.tree U K
              (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
              (g.z.embed g.r.mark) g.z.mark| *
              (ClockTree.pairForkVariation (rBound+3)*
                (Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Cp^aDegree*
                  sourceMonomialScale x W initial)*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
                (nativeWholeLawErrorRadius n as law high (g.tree.splitIndex (g.z.embed g.r.mark) g.z.mark))^(2/p)*
                nativeWholeLawProfileCost n law high g.tree (2/p)) := by
  obtain ⟨Cp,hCp,H⟩:=eventually_actual_minimum_inherited_canonical_G_high_restoration_original_q
    (D:=D) aDegree dOrder (rBound+3) ha hd p hp hOrder Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T t hU ht hT G forms initial x W hxsx hxW hmass g a hef
  have hTg : g.tree.leaves ≤ rBound+3:=g.leaves_le.trans (by omega)
  have hmassg (e : Fin aDegree) : (g.canonicalOldShape G).sourceLowMass e ≤
      Cmass*sourceFactorScale x W initial e:=by
    rw [g.canonicalOldShape_sourceLowMass G e]
    exact hmass e
  have HB:=hgrid U g.tree t hU ht hTg (g.canonicalOldShape G) forms initial x W hxsx hxW hmassg
    (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
    (g.z.embed g.r.mark) g.z.mark hef
  rw [←g.originalRestorationTest_canonical_original_q G M forms] at HB
  exact HB

theorem eventually_actual_minimum_inherited_canonical_G_word_low_restoration_original_q
    (aDegree rBound : ℕ) (ha : 0 < aDegree)
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Cq : ℝ,0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l : ℝ),
          U ≤ as.length → l∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(g : NativeOriginalGMarkedWord T) (a : T.Slot),g.z.embed g.r.mark≠g.z.mark →
          let law:=cutFullVariance n q U l 1 b h K
          let high:=cutTSlope n U 0 b h K
          |cutLowJet n q U b h K g.tree
            (g.originalRestorationTest U K b S (G.canonicalOriginalQSource M forms).product a) 0 1 l 1| ≤
            |(1/2:ℝ)*fullScalarCutConnected4 g.tree U K
              (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
              (g.z.embed g.r.mark) g.z.mark| *
              (ClockTree.absJetVariation (rBound+3) 1*
                (Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Cp^aDegree*
                  sourceMonomialScale x W initial)*
                nativeWholeLawErrorRadius n as law high (g.tree.splitIndex (g.z.embed g.r.mark) g.z.mark)*(Cq*W)) := by
  obtain ⟨Cp,hCp,Cq,hCq,H⟩:=eventually_actual_minimum_inherited_canonical_G_low_restoration_original_q
    (D:=D) aDegree (rBound+3) ha Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,Cq,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T l hU hl hT G forms initial x W hxsx hxW hcut hmass g a hef
  have hTg : g.tree.leaves ≤ rBound+3:=g.leaves_le.trans (by omega)
  have hmassg (e : Fin aDegree) : (g.canonicalOldShape G).sourceLowMass e ≤
      Cmass*sourceFactorScale x W initial e:=by
    rw [g.canonicalOldShape_sourceLowMass G e]
    exact hmass e
  have HB:=hgrid U g.tree l hU hl hTg (g.canonicalOldShape G) forms initial x W hxsx hxW hcut hmassg
    (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
    (g.z.embed g.r.mark) g.z.mark hef
  rw [←g.originalRestorationTest_canonical_original_q G M forms] at HB
  exact HB

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

def nativeActualResourceLongitudinalRestoration_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (a : T.Slot) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  nativeOriginalLongitudinalRestoration n q U b h K C T
    (P.value (fullWeight n) (fullFeature n) 0 qfull
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ)) C 0) a

theorem actual_resource_longitudinal_restoration_normalized_profile_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hdepth : seed.length+k ≤ degree)
    (ho : MassOrdered 0 as) (hi : i ≤ star) (hs : star < as.length)
    (a : T.Slot)
    {A x W price : ℝ} (hA : 1 ≤ A) (hx : M.xs ≤ x) (hxW : x ≤ W) (hprice : 0 ≤ price)
    (Hpair : P.PairMomentBudget (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as
        (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)) 1 1)
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) 0 A x W 1)
    (Hlive :
      let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
      let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
      let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      let G:=nativeActualResourceCanonicalShape P.live hi hs
      |nativeOriginalLongitudinalRestoration n q U b h K C T
        (G.canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).product a| ≤
        nativeResourceScale x W 1 P.live.tags*price) :
    |(W⁻¹)^k*nativeActualResourceLongitudinalRestoration_original_q M U P a| ≤
      |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*price := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let G:=nativeActualResourceCanonicalShape P.live hi hs
  let scalar:=nativeActualResourceOriginalScalar_original_q M U P
  let F:=(G.canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).product
  have HE : nativeActualResourceLongitudinalRestoration_original_q M U P a=
      scalar*nativeOriginalLongitudinalRestoration n q U b h K C T F a := by
    unfold nativeActualResourceLongitudinalRestoration_original_q
    dsimp only
    have HP : P.value (fullWeight n) (fullFeature n) 0
        (finitePhysicalCavitySquareVariance n U as b h 1 1)
        (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
        (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) 0=(fun σ=>scalar*F σ):=by
      funext σ
      dsimp only [F,G]
      rw [native_actual_resource_canonical_product_eq_live_original_q]
      rfl
    rw [HP]
    have hbm : Monotone b:=comp_partitionPoint_monotone
      (fun u hu v hv huv=>show (M.sweepBf u:ℝ) ≤ M.sweepBf v from M.inherited_bf_monotone hu hv huv) as ho
    have hhm : Monotone h:=comp_partitionPoint_monotone
      (fun u hu v hv huv=>show (M.sweepHf u:ℝ) ≤ M.sweepHf v from M.inherited_hf_monotone hu hv huv) as ho
    have HK:=native_continuum_mixed_clock_nonneg n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho
    have HKm:=native_continuum_mixed_clock_monotone n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho
    exact native_original_longitudinal_restoration_const_mul n q U b h K C T ho F a scalar
      (by intro j x;cases x <;> exact NNReal.coe_nonneg _)
      (by intro x;cases x <;> first | exact hbm | exact hhm)
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) HK hbm hhm HKm
  have HS:=hP.normalized_original_scalar_times_live_raw_scale_le hdepth
    (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavitySquareVariance n U as b h 1 1) 0
    (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as)
    A x W 1 hA (M.hxs.trans_le hx) ((M.hxs.trans_le hx).trans_le hxW)
    zero_lt_one le_rfl hi hs Hpair
  change |(W⁻¹)^k*scalar| *nativeResourceScale x W 1 P.live.tags ≤ _ at HS
  dsimp only at Hlive
  rw [HE,mul_assoc,←mul_assoc,abs_mul]
  apply (mul_le_mul_of_nonneg_left Hlive (abs_nonneg ((W⁻¹)^k*scalar))).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right HS hprice

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

def nativeActualOriginalCenteredResourceLongitudinalRestoration_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (a : T.Slot) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  nativeOriginalLongitudinalRestoration n q U b h K C T (fun σ=>Pc (T.cavityAssignment σ).1) a

theorem native_actual_centered_resource_longitudinal_restoration_eq_two_resources_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as) (a : T.Slot) :
    nativeActualOriginalCenteredResourceLongitudinalRestoration_original_q M U P a=
      nativeActualResourceLongitudinalRestoration_original_q M U P a+
      nativeActualResourceLongitudinalRestoration_original_q M U P.freeze a := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_resource_original_centered_rest_eq_two_resources (U:=U) q b h K C T P ho
  dsimp only at Hread
  rw [HQ] at Hread
  unfold nativeActualOriginalCenteredResourceLongitudinalRestoration_original_q nativeActualResourceLongitudinalRestoration_original_q
  dsimp only
  rw [Hread]
  simp_rw [native_actual_resource_rest_value_eq_full]
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ) ≤ M.sweepBf v from M.inherited_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ) ≤ M.sweepHf v from M.inherited_hf_monotone hu hv huv) as ho
  have HK:=native_continuum_mixed_clock_nonneg n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have HKm:=native_continuum_mixed_clock_monotone n M.sweepBf M.sweepHf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  exact native_original_longitudinal_restoration_add n q U b h K C T ho _ _ a
    (by intro j x;cases x <;> exact NNReal.coe_nonneg _)
    (by intro x;cases x <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) HK hbm hhm HKm

theorem native_actual_fresh_resource_longitudinal_restoration_eq_centered_retarget_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as) (right : Bool) :
    let g:=nativeFreshAtSlot T 0 P.live.test.target star
    nativeActualOriginalFreshResourceLongitudinalRestoration_original_q M U P right=
      nativeActualOriginalCenteredResourceLongitudinalRestoration_original_q M U (P.retarget 0)
        (if right then g.mark else g.embed P.live.test.target) := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_centered_resource_fresh_rest_readout (U:=U) q b h K C T P ho
  dsimp only at Hread
  rw [HQ] at Hread
  unfold nativeActualOriginalFreshResourceLongitudinalRestoration_original_q nativeActualOriginalCenteredResourceLongitudinalRestoration_original_q
  dsimp only
  rw [Hread]

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 16000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem native_actual_current_G_restoration_eq_canonical_source_original_q
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (q : ℕ→RestCoordinate n→ℝ) :
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let G:=nativeGeneratedCompleteShape n P.live.test P.live.ancestry hi
      (hs.trans_le hP.highCut_le_length)
    nativeActualGProjectedRestoration_original_q T P.live.test star U M q=
      nativeOriginalGProjectedDisplacementRestoration T P.live.test.target star U q b h K S
        (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
        (G.canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).restProduct := by
  dsimp only
  let G:=nativeGeneratedCompleteShape n P.live.test P.live.ancestry hi
    (hs.trans_le hP.highCut_le_length)
  let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
  have HP : (G.canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).restProduct=
      nativeRestGeneratedTestValue T P.live.test R C :=
    funext (native_generated_complete_canonical_rest_product_original_q n P.live.test P.live.ancestry hi
      (hs.trans_le hP.highCut_le_length) M)
  rw [HP]
  have HC (j : ℕ) : orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)=C j:=
    native_ordered_source_center_eq_completed n M.sweepBf M.sweepHf
      (M.sweep_bf_monotone) (M.sweep_hf_monotone) (partitionPoint_mem as ho j)
  have HCfun : C=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j):=funext (fun j=>(HC j).symm)
  unfold nativeActualGProjectedRestoration_original_q
  dsimp only
  change nativeOriginalGProjectedDisplacementRestoration T P.live.test.target star U q _ _ _ C R
      (nativeRestGeneratedTestValue T P.live.test R C)=_
  rw [HCfun]

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem native_actual_resource_G_restoration_eq_canonical_source_original_q
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star)
    (hs : star < U) (ho : MassOrdered 0 as)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (q : ℕ→RestCoordinate n→ℝ) :
    let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
    let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
    let K:=fun j=>h j+b j*S j
    let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hP.highCut_le_length)
    nativeActualGProjectedRestoration_original_q T P.live.test star U M q=
      nativeOriginalGProjectedDisplacementRestoration T P.live.test.target star U q b h K S
        (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
        (G.canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).restProduct := by
  have H:=native_actual_current_G_restoration_eq_canonical_source_original_q hP hi hs ho M q
  dsimp only at H ⊢
  have HE :
      ((nativeGeneratedCompleteShape n P.live.test P.live.ancestry hi
        (hs.trans_le hP.highCut_le_length)).canonicalOriginalQSource M
        (fun _=>NativeSourceFactorForm.centered)).restProduct=
      ((nativeActualResourceCanonicalShape P.live hi
        (hs.trans_le hP.highCut_le_length)).canonicalOriginalQSource M
        (fun _=>NativeSourceFactorForm.centered)).restProduct := by
    funext σ
    rw [native_generated_complete_canonical_rest_product_original_q,
      native_actual_resource_canonical_rest_product_eq_live_original_q]
    rfl
  rw [HE] at H
  exact H

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem actual_resource_Ga_restoration_normalized_profile_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k degree : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P)
    (hdepth : seed.length+k ≤ degree) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star < as.length)
    {A x W ε price : ℝ} (hA : 1 ≤ A) (hx : M.xs ≤ x) (hxW : x ≤ W)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hprice : 0 ≤ price)
    (Hpair : P.PairMomentBudget (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as
        (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)) 1 1)
      (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
      (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) 0 A x W ε)
    (Hlive : |nativeActualGProjectedRestoration_original_q T P.live.test star U M
      (fun j=>Sum.elim (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ))
        (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ)))| ≤
      nativeResourceScale x W 1 P.live.tags*price) :
    |(W⁻¹)^k*nativeActualResourceGaRestoration_original_q M U P| ≤
      |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*price := by
  have hx0:=M.hxs.trans_le hx
  have hW:=hx0.trans_le hxW
  have HS:=hP.normalized_original_scalar_times_live_raw_scale_le hdepth
    (fullWeight_pos n) (fullFeature n) ho 0
    (finitePhysicalCavitySquareVariance n U as
      (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)) 1 1)
    0 (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
    (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as)
    A x W ε hA hx0 hW hε hε1 hi hs Hpair
  let scalar:=nativeActualResourceOriginalScalar_original_q M U P
  let live:=nativeActualGProjectedRestoration_original_q T P.live.test star U M
    (fun j=>Sum.elim (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ))
      (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ)))
  change |(W⁻¹)^k*scalar| *nativeResourceScale x W 1 P.live.tags ≤ _ at HS
  have H:=mul_le_mul_of_nonneg_left Hlive (abs_nonneg ((W⁻¹)^k*scalar))
  have HF:=mul_le_mul_of_nonneg_right HS hprice
  change |live| ≤ _ at Hlive
  calc
    |(W⁻¹)^k*nativeActualResourceGaRestoration_original_q M U P|=
      |(W⁻¹)^k*scalar| *|live| := by
        dsimp only [nativeActualResourceGaRestoration_original_q,scalar,live]
        rw [←abs_mul]
        congr 1
        ring
    _ ≤ |(W⁻¹)^k*scalar| *(nativeResourceScale x W 1 P.live.tags*price) := H
    _ ≤ _ := by simpa only [mul_assoc] using HF

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_G_word_restoration_original_budget_original_q
    (aDegree dOrder rBound : ℕ) (ha : 0 < aDegree) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Ch Cl Cq : ℝ,0 < Ch ∧ 0 < Cl ∧ 0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(g : NativeOriginalGMarkedWord T) (a : T.Slot),
          |nativeActualLawRestorationRemainder n q U b h K g.tree
            (g.originalRestorationTest U K b S (G.canonicalOriginalQSource M forms).product a)| ≤
            nativeOriginalGWordRestorationCost g U (rBound+3) M.sweepBf M.sweepHf K a Mclock Temp p
              (Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Ch^aDegree*
                sourceMonomialScale x W initial)
              (Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Cl^aDegree*
                sourceMonomialScale x W initial) (Cq*W) := by
  obtain ⟨Ch,hCh,HH⟩:=eventually_actual_minimum_inherited_canonical_G_word_high_restoration_original_q
    (D:=D) aDegree dOrder rBound ha hd p hp hOrder Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cl,hCl,Cq,hCq,HL⟩:=eventually_actual_minimum_inherited_canonical_G_word_low_restoration_original_q
    (D:=D) aDegree rBound ha Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [HH,HL] with n hnH hnL
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnH M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnL M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgridH hgridL
  dsimp only at hgridH hgridL ⊢
  intro U T hU hT G forms initial x W hxsx hxW hcut hmass g a
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
  let j:=g.tree.splitIndex (g.z.embed g.r.mark) g.z.mark
  let κ:=|(1/2:ℝ)*fullScalarCutConnected4 g.tree U K
    (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
    (g.z.embed g.r.mark) g.z.mark|
  let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Ch^aDegree*
    sourceMonomialScale x W initial
  let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Cl^aDegree*
    sourceMonomialScale x W initial
  let BH:=κ*(ClockTree.pairForkVariation (rBound+3)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
    (R j)^(2/p)*(g.tree.forkCost (fun j=>(R j)^(2/p))+ClockTree.edgeBudget 0 as (fun j=>(R j)^(2/p))))
  let BL:=κ*(ClockTree.absJetVariation (rBound+3) 1*CL*R j*(Cq*W))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  by_cases hdiag : g.z.embed g.r.mark=g.z.mark
  · rw [nativeOriginalGWordRestorationCost,ite_eq_left hdiag,
      actual_minimum_G_word_diagonal_restoration_zero_original_q M T ho g U _ a hdiag,abs_zero]
  · have hscale : 0 ≤ sourceMonomialScale x W initial:=by
      rw [←source_factor_scale_product]
      exact Finset.prod_nonneg fun i _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial i).le
    have hCH : 0 ≤ CH:=by dsimp [CH];positivity
    have hCL : 0 ≤ CL:=by dsimp [CL];positivity
    have hκ : 0 ≤ κ:=abs_nonneg _
    have hW : 0 ≤ W := (M.hxs.le.trans hxsx).trans hxW
    have hPV := ClockTree.pairForkVariation_nonneg (rBound+3)
    have hAV := ClockTree.absJetVariation_nonneg (rBound+3) 1
    have hR (j : ℕ) : 0 ≤ R j:=by
      dsimp only [R,nativeOriginalHighErrorEnvelope]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
          (add_nonneg (Real.sqrt_nonneg _) (by positivity))
    have hH (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
        |cutMixedJet n q U b h K g.tree
          (g.originalRestorationTest U K b S (G.canonicalOriginalQSource M forms).product a) 0 0 0 t| ≤ BH:=by
      have H:=hgridH U T t hU ht hT G forms initial x W hxsx hxW hmass g a hdiag
      apply H.trans
      have HR:=Real.rpow_le_rpow (nativeWholeLawErrorRadius_nonneg n as _ _ j)
        (actual_minimum_inherited_current_high_error_radius_le_original_original_q (l:=0) (t:=t) M Temp Cf hTemp hCf hsource hxs ho U
          (by norm_num) ht j (g.tree.splitIndex_le_clockLength _ _)) (show 0 ≤ 2/p by positivity)
      have HC:=actual_minimum_inherited_current_high_profile_le_original_original_q (l:=0) (t:=t) M Temp Cf hTemp hCf hsource hxs g.tree ho U
        (by norm_num) ht (show 0 ≤ 2/p by positivity)
      have hProf := native_whole_law_profile_cost_nonneg n ho
        (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) g.tree (2/p)
      have hRj := hR j
      dsimp only [BH]
      gcongr
    have hL (l : ℝ) (hl : l∈Icc (0:ℝ) 1) :
        |cutLowJet n q U b h K g.tree
          (g.originalRestorationTest U K b S (G.canonicalOriginalQSource M forms).product a) 0 1 l 1| ≤ BL:=by
      have H:=hgridL U T l hU hl hT G forms initial x W hxsx hxW hcut hmass g a hdiag
      apply H.trans
      have HR:=actual_minimum_inherited_current_high_error_radius_le_original_original_q (l:=l) (t:=1) M Temp Cf hTemp hCf hsource hxs ho U
        hl (by norm_num) j (g.tree.splitIndex_le_clockLength _ _)
      dsimp only [BL]
      gcongr
    have H:=native_actual_law_restoration_abs_le n q U b h K g.tree
      (g.originalRestorationTest U K b S (G.canonicalOriginalQSource M forms).product a) BH BL hH hL
    rw [nativeOriginalGWordRestorationCost,ite_eq_right hdiag]
    convert H using 1
    dsimp only [BH,BL,κ,CH,CL,R,j,Mclock,K,b,h,S,as]
    ring

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_unbonded_low_G_restoration_original_q
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (p : ℝ) (hp : 2<p) (hOrder : p/(p-2)≤(dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Ch Cl Cq : ℝ,0<Ch ∧ 0<Cl ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U≤as.length → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x →x≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀u z a c e f : T.Slot,u≠z → T.splitIndex u z<U → e≠f →
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
          let CH:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Ch^(aDegree+1)*
            (W*sourceMonomialScale x W initial)
          let CL:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cl^(aDegree+1)*
            (W*sourceMonomialScale x W initial)
          let J:=fun σ=>(G.canonicalOriginalQSource M forms).product σ*
            (deletedOverlap n (joinSpin (T.atSlot σ u))
              (joinSpin (T.atSlot σ z))-S (T.splitIndex u z))
          |nativeActualLawRestorationRemainder n q U b h K T
            (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ)|≤
            |(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f| *
              (ClockTree.pairForkVariation rBound*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
                (R (T.splitIndex e f))^(2/p)*
                (T.forkCost (fun j=>(R j)^(2/p))+ClockTree.edgeBudget 0 as (fun j=>(R j)^(2/p)))+
                ClockTree.absJetVariation rBound 1*CL*R (T.splitIndex e f)*(Cq*(1+Ccut)*W)) := by
  obtain ⟨Ch,hCh,HH⟩:=eventually_actual_minimum_inherited_unbonded_low_G_high_profile_original_q
    (D:=D) aDegree dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cl,Cq,hCl,hCq,HL⟩:=eventually_actual_minimum_inherited_unbonded_low_G_low_profile_original_q
    (D:=D) aDegree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [HH,HL] with n hnH hnL
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnH M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnL M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgridH hgridL
  dsimp only at hgridH hgridL ⊢
  intro U T hU hT G forms initial x W hxsx hxW hcut hmass u z a c e f huz huzcut hef
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
  let CH:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Ch^(aDegree+1)*
    (W*sourceMonomialScale x W initial)
  let CL:=Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cl^(aDegree+1)*
    (W*sourceMonomialScale x W initial)
  let J:=fun σ=>(G.canonicalOriginalQSource M forms).product σ*
    (deletedOverlap n (joinSpin (T.atSlot σ u))
      (joinSpin (T.atSlot σ z))-S (T.splitIndex u z))
  let κ:=|(1/2:ℝ)*fullScalarCutConnected4 T U K a c e f|
  let BH:=κ*(ClockTree.pairForkVariation rBound*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
    (R (T.splitIndex e f))^(2/p)*
    (T.forkCost (fun j=>(R j)^(2/p))+ClockTree.edgeBudget 0 as (fun j=>(R j)^(2/p))))
  let BL:=κ*(ClockTree.absJetVariation rBound 1*CL*R (T.splitIndex e f)*(Cq*(1+Ccut)*W))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    (M.sweep_bf_monotone) (M.sweep_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ)≤M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ)≤M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf
      (M.sweep_bf_monotone) (M.sweep_hf_monotone)) as ho
  have hK0 j : 0≤K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have hW : 0≤W:=(M.hxs.le.trans hxsx).trans hxW
  have hscale : 0 ≤ sourceMonomialScale x W initial:=by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun i _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial i).le
  have hCH : 0≤CH:=by dsimp [CH];positivity
  have hCL : 0≤CL:=by dsimp [CL];positivity
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hH (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
      |cutMixedJet n q U b h K T (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ) 0 0 0 t|≤BH:=by
    rw [native_cutMixedJet_zero_eq_profile n q U b h K T ho _ 0
      (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
      (fun i=>by cases i <;> first | exact hbm | exact hhm)
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm (by norm_num) ht]
    have H:=hgridH U T 0 t hU (by norm_num) ht hT G forms initial x W hxsx hxW hcut hmass u z a c e f huz huzcut hef
    apply H.trans
    have HR:=Real.rpow_le_rpow (nativeWholeLawErrorRadius_nonneg n as _ _ (T.splitIndex e f))
      (actual_minimum_inherited_current_high_error_radius_le_original_original_q (l:=0) (t:=t) M Temp Cf hTemp hCf hsource hxs ho U
        (by norm_num) ht (T.splitIndex e f) (T.splitIndex_le_clockLength e f)) (show 0≤2/p by positivity)
    have HC:=actual_minimum_inherited_current_high_profile_le_original_original_q (l:=0) (t:=t) M Temp Cf hTemp hCf hsource hxs T ho U
      (by norm_num) ht (show 0≤2/p by positivity)
    have Hprof:=native_whole_law_profile_cost_nonneg n ho
      (cutFullVariance n q U 0 t b h K) (cutTSlope n U 0 b h K) T (2/p)
    have Hpv:=ClockTree.pairForkVariation_nonneg rBound
    have HRj:=hR (T.splitIndex e f)
    dsimp only [BH,κ]
    gcongr
  have hL (l : ℝ) (hl : l∈Icc (0:ℝ) 1) :
      |cutLowJet n q U b h K T (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ) 0 1 l 1|≤BL:=by
    rw [cutLowJet_eq_profileJets n q U b h K T ho _ 0
      (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
      (fun i=>by cases i <;> first | exact hbm | exact hhm)
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm 1 hl (by norm_num)]
    simp only [List.replicate_one]
    have H:=hgridL U T l 1 hU hl (by norm_num) hT G forms initial x W hxsx hxW hcut hmass u z a c e f huz huzcut hef
    apply H.trans
    have HR:=actual_minimum_inherited_current_high_error_radius_le_original_original_q (l:=l) (t:=1) M Temp Cf hTemp hCf hsource hxs ho U
      hl (by norm_num) (T.splitIndex e f) (T.splitIndex_le_clockLength e f)
    have Hav:=ClockTree.absJetVariation_nonneg rBound 1
    have HRj:=hR (T.splitIndex e f)
    dsimp only [BL,κ]
    gcongr
  have H:=native_actual_law_restoration_abs_le n q U b h K T
    (fun σ=>J σ*nativeOriginalHighGAtom T U K b S a c e f σ) BH BL hH hL
  convert H using 1
  dsimp only [BH,BL,κ,CH,CL,R,J,Mclock,K,b,h,S,q,as]
  ring

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_unbonded_low_G_pair_restoration_original_q
    (aDegree dOrder rBound : ℕ) (hd : 0<dOrder)
    (p : ℝ) (hp : 2<p) (hOrder : p/(p-2)≤(dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCmass : 0≤Cmass) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃Ch Cl Cq : ℝ,0<Ch ∧ 0<Cl ∧ 0<Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U≤as.length → T.leaves≤rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs≤x →x≤W →
          partitionPoint 0 as U≤Ccut*W →
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e) →
        ∀u z a c : T.Slot,u≠z → T.splitIndex u z<U →
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
          let f2:=fun j=>((R j)^(2/p))^2
          let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Ch^(aDegree+1)*
            (W*sourceMonomialScale x W initial)
          let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Cl^(aDegree+1)*
            (W*sourceMonomialScale x W initial)
          let AH:=pairForkVariation (rBound+2)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*((rBound:ℝ)+3)
          let AL:=absJetVariation (rBound+2) 1*CL*(Cq*(1+Ccut)*W)
          let J:=fun σ=>(G.canonicalOriginalQSource M forms).restProduct σ*
            (deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot u),false))
              (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot z),false))-S (T.splitIndex u z))
          |nativeOriginalHighPairRestoration n q U b h K S T J a c|≤
            AH*pairForkVariation rBound*(T.forkCost f2+edgeBudget 0 as f2)+
              AL*pairForkVariation rBound*(T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=eventually_actual_minimum_inherited_unbonded_low_G_restoration_original_q
    (D:=D) aDegree dOrder (rBound+2) hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT G forms initial x W hxsx hxW hcut hmass u z a c huz huzcut
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
  let f2:=fun j=>((R j)^(2/p))^2
  let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Ch^(aDegree+1)*
    (W*sourceMonomialScale x W initial)
  let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+2)*Mclock)*Cl^(aDegree+1)*
    (W*sourceMonomialScale x W initial)
  let AH0:=pairForkVariation (rBound+2)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)
  let AH:=AH0*((rBound:ℝ)+3)
  let AL:=absJetVariation (rBound+2) 1*CL*(Cq*(1+Ccut)*W)
  let J:=fun σ=>(G.canonicalOriginalQSource M forms).restProduct σ*
    (deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot u),false))
      (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot z),false))-S (T.splitIndex u z))
  let F:=fun (p : MarkedPlacement T) (r : MarkedPlacement p.tree)=>
    nativeActualLawRestorationRemainder n q U b h K r.tree
      (fun σ=>J (p.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1))*
        nativeOriginalHighGAtom r.tree U K b S (r.embed (p.embed a)) (r.embed (p.embed c))
          (r.embed p.mark) r.mark σ)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hscale : 0 ≤ sourceMonomialScale x W initial:=by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial e).le
  have hW : 0≤W:=(M.hxs.le.trans hxsx).trans hxW
  have hAH0 : 0≤AH0:=by
    dsimp only [AH0,CH]
    exact mul_nonneg (mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) (by positivity))
      (Real.rpow_nonneg (by positivity) _)) (Real.rpow_nonneg (by positivity) _)
  have hAH : 0≤AH:=mul_nonneg hAH0 (by positivity)
  have hCL : 0≤CL:=by dsimp [CL];positivity
  have hAL : 0≤AL:=mul_nonneg (mul_nonneg (absJetVariation_nonneg _ _) hCL) (by positivity)
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf2 j : 0≤f2 j:=sq_nonneg _
  have HF (p0 : MarkedPlacement T) (hp0 : p0∈T.markedAttach 0)
      (r : MarkedPlacement p0.tree) (hr : r∈p0.tree.markedAttach 0) :
      |F p0 r|≤AH*(r.tree.forkCost f2+edgeBudget 0 as f2)+AL*(r.tree.forkCost R+edgeBudget 0 as R) := by
    by_cases hdiag : r.embed p0.mark=r.mark
    · have Hzero:=actual_minimum_original_G_diagonal_restoration_zero_original_q M r.tree ho U
        (fun σ=>J (p0.restRestrict (r.restRestrict (r.tree.cavityAssignment σ).1)))
        (r.embed (p0.embed a)) (r.embed (p0.embed c)) r.mark
      dsimp only [F]
      rw [hdiag,Hzero,abs_zero]
      exact add_nonneg (mul_nonneg hAH (add_nonneg (r.tree.forkCost_nonneg hf2) (edgeBudget_nonneg ho hf2)))
        (mul_nonneg hAL (add_nonneg (r.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
    · let Gr:=(G.nativeCMarkedLift p0 hp0).nativeCMarkedLift r hr
      have hGr e : Gr.sourceLowMass e≤Cmass*sourceFactorScale x W initial e:=by
        simpa only [Gr,ActualNaturalBoundaryShape.nativeCMarkedLift_sourceLowMass] using hmass e
      have hleaf : r.tree.leaves≤rBound+2:=by
        have H1:=T.markedAttach_leaves 0 p0 hp0
        have H2:=p0.tree.markedAttach_leaves 0 r hr
        omega
      have hlow : r.tree.splitIndex (r.embed (p0.embed u)) (r.embed (p0.embed z))<U:=by
        rwa [(p0.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p0 hp0).2]
      have hdistinct : r.embed (p0.embed u)≠r.embed (p0.embed z):=by
        intro HH
        exact huz ((T.markedAttach_embed_preserves 0 p0 hp0).1 ((p0.tree.markedAttach_embed_preserves 0 r hr).1 HH))
      have Hrest:=hgrid U r.tree hU hleaf Gr forms initial x W hxsx hxW hcut hGr
        (r.embed (p0.embed u)) (r.embed (p0.embed z))
        (r.embed (p0.embed a)) (r.embed (p0.embed c)) (r.embed p0.mark) r.mark hdistinct hlow hdiag
      have Htest:=G.native_double_marked_unbonded_low_pair_test_original_q M forms S u z p0 hp0 r hr
      change |nativeActualLawRestorationRemainder n q U b h K r.tree _|≤_
      have Hleft:=congrArg (fun J0 : r.tree.Assignment→ℝ=>
        nativeActualLawRestorationRemainder n q U b h K r.tree
          (fun σ=>J0 σ*nativeOriginalHighGAtom r.tree U K b S (r.embed (p0.embed a))
            (r.embed (p0.embed c)) (r.embed p0.mark) r.mark σ)) Htest
      rw [Hleft]
      apply Hrest.trans
      let ff:=fun j=>(R j)^(2/p)
      have hff j : 0≤ff j:=Real.rpow_nonneg (hR j) _
      have HY:=native_distinct_pair_profile_product_le r.tree ho ff (r.embed p0.mark) r.mark hdiag
      have HS:=r.tree.split_le_forkCost hR (r.embed p0.mark) r.mark hdiag
      have HE:=edgeBudget_nonneg ho hR
      have HP:=add_nonneg (r.tree.forkCost_nonneg hf2) (edgeBudget_nonneg ho hf2)
      have hleafr : (r.tree.leaves:ℝ)+1≤(rBound:ℝ)+3:=by exact_mod_cast (by omega : r.tree.leaves+1≤rBound+3)
      have Hκ:=native_full_scalar_connected_four_abs_le_two r.tree ho U K
        (r.embed (p0.embed a)) (r.embed (p0.embed c)) (r.embed p0.mark) r.mark
      have Hκ' : |(1/2:ℝ)*fullScalarCutConnected4 r.tree U K
          (r.embed (p0.embed a)) (r.embed (p0.embed c)) (r.embed p0.mark) r.mark|≤1:=by
        rw [abs_mul]
        norm_num only [abs_of_nonneg (show (0:ℝ)≤1/2 by norm_num)]
        linarith
      have Hprod:=mul_le_mul_of_nonneg_left HY hAH0
      have Hleaf:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hleafr hAH0) HP
      have Hlow:=mul_le_mul_of_nonneg_left (HS.trans (le_add_of_nonneg_right HE)) hAL
      have Hnonneg : 0≤AH0*(ff (r.tree.splitIndex (r.embed p0.mark) r.mark)*
          (r.tree.forkCost ff+edgeBudget 0 as ff))+AL*R (r.tree.splitIndex (r.embed p0.mark) r.mark):=by
        exact add_nonneg (mul_nonneg hAH0 (mul_nonneg (hff _)
          (add_nonneg (r.tree.forkCost_nonneg hff) (edgeBudget_nonneg ho hff)))) (mul_nonneg hAL (hR _))
      have Hscalar:=mul_le_of_le_one_left Hnonneg Hκ'
      dsimp only [Gr,CH,CL,AH0,AH,AL,R,ff,f2,Mclock] at Hprod Hleaf Hlow Hscalar ⊢
      nlinarith only [Hprod,Hleaf,Hlow,Hscalar]
  have Hsum:=(T.signedPair_abs_le_pairAbsSum F).trans (T.pairAbsSum_mono HF)
  rw [T.pairAbsSum_add,T.pairAbsSum_const_mul AH,T.pairAbsSum_const_mul AL] at Hsum
  have HH:=T.pairAbsSum_forkBudget_le ho hT hf2 (d:=0) (by norm_num)
  have HL:=T.pairAbsSum_forkBudget_le ho hT hR (d:=0) (by norm_num)
  simp only [add_zero] at HH HL
  have HB:=add_le_add (mul_le_mul_of_nonneg_left HH hAH) (mul_le_mul_of_nonneg_left HL hAL)
  apply Hsum.trans
  convert HB using 1
  dsimp only [F,J,AH,AH0,AL,CH,CL,R,f2,q,b,h,K,S,Mclock,as,nativeOriginalHighPairRestoration]
  ring

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem native_canonical_G_projected_displacement_source_original_q
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin a → NativeSourceFactorForm) (s : T.Slot) (star : ℕ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0) (S : ℕ → ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    let GP:=(G.nativeCMarkedLift g (nativeFreshAtSlot_mem T 0 s star)).nativeCMarkedLift p hp
    nativeRestProjectedDisplacementTest T s star
      (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
      (G.canonicalOriginalQSource M forms).restProduct p=
      fun σ=>
        (GP.canonicalOriginalQSource M forms).restProduct σ*
          (deletedOverlap n (joinSpin (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot p.mark),false))
            (joinSpin (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.embed g.mark)),false))-S star)-
        (GP.canonicalOriginalQSource M forms).restProduct σ*
          (deletedOverlap n (joinSpin (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.embed (g.embed s))),false))
            (joinSpin (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.embed g.mark)),false))-S star) := by
  dsimp only
  funext σ
  rw [ActualNaturalBoundaryShape.nativeCMarkedLift_canonical_restProduct_original_q,
    ActualNaturalBoundaryShape.nativeCMarkedLift_canonical_restProduct_original_q]
  unfold nativeRestProjectedDisplacementTest MarkedPlacement.restSpin
  dsimp only
  rw [(nativeFreshAtSlot T 0 s star).restRestrict_at,p.restRestrict_at,p.restRestrict_at]
  ring

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 28000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

theorem eventually_actual_minimum_inherited_canonical_G_projected_restoration_profile_original_q
    (aDegree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Ch Cl Cq : ℝ,0 < Ch ∧ 0 < Cl ∧ 0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(star U : ℕ) (T : ClockTree (Spin n×Bool) as),star < U → U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀s : T.Slot,
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
          let f2:=fun j=>((R j)^(2/p))^2
          let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Ch^(aDegree+1)*
            (W*sourceMonomialScale x W initial)
          let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Cl^(aDegree+1)*
            (W*sourceMonomialScale x W initial)
          let AH:=pairForkVariation (rBound+4)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*((rBound:ℝ)+5)*pairForkVariation (rBound+2)
          let AL:=absJetVariation (rBound+4) 1*CL*(Cq*(1+Ccut)*W)*pairForkVariation (rBound+2)
          |nativeOriginalGProjectedDisplacementRestoration T s star U q b h K S
            (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
            (G.canonicalOriginalQSource M forms).restProduct| ≤
            (4*((rBound:ℝ)+1)+1)*
              (2*AH*(T.forkCost f2+edgeBudget 0 as f2)+2*AL*(T.forkCost R+edgeBudget 0 as R)) := by
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=eventually_actual_minimum_inherited_unbonded_low_G_pair_restoration_original_q
    (D:=D) aDegree dOrder (rBound+2) hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro star U T hs hU hT G forms initial x W hxsx hxW hcut hmass s
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Mclock:=4*Cf+2*Temp
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
  let f2:=fun j=>((R j)^(2/p))^2
  let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Ch^(aDegree+1)*(W*sourceMonomialScale x W initial)
  let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Cl^(aDegree+1)*(W*sourceMonomialScale x W initial)
  let AH:=pairForkVariation (rBound+4)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*((rBound:ℝ)+5)*pairForkVariation (rBound+2)
  let AL:=absJetVariation (rBound+4) 1*CL*(Cq*(1+Ccut)*W)*pairForkVariation (rBound+2)
  let g:=nativeFreshAtSlot T 0 s star
  let A:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
  let P:=(G.canonicalOriginalQSource M forms).restProduct
  let E:=fun p : MarkedPlacement g.tree=>nativeOriginalHighPairRestoration n q U b h K S p.tree
    (nativeRestProjectedDisplacementTest T s star A P p) (p.embed (g.embed s)) p.mark
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 < W:=(M.hxs.trans_le hxsx).trans_le hxW
  have hscale : 0 ≤ sourceMonomialScale x W initial:=by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) hW initial e).le
  have hCH : 0 ≤ CH:=by dsimp [CH];positivity
  have hCL : 0 ≤ CL:=by dsimp [CL];positivity
  have hAH : 0 ≤ AH:=by
    dsimp only [AH]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (pairForkVariation_nonneg _) hCH) (Real.rpow_nonneg (by positivity) _))
      (Real.rpow_nonneg (by positivity) _)) (by positivity)) (pairForkVariation_nonneg _)
  have hAL : 0 ≤ AL:=mul_nonneg (mul_nonneg (mul_nonneg (absJetVariation_nonneg _ _) hCL)
    (by positivity)) (pairForkVariation_nonneg _)
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hf2 j : 0 ≤ f2 j:=sq_nonneg _
  have hRlo j (hj : j < U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hf2lo j (hj : j < U) : f2 j=0:=by dsimp only [f2];rw [hRlo j hj,Real.zero_rpow (by positivity : 2/p ≠ 0)];ring
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    (M.sweep_bf_monotone) (M.sweep_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ) ≤ M.sweepBf v from M.sweep_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ) ≤ M.sweepHf v from M.sweep_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf (M.sweep_bf_monotone) (M.sweep_hf_monotone)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HE (p0 : MarkedPlacement g.tree) (hp0 : p0∈g.tree.markedAttach 0) :
      |E p0| ≤ 2*AH*(p0.tree.forkCost f2+edgeBudget 0 as f2)+2*AL*(p0.tree.forkCost R+edgeBudget 0 as R) := by
    by_cases hhigh : U ≤ p0.tree.splitIndex (p0.embed (g.embed s)) p0.mark
    · let GP:=(G.nativeCMarkedLift g (nativeFreshAtSlot_mem T 0 s star)).nativeCMarkedLift p0 hp0
      have hGP e : GP.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e:=by
        simpa only [GP,ActualNaturalBoundaryShape.nativeCMarkedLift_sourceLowMass] using hmass e
      have hleaf : p0.tree.leaves ≤ rBound+2:=by
        have H1:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 s star)
        have H2:=g.tree.markedAttach_leaves 0 p0 hp0
        omega
      have Hsplits:=native_fresh_observed_endpoint_splits T s hs hU p0 hp0 hhigh
      have hsplit1 : p0.tree.splitIndex (p0.embed g.mark) p0.mark=star:=Hsplits.1
      have hsplit2 : p0.tree.splitIndex (p0.embed g.mark) (p0.embed (g.embed s))=star:=Hsplits.2
      have hsplit1' : p0.tree.splitIndex p0.mark (p0.embed g.mark)=star:=by
        rw [p0.tree.splitIndex_symm,hsplit1]
      have hsplit2' : p0.tree.splitIndex (p0.embed (g.embed s)) (p0.embed g.mark)=star:=by
        rw [p0.tree.splitIndex_symm,hsplit2]
      have hdistinct1 : p0.mark≠p0.embed g.mark:=by
        intro Hsame
        have HH:=Hsplits.1
        rw [←Hsame,p0.tree.splitIndex_self] at HH
        omega
      have hdistinct2 : p0.embed (g.embed s)≠p0.embed g.mark:=by
        intro Hsame
        have HH:=Hsplits.2
        rw [Hsame,p0.tree.splitIndex_self] at HH
        omega
      let J1:=fun σ : p0.tree.cavityLeft.Assignment=>(GP.canonicalOriginalQSource M forms).restProduct σ*
        (A (p0.tree.cavityLeft.atSlot σ (p0.tree.cavityLeftSlot p0.mark))
          (p0.tree.cavityLeft.atSlot σ (p0.tree.cavityLeftSlot (p0.embed g.mark)))-S star)
      let J2:=fun σ : p0.tree.cavityLeft.Assignment=>(GP.canonicalOriginalQSource M forms).restProduct σ*
        (A (p0.tree.cavityLeft.atSlot σ (p0.tree.cavityLeftSlot (p0.embed (g.embed s))))
          (p0.tree.cavityLeft.atSlot σ (p0.tree.cavityLeftSlot (p0.embed g.mark)))-S star)
      have H1:=hgrid U p0.tree hU hleaf GP forms initial x W hxsx hxW hcut hGP
        p0.mark (p0.embed g.mark) (p0.embed (g.embed s)) p0.mark hdistinct1
        (by rw [hsplit1'];exact hs)
      have H2:=hgrid U p0.tree hU hleaf GP forms initial x W hxsx hxW hcut hGP
        (p0.embed (g.embed s)) (p0.embed g.mark) (p0.embed (g.embed s)) p0.mark hdistinct2
        (by rw [hsplit2'];exact hs)
      have Hsource:=native_canonical_G_projected_displacement_source_original_q G M forms s star p0 hp0 S
      change nativeRestProjectedDisplacementTest T s star A P p0=(fun σ=>J1 σ-J2 σ) at Hsource
      have HL:=native_original_high_pair_restoration_test_linear n q U b h K S p0.tree ho
        J1 J2 (p0.embed (g.embed s)) p0.mark 1 (-1)
        (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
        (fun i=>by cases i <;> first | exact hbm | exact hhm)
        (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm
      dsimp only [E]
      rw [Hsource]
      have HL' : nativeOriginalHighPairRestoration n q U b h K S p0.tree (fun σ=>J1 σ-J2 σ)
          (p0.embed (g.embed s)) p0.mark=
          nativeOriginalHighPairRestoration n q U b h K S p0.tree J1 (p0.embed (g.embed s)) p0.mark-
          nativeOriginalHighPairRestoration n q U b h K S p0.tree J2 (p0.embed (g.embed s)) p0.mark:=by
        simpa only [one_mul,neg_one_mul,←sub_eq_add_neg] using HL
      rw [HL',sub_eq_add_neg]
      apply (abs_add_le _ _).trans
      rw [abs_neg]
      have H1' : |nativeOriginalHighPairRestoration n q U b h K S p0.tree J1 (p0.embed (g.embed s)) p0.mark| ≤
          AH*(p0.tree.forkCost f2+edgeBudget 0 as f2)+AL*(p0.tree.forkCost R+edgeBudget 0 as R):=by
        convert H1 using 1 <;> dsimp only [J1,A,CH,CL,AH,AL,Mclock,R,f2] <;>
          (try simp only [hsplit1']) <;> push_cast <;> ring
      have H2' : |nativeOriginalHighPairRestoration n q U b h K S p0.tree J2 (p0.embed (g.embed s)) p0.mark| ≤
          AH*(p0.tree.forkCost f2+edgeBudget 0 as f2)+AL*(p0.tree.forkCost R+edgeBudget 0 as R):=by
        convert H2 using 1 <;> dsimp only [J2,A,CH,CL,AH,AL,Mclock,R,f2] <;>
          (try simp only [hsplit2']) <;> push_cast <;> ring
      exact (add_le_add H1' H2').trans_eq (by ring)
    · dsimp only [E]
      rw [native_original_high_pair_restoration_cross_zero n q U b h K S p0.tree ho
        _ (p0.embed (g.embed s)) p0.mark (lt_of_not_ge hhigh)
        (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
        (fun i=>by cases i <;> first | exact hbm | exact hhm)
        (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm,abs_zero]
      exact add_nonneg (mul_nonneg (by positivity) (add_nonneg (p0.tree.forkCost_nonneg hf2) (edgeBudget_nonneg ho hf2)))
        (mul_nonneg (by positivity) (add_nonneg (p0.tree.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
  exact native_current_restoring_rows_two_profiles_le T ho s hs hT f2 R hf2 hR hf2lo hRlo E
    (by positivity) (by positivity) HE

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem eventually_actual_minimum_inherited_resource_G_restoration_profile_original_q
    (aDegree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k degree : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → P.live.factors.length=aDegree →
        seed.length+k ≤ degree →
        ∀(A x W ε : ℝ),1 ≤ A → M.xs ≤ x → x ≤ W → 0 < ε → ε ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        P.PairMomentBudget (fullWeight n) (fullFeature n) 0
          (finitePhysicalCavitySquareVariance n U as
            (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ))
            (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)) 1 1)
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) 0 A x W ε →
        let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
        let f2:=fun j=>((R j)^(2/p))^2
        |(W⁻¹)^k*nativeActualResourceGaRestoration_original_q M U P| ≤
          |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*
            (C*W*(T.forkCost f2+edgeBudget 0 as f2+
              W*(T.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,Hsource⟩:=
    eventually_actual_minimum_inherited_canonical_G_projected_restoration_profile_original_q
      (D:=D) aDegree dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
      hm hdelta hroom hcl hcu hAz hC0 hCt
  let Mclock:=4*Cf+2*Temp
  let KH:=(4*((rBound:ℝ)+1)+1)*2*pairForkVariation (rBound+4)*
    (Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Ch^(aDegree+1))*
    (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*((rBound:ℝ)+5)*pairForkVariation (rBound+2)
  let KL:=(4*((rBound:ℝ)+1)+1)*2*absJetVariation (rBound+4) 1*
    (Real.exp (wholeLawRowComparisonConstant (rBound+4)*Mclock)*Cl^(aDegree+1))*
    (Cq*(1+Ccut))*pairForkVariation (rBound+2)
  have hpv1:=pairForkVariation_nonneg (rBound+4)
  have hpv2:=pairForkVariation_nonneg (rBound+2)
  have hav:=absJetVariation_nonneg (rBound+4) 1
  have hrp : 0 ≤ (2*Temp)^((p-2)/p):=Real.rpow_nonneg (by positivity) _
  have hKH : 0 ≤ KH:=by dsimp only [KH];positivity
  have hKL : 0 ≤ KL:=by dsimp only [KL];positivity
  let C:=KH+KL+1
  have hC : 0 < C:=by dsimp only [C];linarith
  refine ⟨C,hC,?_⟩
  filter_upwards [Hsource] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro i star U k degree seed T P hP hi hs hU hT hlen hdepth A x W ε hA hx hxW hε hε1 hmi hms hcut Hpair
  let as:=finiteCutMasses us jGrid
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hstar : star < as.length:=hs.trans_le hU
  let G:=nativeActualResourceCanonicalShape P.live hi hstar
  let I:=nativeActualResourceInitialFactors P.live
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
  let f2:=fun j=>((R j)^(2/p))^2
  let F2:=T.forkCost f2+edgeBudget 0 as f2
  let F1:=T.forkCost R+edgeBudget 0 as R
  have hW : 0 ≤ W:=((M.hxs.trans_le hx).trans_le hxW).le
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg Mclock hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hF2 : 0 ≤ F2:=add_nonneg (T.forkCost_nonneg (fun j=>sq_nonneg _))
    (edgeBudget_nonneg ho (fun j=>sq_nonneg _))
  have hF1 : 0 ≤ F1:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hscale : 0 ≤ nativeResourceScale x W 1 P.live.tags:=
    (actual_resource_raw_scale_pos _ (M.hxs.trans_le hx) ((M.hxs.trans_le hx).trans_le hxW)).le
  have Hmass e : G.sourceLowMass e ≤ Cmass*sourceFactorScale x W I e:=
    native_actual_resource_canonical_source_mass P.live hi hstar Cmass x W hmi hms e
  have Hlive : |nativeActualGProjectedRestoration_original_q T P.live.test star U M
      (fun j=>Sum.elim (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ))
        (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ)))| ≤
      nativeResourceScale x W 1 P.live.tags*(W*(KH*F2+KL*(W*F1))) := by
    have Hgrid:=hgrid
    rw [←hlen] at Hgrid
    have H:=Hgrid star U T hs hU hT G (fun _=>NativeSourceFactorForm.centered) I x W hx hxW
      hcut Hmass P.live.test.target
    rw [native_actual_resource_live_scale_eq_annotations] at H
    have HCh : Ch^(P.live.factors.length+1)=Ch^(aDegree+1):=by rw [hlen]
    have HCl : Cl^(P.live.factors.length+1)=Cl^(aDegree+1):=by rw [hlen]
    simp only [HCh,HCl] at H
    rw [native_actual_resource_G_restoration_eq_canonical_source_original_q hP hi hs ho M]
    convert H using 1
    dsimp only [G,R,f2,F1,F2,KH,KL,Mclock,as]
    ring
  have Hmajor : KH*F2+KL*(W*F1) ≤ C*(F2+W*F1):=by
    have H1:=mul_nonneg (show 0 ≤ C-KH by dsimp only [C];linarith) hF2
    have H2:=mul_nonneg (show 0 ≤ C-KL by dsimp only [C];linarith) (mul_nonneg hW hF1)
    nlinarith
  have Hlive':=Hlive.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left Hmajor hW) hscale)
  have Hprice : 0 ≤ C*W*(F2+W*F1):=by positivity
  apply actual_resource_Ga_restoration_normalized_profile_le_original_q M hP hdepth ho hi hstar
    hA hx hxW hε hε1 Hprice Hpair
  apply Hlive'.trans_eq
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem eventually_actual_minimum_inherited_bounded_resource_G_restoration_profile_original_q
    (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound →
        seed.length+k ≤ degree →
        ∀(A x W ε : ℝ),1 ≤ A → M.xs ≤ x → x ≤ W → 0 < ε → ε ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        P.PairMomentBudget (fullWeight n) (fullFeature n) 0
          (finitePhysicalCavitySquareVariance n U as
            (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ))
            (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)) 1 1)
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) 0 A x W ε →
        let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
        let f2:=fun j=>((R j)^(2/p))^2
        |(W⁻¹)^k*nativeActualResourceGaRestoration_original_q M U P| ≤
          |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*
            (C*W*(T.forkCost f2+edgeBudget 0 as f2+
              W*(T.forkCost R+edgeBudget 0 as R))) := by
  classical
  have HP (a : Fin (degree+1)) :=
    eventually_actual_minimum_inherited_resource_G_restoration_profile_original_q
      (D:=D) a.val dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
      hm hdelta hroom hcl hcu hAz hC0 hCt
  choose C hC HC using HP
  let Cmax:=1+∑a : Fin (degree+1),C a
  have hsum : 0 ≤ ∑a : Fin (degree+1),C a:=Finset.sum_nonneg (fun a _=>(hC a).le)
  have hCmax : 0 < Cmax:=by dsimp only [Cmax];linarith
  have hdom a : C a ≤ Cmax:=by
    have H:=Finset.single_le_sum (fun a _=>(hC a).le) (Finset.mem_univ a)
    dsimp only [Cmax]
    linarith
  refine ⟨Cmax,hCmax,?_⟩
  filter_upwards [Filter.eventually_all.mpr HC] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  have Hgrids a:=hn a M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr Hgrids] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth A x W ε hA hx hxW hε hε1 hmi hms hcut Hpair
  have Hlive : P.live.factors.length ≤ degree:=by
    have Hlen:=hP.total_factor_depth
    simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,
      List.length_map] at Hlen
    omega
  let a : Fin (degree+1):=⟨P.live.factors.length,by omega⟩
  have H:=hj a i star U k degree seed T P hP hi hs hU hT rfl hdepth
    A x W ε hA hx hxW hε hε1 hmi hms hcut Hpair
  have hx0:=M.hxs.trans_le hx
  have hW:=hx0.trans_le hxW
  let as:=finiteCutMasses us jGrid
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
  let f2:=fun j=>((R j)^(2/p))^2
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hF2 : 0 ≤ T.forkCost f2+edgeBudget 0 as f2:=
    add_nonneg (T.forkCost_nonneg (fun j=>sq_nonneg _)) (edgeBudget_nonneg ho (fun j=>sq_nonneg _))
  have hF1 : 0 ≤ T.forkCost R+edgeBudget 0 as R:=
    add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hseed:=actual_resource_raw_scale_pos seed hx0 hW
  have HD:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hdom a) hW.le)
    (show 0 ≤ T.forkCost f2+edgeBudget 0 as f2+W*(T.forkCost R+edgeBudget 0 as R) by positivity))
    (show 0 ≤ |P.coefficient| *A^degree*nativeResourceScale x W 1 seed by positivity)
  exact H.trans HD

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem eventually_actual_minimum_inherited_resource_G_restoration_from_minimum_original_q
    (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound →
        seed.length+k ≤ degree →
        ∀x W : ℝ,M.xs ≤ x → x ≤ W →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
        let f2:=fun j=>((R j)^(2/p))^2
        |(W⁻¹)^k*nativeActualResourceGaRestoration_original_q M U P| ≤
          |P.coefficient| *nativeResourceScale x W 1 seed*
            (C*W*(T.forkCost f2+edgeBudget 0 as f2+
              W*(T.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_bounded_resource_G_restoration_profile_original_q
    (D:=D) degree dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget_original_q
    (D:=D) (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  refine ⟨C*A^degree,by positivity,?_⟩
  filter_upwards [HC,HA] with n hnC hnA
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnC M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnA M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hjC hjA
  dsimp only at hjC hjA ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth x W hx hxW hmi hms hcut
  have Hdegree : P.resources.length ≤ degree+1:=by rw [hP.total_factor_depth];omega
  have HP:=hjA U i star T P Hdegree (hi.trans (hs.le.trans hU)) (hs.le.trans hU)
    x W hx hxW hmi hms 1 1 (by norm_num) (by norm_num)
  have H:=hjC i star U k seed T P hP hi hs hU hT hdepth A x W 1 hA hx hxW
    zero_lt_one le_rfl hmi hms hcut HP
  apply H.trans_eq
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem eventually_actual_minimum_inherited_bounded_resource_HIGH_parts_profile_original_q
    (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound →
        seed.length+k ≤ degree →
        ∀(A x W : ℝ),1 ≤ A → M.xs ≤ x → x ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        P.PairMomentBudget (fullWeight n) (fullFeature n) 0
          (finitePhysicalCavitySquareVariance n U as
            (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ))
            (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)) 1 1)
          (fun σ τ=>deletedOverlap n (joinSpin σ) (joinSpin τ))
          (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) 0 A x W 1 →
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
        let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
        |(W⁻¹)^k*nativeActualResourceHigherHighPart_original_q M U P part a z l t| ≤
          |P.coefficient| *A^degree*nativeResourceScale x W 1 seed*
            (C*W*(T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
              W*(T.forkCost R+edgeBudget 0 as R))) := by
  classical
  have HP (a : Fin (degree+1)) :=
    eventually_actual_minimum_inherited_resource_HIGH_parts_profile_original_q
      (D:=D) a.val dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
      hm hdelta hroom hcl hcu hAz hC0 hCt
  choose C hC HC using HP
  let Cmax:=1+∑a : Fin (degree+1),C a
  have hsum : 0 ≤ ∑a : Fin (degree+1),C a:=Finset.sum_nonneg (fun a _=>(hC a).le)
  have hCmax : 0 < Cmax:=by dsimp only [Cmax];linarith
  have hdom a : C a ≤ Cmax:=by
    have H:=Finset.single_le_sum (fun a _=>(hC a).le) (Finset.mem_univ a)
    dsimp only [Cmax]
    linarith
  refine ⟨Cmax,hCmax,?_⟩
  filter_upwards [Filter.eventually_all.mpr HC] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  have Hgrids a:=hn a M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr Hgrids] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth A x W hA hx hxW hW1 hmi hms hcut Hpair aSlot z l t hl ht part
  have Hlive : P.live.factors.length ≤ degree:=by
    have Hlen:=hP.total_factor_depth
    simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,
      List.length_map] at Hlen
    omega
  let a : Fin (degree+1):=⟨P.live.factors.length,by omega⟩
  have H:=hj a i star U k degree seed T P hP hi hs hU hT rfl hdepth
    A x W hA hx hxW hW1 hmi hms hcut Hpair aSlot z l t hl ht part
  have hx0:=M.hxs.trans_le hx
  have hW:=hx0.trans_le hxW
  let as:=finiteCutMasses us jGrid
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
  let f2:=fun j=>(R j)^(4/p)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hF2 : 0 ≤ T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)):=
    add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
      (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
  have hF1 : 0 ≤ T.forkCost R+edgeBudget 0 as R:=
    add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hseed:=actual_resource_raw_scale_pos seed hx0 hW
  have HD:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hdom a) hW.le)
    (show 0 ≤ T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+W*(T.forkCost R+edgeBudget 0 as R) by positivity))
    (show 0 ≤ |P.coefficient| *A^degree*nativeResourceScale x W 1 seed by positivity)
  exact H.trans HD

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem eventually_actual_minimum_inherited_resource_HIGH_parts_from_minimum_original_q
    (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound →
        seed.length+k ≤ degree →
        ∀x W : ℝ,M.xs ≤ x → x ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
        let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
        |(W⁻¹)^k*nativeActualResourceHigherHighPart_original_q M U P part a z l t| ≤
          |P.coefficient| *nativeResourceScale x W 1 seed*
            (C*W*(T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
              W*(T.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_bounded_resource_HIGH_parts_profile_original_q
    (D:=D) degree dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget_original_q
    (D:=D) (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  refine ⟨C*A^degree,by positivity,?_⟩
  filter_upwards [HC,HA] with n hnC hnA
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnC M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnA M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hjC hjA
  dsimp only at hjC hjA ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth x W hx hxW hW1 hmi hms hcut a z l t hl ht part
  have Hdegree : P.resources.length ≤ degree+1:=by rw [hP.total_factor_depth];omega
  have HP:=hjA U i star T P Hdegree (hi.trans (hs.le.trans hU)) (hs.le.trans hU)
    x W hx hxW hmi hms 1 1 (by norm_num) (by norm_num)
  have H:=hjC i star U k seed T P hP hi hs hU hT hdepth A x W hA hx hxW hW1 hmi hms hcut HP a z l t hl ht part
  apply H.trans_eq
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem eventually_actual_minimum_inherited_centered_resource_HIGH_parts_from_minimum_original_q
    (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound →
        seed.length+k ≤ degree →
        ∀x W : ℝ,M.xs ≤ x → x ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
        let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
        |(W⁻¹)^k*nativeActualOriginalCenteredResourceHigherHighPart_original_q M U P part a z l t| ≤
          |P.coefficient| *nativeResourceScale x W 1 seed*
            (C*W*(T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
              W*(T.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_resource_HIGH_parts_from_minimum_original_q
    (D:=D) degree dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth x W hx hxW hW1 hmi hms hcut a z l t hl ht part
  have ho:=finiteCutMasses_ordered us hus jGrid
  rw [native_actual_original_centered_resource_HIGH_part_eq_two_resources_original_q M U P ho part a z l t,mul_add]
  have HP:=hj i star U k seed T P hP hi hs hU hT hdepth x W hx hxW hW1 hmi hms hcut a z l t hl ht part
  have HF:=hj i star U k seed T P.freeze hP.freeze hi hs hU hT hdepth x W hx hxW hW1 hmi hms hcut a z l t hl ht part
  simp only [NativeResourceTerm.freeze,abs_neg] at HF
  apply ((abs_add_le _ _).trans (add_le_add HP HF)).trans_eq
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem eventually_actual_minimum_inherited_fresh_resource_HIGH_parts_from_minimum_original_q
    (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound →
        seed.length+k ≤ degree →
        ∀x W : ℝ,M.xs ≤ x → x ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀(l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀part : Fin 3,
        let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
        |(W⁻¹)^k*nativeActualOriginalFreshResourceHigherHighPart_original_q M U P part l t| ≤
          |P.coefficient| *nativeResourceScale x W 1 seed*
            (C*W*(T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
              W*(T.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_centered_resource_HIGH_parts_from_minimum_original_q
    (D:=D) degree dOrder (rBound+1) hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth x W hx hxW hW1 hmi hms hcut l t hl ht part
  let as:=finiteCutMasses us jGrid
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
  let f:=fun j=>(R j)^(4/p)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves ≤ rBound+1:=by
    have HH:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 P.live.test.target star)
    omega
  have H0:=hj i star U k seed g.tree (P.retarget 0) hP.retarget hi hs hU hg hdepth
    x W hx hxW hW1 hmi hms hcut (g.embed P.live.test.target) g.mark l t hl ht part
  have hlo j (hj : j<U) : R j=0:=by
    simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hflo j (hj : j<U) : f j=0:=by
    dsimp only [f]
    rw [hlo j hj,Real.zero_rpow (by positivity : 4/p≠0)]
  have Hf:=nativeFreshAtSlot_high_forkCost T 0 P.live.test.target hs f hflo
  have HR:=nativeFreshAtSlot_high_forkCost T 0 P.live.test.target hs R hlo
  rw [native_actual_original_fresh_resource_HIGH_part_eq_centered_retarget_original_q M U P ho]
  change |(W⁻¹)^k*nativeActualOriginalCenteredResourceHigherHighPart_original_q M U (P.retarget 0) part
    (g.embed P.live.test.target) g.mark l t| ≤ |P.coefficient| *nativeResourceScale x W 1 seed*
      (C*W*(T.forkCost f+edgeBudget 0 as f+W*(T.forkCost R+edgeBudget 0 as R)))
  change |(W⁻¹)^k*nativeActualOriginalCenteredResourceHigherHighPart_original_q M U (P.retarget 0) part
    (g.embed P.live.test.target) g.mark l t| ≤ |P.coefficient| *nativeResourceScale x W 1 seed*
      (C*W*(g.tree.forkCost f+edgeBudget 0 as f+W*(g.tree.forkCost R+edgeBudget 0 as R))) at H0
  simpa only [show g.tree.forkCost f=T.forkCost f from Hf,
    show g.tree.forkCost R=T.forkCost R from HR] using H0

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_minimum_inherited_canonical_joint_HIGH_restoration_price_original_q
    (kind : NativeJointHighRestorationKind) (aDegree dOrder rBound : ℕ)
    (hd : 0 < dOrder) (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (W : ℝ),M.xs ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
        ∀a z : T.Slot,T.splitIndex a z<U →
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
          |nativeJointHighRestorationSource kind n q U b h K S T
            (G.canonicalOriginalQSource M forms).restProduct a z| ≤
            C*W*sourceMonomialScale M.xs W initial*
              (T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
                W*(T.forkCost R+edgeBudget 0 as R)) := by
  cases kind with
  | lowTwoHigh=>
    let Cgeom:=max Cmass Ccut
    have hCgeom : 0 ≤ Cgeom:=hCmass.trans (le_max_left _ _)
    obtain ⟨Cp,hCp,H⟩:=eventually_actual_minimum_inherited_canonical_C_two_high_profile_budget_original_q
      (D:=D) aDegree dOrder rBound hd p hp hOrder Bclock Temp Cf Cgeom hTemp hCf hCgeom
      hm hdelta hroom hcl hcu hAz hC0 hCt
    let base:=pairForkVariation (rBound+2)*pairForkVariation (rBound+4)*
      (Real.exp (wholeLawRowComparisonConstant (rBound+2)*(4*Cf+2*Temp))*Cp^(aDegree+1))*
      (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*pairForkVariation rBound
    have hbase : 0 ≤ base:=by
      have HV0:=pairForkVariation_nonneg (rBound+2)
      have HV1:=pairForkVariation_nonneg (rBound+4)
      have HV2:=pairForkVariation_nonneg rBound
      have HP:=Real.rpow_nonneg (show 0 ≤ 2*Temp by positivity) ((p-2)/p)
      dsimp only [base]
      positivity
    refine ⟨base+1,by positivity,?_⟩
    filter_upwards [H] with n hn
    intro M hs0 hsxs hsource hxs L us hus hret hmesh
    filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro U T hU hT G forms initial W hxW hcut hmass a z haz
    have hW : 0 ≤ W:=M.hxs.le.trans hxW
    have hmass' e : G.sourceLowMass e ≤ Cgeom*sourceFactorScale M.xs W initial e:=
      (hmass e).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le)
    have hcut' : partitionPoint 0 (finiteCutMasses us jGrid) U ≤ Cgeom*W:=
      hcut.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hW)
    have Hraw:=hj U T hU hT G forms initial W hxW hcut' hmass' a z haz
    let as:=finiteCutMasses us jGrid
    let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
    let Z:=sourceMonomialScale M.xs W initial
    let A:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))
    let B:=T.forkCost R+edgeBudget 0 as R
    have ho:=finiteCutMasses_ordered us hus jGrid
    have hR j : 0 ≤ R j:=by
      dsimp only [R,nativeOriginalHighErrorEnvelope]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) (by
          dsimp only [nativeOriginalCutLowErrorRadius]
          positivity)
    have hA : 0 ≤ A:=add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
      (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
    have hB : 0 ≤ B:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
    have hZ : 0 ≤ Z:=by
      rw [show Z=∏e,sourceFactorScale M.xs W initial e from (source_factor_scale_product _ _ _).symm]
      exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le
    have Hmajor:=mul_le_mul_of_nonneg_right (show base ≤ base+1 by linarith)
      (show 0 ≤ W*Z*A by positivity)
    have Hprice : base*W*Z*A ≤ (base+1)*W*Z*(A+W*B):=by
      have Hplus : 0 ≤ (base+1)*W*Z*(W*B):=by positivity
      nlinarith only [Hmajor,Hplus]
    apply Hraw.trans
    convert Hprice using 1
    dsimp only [base,R,Z,A,B,as,nativeJointHighRestorationSource]
    ring
  | fourGLow=>
    obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=eventually_actual_minimum_inherited_canonical_four_G_low_restoration_original_q
      (D:=D) aDegree dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
      hm hdelta hroom hcl hcu hAz hC0 hCt
    let bh:=2*pairForkVariation (rBound+4)*
      (Real.exp (wholeLawRowComparisonConstant (rBound+4)*(4*Cf+2*Temp))*Ch^(aDegree+1))*
      (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*((rBound:ℝ)+5)*pairForkVariation (rBound+2)*pairForkVariation rBound
    let bl:=2*absJetVariation (rBound+4) 1*
      (Real.exp (wholeLawRowComparisonConstant (rBound+4)*(4*Cf+2*Temp))*Cl^(aDegree+1))*
      (Cq*(1+Ccut))*pairForkVariation (rBound+2)*pairForkVariation rBound
    have hbh : 0 ≤ bh:=by
      have HV0:=pairForkVariation_nonneg (rBound+4)
      have HV1:=pairForkVariation_nonneg (rBound+2)
      have HV2:=pairForkVariation_nonneg rBound
      have HP:=Real.rpow_nonneg (show 0 ≤ 2*Temp by positivity) ((p-2)/p)
      dsimp only [bh]
      positivity
    have hbl : 0 ≤ bl:=by
      have HV0:=absJetVariation_nonneg (rBound+4) 1
      have HV1:=pairForkVariation_nonneg (rBound+2)
      have HV2:=pairForkVariation_nonneg rBound
      dsimp only [bl]
      positivity
    refine ⟨bh+bl+1,by positivity,?_⟩
    filter_upwards [H] with n hn
    intro M hs0 hsxs hsource hxs L us hus hret hmesh
    filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro U T hU hT G forms initial W hxW hcut hmass a z _haz
    have Hraw:=hj U T hU hT G forms initial W hxW hcut hmass a z
    let as:=finiteCutMasses us jGrid
    let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
    let Z:=sourceMonomialScale M.xs W initial
    let A:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))
    let B:=T.forkCost R+edgeBudget 0 as R
    have ho:=finiteCutMasses_ordered us hus jGrid
    have hW : 0 ≤ W:=M.hxs.le.trans hxW
    have hR j : 0 ≤ R j:=by
      dsimp only [R,nativeOriginalHighErrorEnvelope]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) (by
          dsimp only [nativeOriginalCutLowErrorRadius]
          positivity)
    have Hpow : (fun j=>((R j)^(2/p))^2)=(fun j=>(R j)^(4/p)):=by
      funext j
      rw [wholeLaw_rpow_square_eq (hR j) (2/p)]
      congr 1
      ring
    change |nativeJointHighRestorationSource .fourGLow n _ U _ _ _ _ T _ a z| ≤ _ at Hraw
    rw [Hpow] at Hraw
    have hA : 0 ≤ A:=add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
      (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
    have hB : 0 ≤ B:=add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
    have hZ : 0 ≤ Z:=by
      rw [show Z=∏e,sourceFactorScale M.xs W initial e from (source_factor_scale_product _ _ _).symm]
      exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le
    have Hmajor:=add_le_add
      (mul_le_mul_of_nonneg_right (show bh ≤ bh+bl+1 by linarith) (show 0 ≤ W*Z*A by positivity))
      (mul_le_mul_of_nonneg_right (show bl ≤ bh+bl+1 by linarith) (show 0 ≤ W^2*Z*B by positivity))
    apply Hraw.trans
    convert Hmajor using 1 <;> (try dsimp only [bh,bl,R,Z,A,B,as]) <;> ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_minimum_inherited_resource_joint_HIGH_restoration_from_minimum_original_q
    (kind : NativeJointHighRestorationKind) (degree dOrder rBound : ℕ)
    (hd : 0 < dOrder) (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ)) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        ∀W : ℝ,M.xs ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀a z : T.Slot,T.splitIndex a z<U →
        let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
        let cost:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
          W*(T.forkCost R+edgeBudget 0 as R)
        |(W⁻¹)^k*nativeActualResourceJointHighRestoration_original_q kind M U P a z| ≤
          |P.coefficient| *nativeResourceScale M.xs W 1 seed*(C*W*cost) := by
  classical
  have HP (a : Fin (degree+1)):=eventually_actual_minimum_inherited_canonical_joint_HIGH_restoration_price_original_q
    (D:=D) kind a.val dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  choose C hC HC using HP
  let Cmax:=1+∑a : Fin (degree+1),C a
  have hsum : 0 ≤ ∑a : Fin (degree+1),C a:=Finset.sum_nonneg (fun a _=>(hC a).le)
  have hCmax : 0 < Cmax:=by dsimp only [Cmax];linarith
  have hdom a : C a ≤ Cmax:=by
    have H:=Finset.single_le_sum (fun a _=>(hC a).le) (Finset.mem_univ a)
    dsimp only [Cmax]
    linarith
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget_original_q
    (D:=D) (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  refine ⟨Cmax*A^degree,by positivity,?_⟩
  filter_upwards [Filter.eventually_all.mpr HC,HA] with n hn hnA
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  have Hgrids a:=hn a M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr Hgrids,hnA M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj hjA
  dsimp only at hj hjA ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth W hxW hW1 hmi hms hcut aSlot z haz
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
  let cost:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
    W*(T.forkCost R+edgeBudget 0 as R)
  let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hU)
  let I:=nativeActualResourceInitialFactors P.live
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp) (by
        dsimp only [nativeOriginalCutLowErrorRadius]
        positivity)
  have hcost : 0 ≤ cost:=add_nonneg
    (add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
      (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _)))
    (mul_nonneg (M.hxs.le.trans hxW) (add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)))
  have hW : 0 < W:=M.hxs.trans_le hxW
  have hprice : 0 ≤ Cmax*W*cost:=by positivity
  have Hdegree : P.resources.length ≤ degree+1:=by rw [hP.total_factor_depth];omega
  have Hpair:=hjA U i star T P Hdegree (hi.trans (hs.le.trans hU)) (hs.le.trans hU)
    M.xs W le_rfl hxW hmi hms 1 1 (by norm_num) (by norm_num)
  have Hlive : P.live.factors.length ≤ degree:=by
    have Hlen:=hP.total_factor_depth
    simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,List.length_map] at Hlen
    omega
  let a : Fin (degree+1):=⟨P.live.factors.length,by omega⟩
  have HL:=hj a U T hU hT G (fun _=>.centered) I W hxW hcut
    (native_actual_resource_canonical_source_mass P.live hi (hs.trans_le hU) Cmass M.xs W hmi hms) aSlot z haz
  rw [native_actual_resource_live_scale_eq_annotations] at HL
  have Hcenter : nativePhysicalResourceCenter n M.sweepBf M.sweepHf as=
      (fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)):=by
    funext j
    exact (native_ordered_source_center_eq_completed n M.sweepBf M.sweepHf
      M.inherited_bf_monotone M.inherited_hf_monotone (partitionPoint_mem as ho j)).symm
  rw [←Hcenter] at HL
  have HL' : |nativeJointHighRestorationSource kind n q U b h K (nativePhysicalResourceCenter n M.sweepBf M.sweepHf as) T
      (G.canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)).restProduct aSlot z| ≤
      nativeResourceScale M.xs W 1 P.live.tags*(Cmax*W*cost):=by
    apply HL.trans
    have Hdom:=mul_le_mul_of_nonneg_left (hdom a)
      (show 0 ≤ W*nativeResourceScale M.xs W 1 P.live.tags*cost by
        exact mul_nonneg (mul_nonneg (M.hxs.le.trans hxW) (actual_resource_raw_scale_pos _ M.hxs (M.hxs.trans_le hxW)).le) hcost)
    convert Hdom using 1 <;> ring
  have H:=actual_resource_joint_HIGH_normalized_price_le_original_q kind M hP hdepth ho hi (hs.trans_le hU)
    aSlot z hA le_rfl hxW hprice Hpair HL'
  apply H.trans_eq
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem eventually_actual_minimum_inherited_centered_resource_joint_HIGH_restoration_from_minimum_original_q
    (kind : NativeJointHighRestorationKind) (degree dOrder rBound : ℕ)
    (hd : 0 < dOrder) (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ)) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        ∀W : ℝ,M.xs ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀a z : T.Slot,T.splitIndex a z<U →
        let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
        let cost:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
          W*(T.forkCost R+edgeBudget 0 as R)
        |(W⁻¹)^k*nativeActualOriginalCenteredResourceJointHighRestoration_original_q kind M U P a z| ≤
          |P.coefficient| *nativeResourceScale M.xs W 1 seed*(C*W*cost) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_resource_joint_HIGH_restoration_from_minimum_original_q
    (D:=D) kind degree dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth W hxW hW1 hmi hms hcut a z haz
  have ho:=finiteCutMasses_ordered us hus jGrid
  rw [native_actual_original_centered_resource_joint_HIGH_restoration_eq_two_resources_original_q kind M U P ho a z,mul_add]
  have HP:=hj i star U k seed T P hP hi hs hU hT hdepth W hxW hW1 hmi hms hcut a z haz
  have HF:=hj i star U k seed T P.freeze hP.freeze hi hs hU hT hdepth W hxW hW1 hmi hms hcut a z haz
  simp only [NativeResourceTerm.freeze,abs_neg] at HF
  apply ((abs_add_le _ _).trans (add_le_add HP HF)).trans_eq
  ring

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_longitudinal_restoration_original_budget_original_q
    (aDegree dOrder rBound : ℕ) (ha : 0 < aDegree) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Ch Cl Cq : ℝ,0 < Ch ∧ 0 < Cl ∧ 0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          partitionPoint 0 as U ≤ Ccut*W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀a : T.Slot,
          |nativeOriginalLongitudinalRestoration n q U b h K S T
            (G.canonicalOriginalQSource M forms).product a| ≤
            ((nativeOriginalGMarkedWords T).map (fun g=>|g.coefficient| *
              nativeOriginalGWordRestorationCost g U (rBound+3) M.sweepBf M.sweepHf K a Mclock Temp p
                (Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Ch^aDegree*
                  sourceMonomialScale x W initial)
                (Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Cl^aDegree*
                  sourceMonomialScale x W initial) (Cq*W))).sum := by
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=
    eventually_actual_minimum_inherited_canonical_G_word_restoration_original_budget_original_q
      (D:=D) aDegree dOrder rBound ha hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
      hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT G forms initial x W hxsx hxW hcut hmass a
  rw [native_original_longitudinal_restoration_eq_words]
  exact native_original_G_word_weighted_sum_abs_le T _ _
    (fun g _=>hgrid U T hU hT G forms initial x W hxsx hxW hcut hmass g a)

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_longitudinal_restoration_profile_budget_original_q
    (aDegree dOrder rBound : ℕ) (ha : 0 < aDegree) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Ch Cl Cq : ℝ,0 < Ch ∧ 0 < Cl ∧ 0 < Cq ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf→M.xs ≤ 1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length→T.leaves ≤ rBound→
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x→x ≤ W→
          partitionPoint 0 as U ≤ Ccut*W→
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e)→
        ∀a : T.Slot,
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
          let f2:=fun j=>((R j)^(2/p))^2
          let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Ch^aDegree*
            sourceMonomialScale x W initial
          let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Cl^aDegree*
            sourceMonomialScale x W initial
          |nativeOriginalLongitudinalRestoration n q U b h K S T
            (G.canonicalOriginalQSource M forms).product a| ≤
            (pairForkVariation (rBound+3)*CH*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p))*
              nativeOriginalRestorationProfileVariation rBound*(T.forkCost f2+edgeBudget 0 as f2)+
            (absJetVariation (rBound+3) 1*CL*(Cq*W))*forkVariation rBound 3*
              (T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=
    eventually_actual_minimum_inherited_canonical_longitudinal_restoration_original_budget_original_q
      (D:=D) aDegree dOrder rBound ha hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
      hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Ch,Cl,Cq,hCh,hCl,hCq,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hgrid
  dsimp only at hgrid ⊢
  intro U T hU hT G forms initial x W hxsx hxW hcut hmass a
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let Mclock:=4*Cf+2*Temp
  let CH:=Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Ch^aDegree*
    sourceMonomialScale x W initial
  let CL:=Real.exp (wholeLawRowComparisonConstant (rBound+3)*Mclock)*Cl^aDegree*
    sourceMonomialScale x W initial
  have hscale : 0 ≤ sourceMonomialScale x W initial := by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx) ((M.hxs.trans_le hxsx).trans_le hxW) initial e).le
  have hCH : 0 ≤ CH:=by dsimp only [CH];positivity
  have hCL : 0 ≤ CL:=by dsimp only [CL];positivity
  have hW : 0 ≤ W:=(M.hxs.le.trans hxsx).trans hxW
  have Hwords:=native_original_G_word_restoration_sum_le_profiles T
    (finiteCutMasses_ordered us hus jGrid) U (rBound+3) rBound hT M.sweepBf M.sweepHf K a
    Mclock Temp p CH CL (Cq*W) hTemp hCH hCL (mul_nonneg hCq.le hW)
  exact (hgrid U T hU hT G forms initial x W hxsx hxW hcut hmass a).trans Hwords

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem native_actual_original_fresh_resource_joint_HIGH_restoration_eq_centered_retarget_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (kind : NativeJointHighRestorationKind) (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as) :
    let g:=nativeFreshAtSlot T 0 P.live.test.target star
    nativeActualOriginalFreshResourceJointHighRestoration_original_q kind M U P=
      nativeActualOriginalCenteredResourceJointHighRestoration_original_q kind M U (P.retarget 0)
        (g.embed P.live.test.target) g.mark := by
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let C:=nativePhysicalResourceCenter n M.sweepBf M.sweepHf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_centered_resource_fresh_rest_readout (U:=U) q b h K C T P ho
  dsimp only at Hread
  rw [HQ] at Hread
  unfold nativeActualOriginalFreshResourceJointHighRestoration_original_q nativeActualOriginalCenteredResourceJointHighRestoration_original_q
  dsimp only
  rw [Hread]

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

private theorem longitudinal_profile_price_le
    {S : Type} {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (R : ℕ→ℝ) (hR : ∀j,0 ≤ R j) (p A B Z W : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hZ : 0 ≤ Z) (hW : 0 ≤ W) :
    A*Z*(T.forkCost (fun j=>((R j)^(2/p))^2)+edgeBudget 0 as (fun j=>((R j)^(2/p))^2))+
      B*Z*W*(T.forkCost R+edgeBudget 0 as R) ≤
    (A+B+1)*Z*((T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)))+
      W*(T.forkCost R+edgeBudget 0 as R)) := by
  have Hpow : (fun j=>((R j)^(2/p))^2)=(fun j=>(R j)^(4/p)):=by
    funext j
    rw [wholeLaw_rpow_square_eq (hR j) (2/p)]
    congr 1
    ring
  rw [Hpow]
  have HF : 0 ≤ T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)):=
    add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
      (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
  have HR : 0 ≤ T.forkCost R+edgeBudget 0 as R:=
    add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have HA:=mul_le_mul_of_nonneg_right (show A ≤ A+B+1 by linarith) (mul_nonneg hZ HF)
  have HB:=mul_le_mul_of_nonneg_right (show B ≤ A+B+1 by linarith) (mul_nonneg (mul_nonneg hZ hW) HR)
  convert add_le_add HA HB using 1 <;> ring

theorem eventually_actual_minimum_inherited_all_degree_longitudinal_restoration_profile_original_q
    (aDegree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf→M.xs ≤ 1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length→T.leaves ≤ rBound→
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x→x ≤ W→
          partitionPoint 0 as U ≤ Ccut*W→
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e)→
        ∀a : T.Slot,
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
          |nativeOriginalLongitudinalRestoration n q U b h K S T
            (G.canonicalOriginalQSource M forms).product a| ≤
            C*sourceMonomialScale x W initial*
              ((T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)))+
                W*(T.forkCost R+edgeBudget 0 as R)) := by
  by_cases ha : 0 < aDegree
  · obtain ⟨Ch,Cl,Cq,hCh,hCl,hCq,H⟩:=
      eventually_actual_minimum_inherited_canonical_longitudinal_restoration_profile_budget_original_q
        (D:=D) aDegree dOrder rBound ha hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
        hm hdelta hroom hcl hcu hAz hC0 hCt
    let A:=pairForkVariation (rBound+3)*
      (Real.exp (wholeLawRowComparisonConstant (rBound+3)*(4*Cf+2*Temp))*Ch^aDegree)*
      (2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*nativeOriginalRestorationProfileVariation rBound
    let B:=absJetVariation (rBound+3) 1*
      (Real.exp (wholeLawRowComparisonConstant (rBound+3)*(4*Cf+2*Temp))*Cl^aDegree)*
      Cq*forkVariation rBound 3
    have hA : 0 ≤ A:=by
      dsimp only [A]
      have :=pairForkVariation_nonneg (rBound+3)
      have :=nativeOriginalRestorationProfileVariation_nonneg rBound
      positivity
    have hB : 0 ≤ B:=by
      dsimp only [B]
      have :=absJetVariation_nonneg (rBound+3) 1
      have :=forkVariation_nonneg rBound 3
      positivity
    refine ⟨A+B+1,by positivity,?_⟩
    filter_upwards [H] with n hn
    intro M hs0 hsxs hsource hxs L us hus hret hmesh
    filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro U T hU hT G forms initial x W hxsx hxW hcut hmass a
    let as:=finiteCutMasses us jGrid
    let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
    have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
    have hR j : 0 ≤ R j:=by
      dsimp only [R,nativeOriginalHighErrorEnvelope]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
          (add_nonneg (Real.sqrt_nonneg _) (by positivity))
    have hZ : 0 ≤ sourceMonomialScale x W initial:=by
      rw [←source_factor_scale_product]
      exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx)
        ((M.hxs.trans_le hxsx).trans_le hxW) initial e).le
    have Hnum:=longitudinal_profile_price_le T ho R hR p A B (sourceMonomialScale x W initial) W
      hA hB hZ ((M.hxs.le.trans hxsx).trans hxW)
    apply (hj U T hU hT G forms initial x W hxsx hxW hcut hmass a).trans
    convert Hnum using 1
    dsimp only [A,B,R,as]
    ring
  · have hz : aDegree=0:=by omega
    subst aDegree
    obtain ⟨Cq,hCq,H⟩:=eventually_actual_minimum_inherited_constant_longitudinal_restoration_profile_original_q
      (D:=D) rBound p hp Bclock Temp Cf Ccut hTemp hCf hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
    let A:=pairForkVariation (rBound+3)*(2*Temp)^((p-2)/p)*(2*Temp)^((p-2)/p)*
      nativeOriginalRestorationProfileVariation rBound
    let B:=absJetVariation (rBound+3) 1*Cq*forkVariation rBound 3
    have hA : 0 ≤ A:=by
      dsimp only [A]
      have :=pairForkVariation_nonneg (rBound+3)
      have :=nativeOriginalRestorationProfileVariation_nonneg rBound
      positivity
    have hB : 0 ≤ B:=by
      dsimp only [B]
      have :=absJetVariation_nonneg (rBound+3) 1
      have :=forkVariation_nonneg rBound 3
      positivity
    refine ⟨A+B+1,by positivity,?_⟩
    filter_upwards [H] with n hn
    intro M hs0 hsxs hsource hxs L us hus hret hmesh
    filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro U T hU hT G forms initial x W hxsx hxW hcut _hmass a
    let as:=finiteCutMasses us jGrid
    let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
    have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
    have hR j : 0 ≤ R j:=by
      dsimp only [R,nativeOriginalHighErrorEnvelope]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
          (add_nonneg (Real.sqrt_nonneg _) (by positivity))
    have hZ : sourceMonomialScale x W initial=1:=by
      rw [←source_factor_scale_product]
      exact Fin.prod_univ_zero _
    have Hprod : (G.canonicalOriginalQSource M forms).product=(fun _=>1):=
      funext (native_canonical_source_zero_degree_product_original_q G M forms)
    rw [Hprod]
    rw [hZ]
    have Hnum:=longitudinal_profile_price_le T ho R hR p A B 1 W
      hA hB zero_le_one ((M.hxs.le.trans hxsx).trans hxW)
    apply (hj U T hU hT W (hxsx.trans hxW) hcut a).trans
    convert Hnum using 1
    dsimp only [A,B,R,as]
    ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_minimum_inherited_bounded_degree_longitudinal_restoration_profile_original_q
    (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf→M.xs ≤ 1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ M.xs→
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        let Mclock:=4*Cf+2*Temp
        ∀aDegree : ℕ,aDegree ≤ degree →
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length→T.leaves ≤ rBound→
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
          (initial : Finset (Fin aDegree)) (x W : ℝ),M.xs ≤ x→x ≤ W→
          partitionPoint 0 as U ≤ Ccut*W→
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e)→
        ∀a : T.Slot,
          let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as Mclock Temp
          |nativeOriginalLongitudinalRestoration n q U b h K S T
            (G.canonicalOriginalQSource M forms).product a| ≤
            C*sourceMonomialScale x W initial*
              ((T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)))+
                W*(T.forkCost R+edgeBudget 0 as R)) := by
  classical
  have HP (a : Fin (degree+1)):=eventually_actual_minimum_inherited_all_degree_longitudinal_restoration_profile_original_q
    (D:=D) a.val dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  choose C hC HC using HP
  let Cmax:=1+∑a : Fin (degree+1),C a
  have hsum : 0 ≤ ∑a : Fin (degree+1),C a:=Finset.sum_nonneg (fun a _=>(hC a).le)
  have hCmax : 0 < Cmax:=by dsimp only [Cmax];linarith
  have hdom a : C a ≤ Cmax:=by
    have H:=Finset.single_le_sum (fun a _=>(hC a).le) (Finset.mem_univ a)
    dsimp only [Cmax]
    linarith
  refine ⟨Cmax,hCmax,?_⟩
  filter_upwards [Filter.eventually_all.mpr HC] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  have Hgrids a:=hn a M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [Filter.eventually_all.mpr Hgrids] with jGrid hj
  dsimp only at hj ⊢
  intro aDegree hdegree U T hU hT G forms initial x W hxsx hxW hcut hmass slot
  let a : Fin (degree+1):=⟨aDegree,by omega⟩
  have Hraw:=hj a U T hU hT G forms initial x W hxsx hxW hcut hmass slot
  let as:=finiteCutMasses us jGrid
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hZ : 0 ≤ sourceMonomialScale x W initial:=by
    rw [←source_factor_scale_product]
    exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos (M.hxs.trans_le hxsx)
      ((M.hxs.trans_le hxsx).trans_le hxW) initial e).le
  have HF : 0 ≤ T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)):=
    add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
      (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
  have HR : 0 ≤ T.forkCost R+edgeBudget 0 as R:=
    add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  exact Hraw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hdom a) hZ)
    (add_nonneg HF (mul_nonneg ((M.hxs.le.trans hxsx).trans hxW) HR)))

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem eventually_actual_minimum_inherited_resource_longitudinal_restoration_from_minimum_original_q
    (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound →
        seed.length+k ≤ degree →
        ∀x W : ℝ,M.xs ≤ x → x ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀a : T.Slot,
        let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
        |(W⁻¹)^k*nativeActualResourceLongitudinalRestoration_original_q M U P a| ≤
          |P.coefficient| *nativeResourceScale x W 1 seed*
            (C*(T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
              W*(T.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_inherited_bounded_degree_longitudinal_restoration_profile_original_q
    (D:=D) degree dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨A,hA,HA⟩:=eventually_actual_minimum_inherited_raw_resource_pair_budget_original_q
    (D:=D) (degree+1) (by omega) Bclock Temp Cf Cmass hTemp hCf hCmass
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have hA0 : 0 < A:=zero_lt_one.trans_le hA
  refine ⟨C*A^degree,by positivity,?_⟩
  filter_upwards [HC,HA] with n hnC hnA
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hnC M hs0 hsxs hsource hxs L us hus hret hmesh,
    hnA M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hjC hjA
  dsimp only at hjC hjA ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth x W hx hxW _hW1 hmi hms hcut a
  have Hdegree : P.resources.length ≤ degree+1:=by rw [hP.total_factor_depth];omega
  have HP:=hjA U i star T P Hdegree (hi.trans (hs.le.trans hU)) (hs.le.trans hU)
    x W hx hxW hmi hms 1 1 (by norm_num) (by norm_num)
  let as:=finiteCutMasses us jGrid
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
  let profile:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
    W*(T.forkCost R+edgeBudget 0 as R)
  let G:=nativeActualResourceCanonicalShape P.live hi (hs.trans_le hU)
  let I:=nativeActualResourceInitialFactors P.live
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have HF : 0 ≤ T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p)):=
    add_nonneg (T.forkCost_nonneg (fun j=>Real.rpow_nonneg (hR j) _))
      (edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) _))
  have HR : 0 ≤ T.forkCost R+edgeBudget 0 as R:=
    add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have hprofile : 0 ≤ profile:=add_nonneg HF (mul_nonneg ((M.hxs.le.trans hx).trans hxW) HR)
  have HliveDegree : P.live.factors.length ≤ degree:=by
    have Hlen:=hP.total_factor_depth
    simp only [NativeResourceTerm.resources,List.length_append,NativeResourceMonomial.tags,
      List.length_map] at Hlen
    omega
  have HL:=hjC P.live.factors.length HliveDegree U T hU hT G (fun _=>.centered) I x W hx hxW hcut
    (native_actual_resource_canonical_source_mass P.live hi (hs.trans_le hU) Cmass x W hmi hms) a
  rw [native_actual_resource_live_scale_eq_annotations] at HL
  have Hcenter : nativePhysicalResourceCenter n M.sweepBf M.sweepHf as=
      (fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)):=by
    funext j
    exact (native_ordered_source_center_eq_completed n M.sweepBf M.sweepHf
      M.inherited_bf_monotone M.inherited_hf_monotone (partitionPoint_mem as ho j)).symm
  rw [←Hcenter] at HL
  have H:=actual_resource_longitudinal_restoration_normalized_profile_le_original_q M hP hdepth ho hi
    (hs.trans_le hU) a hA hx hxW (mul_nonneg hC.le hprofile) HP (by
      dsimp only
      convert HL using 1 <;> first
      | rfl
      | (dsimp only [G,profile,R,as];ring))
  apply H.trans_eq
  dsimp only [profile,R,as]
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 22000000

theorem eventually_actual_minimum_inherited_centered_resource_longitudinal_restoration_profile_original_q
    (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound →
        seed.length+k ≤ degree →
        ∀x W : ℝ,M.xs ≤ x → x ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀a : T.Slot,
        let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
        |(W⁻¹)^k*nativeActualOriginalCenteredResourceLongitudinalRestoration_original_q M U P a| ≤
          |P.coefficient| *nativeResourceScale x W 1 seed*
            (C*(T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
              W*(T.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_resource_longitudinal_restoration_from_minimum_original_q
    (D:=D) degree dOrder rBound hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth x W hx hxW hW1 hmi hms hcut a
  have ho:=finiteCutMasses_ordered us hus jGrid
  rw [native_actual_centered_resource_longitudinal_restoration_eq_two_resources_original_q M U P ho a,mul_add]
  have HP:=hj i star U k seed T P hP hi hs hU hT hdepth x W hx hxW hW1 hmi hms hcut a
  have HF:=hj i star U k seed T P.freeze hP.freeze hi hs hU hT hdepth x W hx hxW hW1 hmi hms hcut a
  simp only [NativeResourceTerm.freeze,abs_neg] at HF
  apply ((abs_add_le _ _).trans (add_le_add HP HF)).trans_eq
  ring

theorem eventually_actual_minimum_inherited_fresh_resource_longitudinal_restoration_profile_original_q
    (degree dOrder rBound : ℕ) (hd : 0 < dOrder)
    (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ))
    (Bclock Temp Cf Cmass Ccut : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound →
        seed.length+k ≤ degree →
        ∀x W : ℝ,M.xs ≤ x → x ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        ∀right : Bool,
        let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
        |(W⁻¹)^k*nativeActualOriginalFreshResourceLongitudinalRestoration_original_q M U P right| ≤
          |P.coefficient| *nativeResourceScale x W 1 seed*
            (C*(T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
              W*(T.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_centered_resource_longitudinal_restoration_profile_original_q
    (D:=D) degree dOrder (rBound+1) hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth x W hx hxW hW1 hmi hms hcut right
  let as:=finiteCutMasses us jGrid
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
  let f:=fun j=>(R j)^(4/p)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves ≤ rBound+1:=by
    have HH:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 P.live.test.target star)
    omega
  have H0:=hj i star U k seed g.tree (P.retarget 0) hP.retarget hi hs hU hg hdepth
    x W hx hxW hW1 hmi hms hcut (if right then g.mark else g.embed P.live.test.target)
  have hlo j (hj : j<U) : R j=0:=by
    simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hflo j (hj : j<U) : f j=0:=by
    dsimp only [f]
    rw [hlo j hj,Real.zero_rpow (by positivity : 4/p≠0)]
  have Hf:=nativeFreshAtSlot_high_forkCost T 0 P.live.test.target hs f hflo
  have HR:=nativeFreshAtSlot_high_forkCost T 0 P.live.test.target hs R hlo
  rw [native_actual_fresh_resource_longitudinal_restoration_eq_centered_retarget_original_q M U P ho right]
  change |(W⁻¹)^k*nativeActualOriginalCenteredResourceLongitudinalRestoration_original_q M U (P.retarget 0)
    (if right then g.mark else g.embed P.live.test.target)| ≤ |P.coefficient| *nativeResourceScale x W 1 seed*
      (C*(T.forkCost f+edgeBudget 0 as f+W*(T.forkCost R+edgeBudget 0 as R)))
  change |(W⁻¹)^k*nativeActualOriginalCenteredResourceLongitudinalRestoration_original_q M U (P.retarget 0)
    (if right then g.mark else g.embed P.live.test.target)| ≤ |P.coefficient| *nativeResourceScale x W 1 seed*
      (C*(g.tree.forkCost f+edgeBudget 0 as f+W*(g.tree.forkCost R+edgeBudget 0 as R))) at H0
  simpa only [show g.tree.forkCost f=T.forkCost f from Hf,
    show g.tree.forkCost R=T.forkCost R from HR] using H0

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem eventually_actual_minimum_inherited_fresh_resource_joint_HIGH_restoration_from_minimum_original_q
    (kind : NativeJointHighRestorationKind) (degree dOrder rBound : ℕ)
    (hd : 0 < dOrder) (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ)) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        ∀W : ℝ,M.xs ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
        let cost:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
          W*(T.forkCost R+edgeBudget 0 as R)
        |(W⁻¹)^k*nativeActualOriginalFreshResourceJointHighRestoration_original_q kind M U P| ≤
          |P.coefficient| *nativeResourceScale M.xs W 1 seed*(C*W*cost) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_centered_resource_joint_HIGH_restoration_from_minimum_original_q
    (D:=D) kind degree dOrder (rBound+1) hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth W hxW hW1 hmi hms hcut
  let as:=finiteCutMasses us jGrid
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
  let f:=fun j=>(R j)^(4/p)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves ≤ rBound+1:=by
    have H:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 P.live.test.target star)
    omega
  have Hsplit : g.tree.splitIndex (g.embed P.live.test.target) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,min_eq_left (hs.le.trans hU)]
  have hRlo j (hj : j<U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hflo j (hj : j<U) : f j=0:=by
    dsimp only [f]
    rw [hRlo j hj,Real.zero_rpow (by positivity : 4/p≠0)]
  have HR:=nativeFreshAtSlot_high_forkCost T 0 P.live.test.target hs R hRlo
  have HF:=nativeFreshAtSlot_high_forkCost T 0 P.live.test.target hs f hflo
  have Hbound:=hj i star U k seed g.tree (P.retarget 0) hP.retarget hi hs hU hg hdepth
    W hxW hW1 hmi hms hcut (g.embed P.live.test.target) g.mark (by rw [Hsplit];exact hs)
  rw [native_actual_original_fresh_resource_joint_HIGH_restoration_eq_centered_retarget_original_q kind M U P ho]
  change |(W⁻¹)^k*nativeActualOriginalCenteredResourceJointHighRestoration_original_q kind M U (P.retarget 0)
      (g.embed P.live.test.target) g.mark| ≤ _
  change |(W⁻¹)^k*nativeActualOriginalCenteredResourceJointHighRestoration_original_q kind M U (P.retarget 0)
      (g.embed P.live.test.target) g.mark| ≤ |P.coefficient| *nativeResourceScale M.xs W 1 seed*
        (C*W*(g.tree.forkCost f+edgeBudget 0 as f+W*(g.tree.forkCost R+edgeBudget 0 as R))) at Hbound
  rw [show g.tree.forkCost f=T.forkCost f from HF,show g.tree.forkCost R=T.forkCost R from HR] at Hbound
  exact Hbound

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem eventually_actual_minimum_inherited_working_scale_fresh_resource_joint_HIGH_restoration_from_minimum_original_q
    (kind : NativeJointHighRestorationKind) (degree dOrder rBound : ℕ)
    (hd : 0 < dOrder) (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ)) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        ∀xScale W : ℝ,M.xs ≤ xScale → xScale ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*xScale → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
        let cost:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
          W*(T.forkCost R+edgeBudget 0 as R)
        |(W⁻¹)^k*nativeActualOriginalFreshResourceJointHighRestoration_original_q kind M U P| ≤
          |P.coefficient| *nativeResourceScale xScale W 1 seed*(C*W*cost) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_working_scale_centered_resource_joint_HIGH_restoration_from_minimum_original_q
    (D:=D) kind degree dOrder (rBound+1) hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth xScale W hxsScale hxW hW1 hmi hms hcut
  let as:=finiteCutMasses us jGrid
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  let R:=nativeOriginalHighErrorEnvelope n U M.sweepBf M.sweepHf as (4*Cf+2*Temp) Temp
  let f:=fun j=>(R j)^(4/p)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves ≤ rBound+1:=by
    have H:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 P.live.test.target star)
    omega
  have Hsplit : g.tree.splitIndex (g.embed P.live.test.target) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,min_eq_left (hs.le.trans hU)]
  have hRlo j (hj : j<U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hflo j (hj : j<U) : f j=0:=by
    dsimp only [f]
    rw [hRlo j hj,Real.zero_rpow (by positivity : 4/p≠0)]
  have HR:=nativeFreshAtSlot_high_forkCost T 0 P.live.test.target hs R hRlo
  have HF:=nativeFreshAtSlot_high_forkCost T 0 P.live.test.target hs f hflo
  have Hbound:=hj i star U k seed g.tree (P.retarget 0) hP.retarget hi hs hU hg hdepth
    xScale W hxsScale hxW hW1 hmi hms hcut (g.embed P.live.test.target) g.mark (by rw [Hsplit];exact hs)
  rw [native_actual_original_fresh_resource_joint_HIGH_restoration_eq_centered_retarget_original_q kind M U P ho]
  change |(W⁻¹)^k*nativeActualOriginalCenteredResourceJointHighRestoration_original_q kind M U (P.retarget 0)
      (g.embed P.live.test.target) g.mark| ≤ _
  change |(W⁻¹)^k*nativeActualOriginalCenteredResourceJointHighRestoration_original_q kind M U (P.retarget 0)
      (g.embed P.live.test.target) g.mark| ≤ |P.coefficient| *nativeResourceScale xScale W 1 seed*
        (C*W*(g.tree.forkCost f+edgeBudget 0 as f+W*(g.tree.forkCost R+edgeBudget 0 as R))) at Hbound
  rw [show g.tree.forkCost f=T.forkCost f from HF,show g.tree.forkCost R=T.forkCost R from HR] at Hbound
  exact Hbound

end OAI.SKFluctuations.Cavity
