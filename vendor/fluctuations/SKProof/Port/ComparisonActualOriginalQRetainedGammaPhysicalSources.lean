module

public import ComparisonSignedCavityActualMinimumResampling
public import ComparisonSignedCavityActualBufferDyadicCount
public import ComparisonSignedCavityObservedCalibrationScale
public import ComparisonSignedCavityGeneratedExteriorShape
public import ComparisonSignedCavityActualObservedProjectionFactorization
public import ComparisonSignedCavityGeneratedBaseFactorization
public import ComparisonSignedCavityGeneratedMarkedReset
public import ComparisonSignedCavityActualResetStarIncomingSource
public import ComparisonSignedCavityActualResetIncomingSource
public import ComparisonSignedCavityResetPairedValue
public import ComparisonSignedCavityActualResetPowerSource
public import ComparisonSignedCavityRadiusRowInterval
public import ComparisonSignedCavityActualRadiusDyadicCover
public import ComparisonSignedCavityResetPairedRowAlgebra
public import ComparisonSignedCavityInheritedAnchorPrimitives
public import ComparisonSignedCavityInheritedStarSubtreeProjection
public import ComparisonSignedCavityInheritedCalibratedStarSubtreeProjection
public import ComparisonSignedCavityInheritedCanonicalExteriorMoments
public import ComparisonSignedCavityInheritedIRootAnchorRaw
public import ComparisonSignedCavityInheritedTwoLevelProjection
public import ComparisonSignedCavityInheritedCanonicalTwoLevelProjection
public import ComparisonSignedCavityInheritedStarRootAnchorRaw
public import ComparisonSignedCavityInheritedStarTwoLevelProjection
public import ComparisonSignedCavityInheritedCanonicalStarTwoLevelProjection
public import ComparisonSignedCavityProjectedGammaRowTopology
public import ComparisonSignedCavityProjectionSpinePhysicalRow
public import ComparisonSignedCavityInheritedGammaSourceBaseFourth
public import SKProof.Port.ComparisonActualOriginalQObservedInnovationSource
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQNaturalSourceCalibration
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics

@[expose] public section
noncomputable section
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 4500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations
open Hierarchy Cavity

end OAI.SKFluctuations

namespace OAI.SKFluctuations
open Hierarchy Cavity

end OAI.SKFluctuations

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity

theorem native_minimum_original_boundary_critical_radius_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ} (hC0 : 0<C0)
    (a : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) :
    (n:ℝ)^(-(1:ℝ)/6+m) ≤ C0*a.xs := by
  have hN := a.data.hN
  have hsqrt : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hN
  have he : Real.sqrt (n:ℝ)*(n:ℝ)^(-(2:ℝ)/3+m)=(n:ℝ)^(-(1:ℝ)/6+m) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_add hN]
    congr 1
    ring
  have H := mul_le_mul_of_nonneg_left a.hlower hsqrt.le
  have H' : (n:ℝ)^(-(1:ℝ)/6+m)*a.data.d ≤ C0*(Real.sqrt (n:ℝ)*a.data.E) := by
    rw [←he]
    nlinarith [H]
  have Hscale : (n:ℝ)^(-(1:ℝ)/6+m) ≤ C0*comparisonLowerScale n a.data.E a.data.d := by
    unfold comparisonLowerScale
    rw [←mul_div_assoc]
    exact (le_div_iff₀ a.data.hd).mpr H'
  exact Hscale.trans (mul_le_mul_of_nonneg_left a.hscale hC0.le)

end OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity
set_option maxHeartbeats 6000000

namespace ActualThetaZeroOverlapMinimum

theorem eventually_actual_minimum_scale_polynomial_lower_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.N^(-(2:ℝ)) ≤ M.xs := by
  have Hcoef := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=1/C0) (q:=-(2:ℝ)) (r:=-(1:ℝ))
      (by positivity) (by norm_num))
  filter_upwards [Hcoef] with n hn
  intro M
  have hupper : M.data.E ≤ M.data.d^2/Real.sqrt M.data.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr M.data.hN)).mpr (by simpa only [mul_comm] using M.hupper)
  have hlower : (1/C0)*M.data.N^(-(2:ℝ)/3+m)*M.data.d ≤ M.data.E := by
    have H : (M.data.N^(-(2:ℝ)/3+m)*M.data.d)/C0 ≤ M.data.E :=
      (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using M.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have Hparent := comparison_parent_scale_lower_bounds M.data.hN (one_div_pos.mpr hC0)
    M.data.hd hlower hupper
  have Hpow : M.data.N^(-(1:ℝ)) ≤ M.data.N^(-(1:ℝ)/6+m) :=
    Real.rpow_le_rpow_of_exponent_le (by
      dsimp only [ActualHighWallData.N]
      exact_mod_cast Nat.succ_pos n) (by linarith)
  have Hx := (mul_le_mul_of_nonneg_left Hpow (one_div_pos.mpr hC0).le).trans
    (Hparent.2.2.trans M.hscale)
  exact (show M.data.N^(-(2:ℝ)) ≤ (1/C0)*M.data.N^(-(1:ℝ)) by
    simpa only [ActualHighWallData.N,one_mul] using hn).trans Hx

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization
set_option maxHeartbeats 4000000

theorem native_minimum_observed_calibration_scales_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock C v : ℝ}
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hn : 2 ≤ n) (hm : 0 ≤ m) (hC0 : 0 < C0) (hC : 1 ≤ C)
    (hcompare : a.xs^2 ≤ C^2*laplaceComparisonStrength a.data.d a.lam a.xs)
    (hWv : max a.xs (Real.sqrt (laplaceComparisonStrength a.data.d a.lam a.xs)) ≤ v)
    (hv1 : v ≤ 1) :
    let W := max a.xs (Real.sqrt (laplaceComparisonStrength a.data.d a.lam a.xs))
    (n:ℝ)^(-(1:ℝ)/6+m) ≤ (2*C0)*a.xs ∧
      (1/(24*C^3))*W^3/Real.log (n:ℝ) ≤
        laplaceComparisonStrength a.data.d a.lam v*v/(12*Real.log ((n+1:ℕ):ℝ)) := by
  dsimp only
  constructor
  · have H := observed_critical_power_succ (by omega : 1 ≤ n)
      (show -1 ≤ -(1:ℝ)/6+m by linarith)
    have Hmin := native_minimum_original_boundary_critical_radius_original_q hC0 a
    nlinarith
  · exact observed_direct_test_innovation_strength hn a.data.hd a.hlam a.hld a.hxs
      hC hcompare hWv hv1

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_generated_exterior_canonical_product_original_q (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hstar : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (σ : T.Assignment) :
    ((nativeGeneratedExteriorShape n P hP hi hstar).canonicalOriginalQSource M
      (fun _=>NativeSourceFactorForm.centered)).product σ =
      nativeGeneratedEdgeProduct T (fun s t=>deletedOverlap n (joinSpin s) (joinSpin t))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1))
          (partitionPoint 0 as j)) P.exterior σ := by
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  rw [←List.prod_ofFn]
  unfold nativeGeneratedEdgeProduct
  conv_rhs => rw [←List.ofFn_get P.exterior,List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext e
  simp only [ActualNaturalBoundaryShape.canonicalOriginalQSource,
    ActualNaturalBoundaryShape.sourceLowMass,nativeGeneratedExteriorShape,
    NativeSourceFactorForm.intercept,NativeSourceFactorForm.slope,
    fullBoundaryAffineFactor,one_mul]
  rw [T.splitIndex_symm]
  dsimp only [Function.comp_apply]
  ring

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 20000000
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S B : Type} [Fintype ι] [Fintype S] [Nonempty S] [Fintype B] [Nonempty B]
variable {as : List PositiveMass}

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_actual_observed_generated_dynamic_exterior_source_original_q
    (n : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (c : T.Slot) (hh : U≤p.tree.splitIndex p.mark (p.embed c))
    (hc : U≤T.splitIndex c P.live.test.target)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ) :
    let hlen : U≤(pre++(mid++tail)).length:=hh.trans (p.tree.splitIndex_le_clockLength _ _)
    let G:=nativeGeneratedExteriorShape n P.live.test P.live.ancestry (by omega) (hU.trans_le hlen)
    Nonempty (NativeDynamicCanonicalExteriorSource n P.live.test.exterior.length pre mid tail p.tree
      (p.tree.cavityLeftSlot (p.embed c))
      ((G.retainOnMarked a p hp).canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)) v q x) := by
  dsimp only
  apply native_actual_generated_dynamic_canonical_exterior_source n _ pre mid tail hP hmid hU a p hp c hh ho
  intro j
  simpa only [ActualNaturalBoundaryShape.restLabels,ActualNaturalBoundaryShape.canonicalOriginalQSource]
    using native_generated_exterior_marked_labels_low n P.live.test P.live.ancestry
      (by omega) hU (hh.trans (p.tree.splitIndex_le_clockLength _ _)) a p hp c hc j

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 14000000
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S B : Type} {as : List PositiveMass}

variable [Nonempty B]

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_generated_exterior_canonical_rest_product_original_q (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hstar : star < as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (σ : T.cavityLeft.Assignment) :
    ((nativeGeneratedExteriorShape n P hP hi hstar).canonicalOriginalQSource M
      (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      nativeRestGeneratedExteriorValue T P
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1))
          (partitionPoint 0 as j)) σ := by
  let τ:=T.cavityAssignment.symm (σ,assignmentOfSlots T.cavityRight (fun _=>false))
  have ht : (T.cavityAssignment τ).1=σ := by
    dsimp only [τ]
    rw [Equiv.apply_symm_apply]
  have H:=native_generated_exterior_canonical_product_original_q n P hP hi hstar M τ
  rw [ActualNaturalBoundaryShape.product_eq_restProduct,ht] at H
  rw [←ht,native_rest_generated_exterior_value_eq_full]
  rw [ht,H]
  unfold nativeGeneratedEdgeProduct
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  simp [deletedOverlap,joinSpin]

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_generated_marked_canonical_rest_product_original_q (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P) (hi : i ≤ star) (hlen : star<as.length)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (r : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach r)
    (σ : p.tree.cavityLeft.Assignment) :
    (((nativeGeneratedCompleteShape n P hP hi hlen).retainOnMarked r p hp).canonicalOriginalQSource M
      (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      nativeRestGeneratedTestValue T P
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1)) (partitionPoint 0 as j))
        (p.restRestrict σ) := by
  rw [ActualNaturalBoundaryShape.retained_canonical_restProduct_original_q,
    native_generated_complete_canonical_rest_product_original_q]

theorem native_generated_marked_reset_change_original_q (n : ℕ) {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : NativeGeneratedTest T)
    {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P) (ht : P.teeth=[])
    (hi : i ≤ star) (hlen : star<as.length) (e : T.Slot) (hIncoming : P.incoming=[e])
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (r : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach r)
    (σ : p.tree.cavityLeft.Assignment) :
    let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
    let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
    nativeRestGeneratedTestValue T P R C
      (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) (p.restRestrict σ) (p.restSpin σ))-
      (((nativeGeneratedCompleteShape n P hP hi hlen).retainOnMarked r p hp).canonicalOriginalQSource M
        (fun _=>NativeSourceFactorForm.centered)).restProduct σ=
      (((nativeGeneratedExteriorShape n P hP hi hlen).retainOnMarked r p hp).canonicalOriginalQSource M
        (fun _=>NativeSourceFactorForm.centered)).restProduct σ*
      (R (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot p.mark))
          (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.embed e)))-
        R (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.embed P.target)))
          (p.tree.cavityLeft.atSlot σ (p.tree.cavityLeftSlot (p.embed e)))) := by
  dsimp only
  rw [native_generated_marked_canonical_rest_product_original_q,
    native_rest_generated_reset_replace_sub P hP ht hi hlen,
    ActualNaturalBoundaryShape.retained_canonical_restProduct_original_q,
    native_generated_exterior_canonical_rest_product_original_q,hIncoming]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,p.restRestrict_at]
  rfl

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 22000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_actual_reset_incoming_star_paired_source_original_q
    (n : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length < U)
    (ht : P.live.test.teeth=[]) (e₀ : T.Slot) (hIn : P.live.test.incoming=[e₀])
    (hi : T.splitIndex P.live.test.target e₀=pre.length+mid.length)
    (r : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach r)
    (hh : U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target))
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ)
    (d : ℕ) (center : ℝ) :
    let as:=pre++(mid++tail)
    let hlen : pre.length+mid.length<as.length:=
      hU.trans_le (hh.trans (p.tree.splitIndex_le_clockLength _ _))
    let G:=((nativeGeneratedExteriorShape n P.live.test P.live.ancestry (by omega) hlen).retainOnMarked r p hp).canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)
    let G₀:=((nativeGeneratedCompleteShape n P.live.test P.live.ancestry (by omega) hlen).retainOnMarked r p hp).canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)
    let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
    let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
    let B:=fun σ=>nativeRestGeneratedTestValue T P.live.test R C
      (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.live.test.target)
        (p.restRestrict σ) (p.restSpin σ))
    ∃E : NativeDynamicCanonicalExteriorSource n P.live.test.exterior.length pre mid tail p.tree
      (p.tree.cavityLeftSlot (p.embed P.live.test.target)) G v q x,
    ∃(t : E.D.Slot) (e : E.Es.Slot),
      (∀η ζ δ,p.restSpin (E.read η ζ δ)=E.D.atSlot δ t) ∧
      (∀η ζ δ,T.cavityLeft.atSlot (p.restRestrict (E.read η ζ δ)) (T.cavityLeftSlot e₀)=
        E.Es.atSlot ζ e) ∧
      pre.length+mid.length+E.D.splitIndex E.target t=
        p.tree.splitIndex (p.embed P.live.test.target) p.mark ∧
    let dq:=cumulativeIncrements (q 0) (fun l=>q (l+1))
    let qi:=fun l=>dq (pre.length+l)
    let qs:=fun l=>dq (pre.length+(mid.length+l))
    let Y:=fun y=>nativeStarCenteredProjection n tail qs center y
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed P.live.test.target)) (pre.length+mid.length) v q
      (fun y σ=>(Y y (p.restSpin σ)-Y y
        (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot P.live.test.target)))*
        (B σ*Y y (p.restSpin σ)^d-G₀.restProduct σ*Y y
          (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot P.live.test.target))^d)) x=
      (∫z,nativeTwoLevelStarIncomingProduct n 0 d E.Ei E.Es E.D E.H e E.target t qi qs center
        (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x)+
      ∑j∈Finset.range d,∫z,nativeTwoLevelPowerProduct n j (d-1-j) E.Ei E.Es E.D
        (fun η ζ δ=>G₀.restProduct (E.read η ζ δ)) E.target t qi qs center
        (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
  dsimp only
  have hlen : U≤(pre++(mid++tail)).length:=hh.trans (p.tree.splitIndex_le_clockLength _ _)
  have hself : U≤T.splitIndex P.live.test.target P.live.test.target:=by rw [T.splitIndex_self];exact hlen
  obtain ⟨E⟩:=native_actual_observed_generated_dynamic_exterior_source_original_q n pre mid tail hP hmid hU
    r p hp P.live.test.target hh hself ho M v q x
  have hHigh : pre.length+mid.length<p.tree.cavityLeft.splitIndex
      (p.tree.cavityLeftSlot (p.embed P.live.test.target)) (p.tree.cavityLeftSlot p.mark) := by
    rw [cavityLeft_splitIndex,splitIndex_symm]
    exact hU.trans_le hh
  obtain ⟨t,htRead,htSplit⟩:=E.high (p.tree.cavityLeftSlot p.mark) hHigh
  have hLow : p.tree.cavityLeft.splitIndex (p.tree.cavityLeftSlot (p.embed P.live.test.target))
      (p.tree.cavityLeftSlot (p.embed e₀))=pre.length+mid.length := by
    rw [cavityLeft_splitIndex,(T.markedAttach_embed_preserves r p hp).2,hi]
  obtain ⟨e,heRead⟩:=E.incoming_star (p.tree.cavityLeftSlot (p.embed e₀)) hLow
  refine ⟨E,t,e,htRead,?_,?_,?_⟩
  · intro η ζ δ
    rw [p.restRestrict_at]
    exact heRead η ζ δ
  · simpa only [cavityLeft_splitIndex] using htSplit
  · have H:=E.paired_incoming_star_allocation ho (p.tree.cavityLeftSlot p.mark)
      (p.tree.cavityLeftSlot (p.embed e₀)) t e htRead heRead _ _
      (fun σ=>native_generated_marked_reset_change_original_q n P.live.test P.live.ancestry ht
        (by omega) (hU.trans_le hlen) e₀ hIn M r p hp σ) d center
    simpa only [p.restRestrict_at,MarkedPlacement.restSpin] using H

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 22000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_actual_reset_incoming_i_paired_source_original_q
    (n : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length < U)
    (ht : P.live.test.teeth=[]) (e₀ : T.Slot) (hIn : P.live.test.incoming=[e₀])
    (hi : T.splitIndex P.live.test.target e₀=pre.length)
    (r : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach r)
    (hh : U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target))
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ)
    (d : ℕ) (center : ℝ) :
    let as:=pre++(mid++tail)
    let hlen : pre.length+mid.length<as.length:=
      hU.trans_le (hh.trans (p.tree.splitIndex_le_clockLength _ _))
    let G:=((nativeGeneratedExteriorShape n P.live.test P.live.ancestry (by omega) hlen).retainOnMarked r p hp).canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)
    let G₀:=((nativeGeneratedCompleteShape n P.live.test P.live.ancestry (by omega) hlen).retainOnMarked r p hp).canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)
    let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
    let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
    let B:=fun σ=>nativeRestGeneratedTestValue T P.live.test R C
      (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.live.test.target)
        (p.restRestrict σ) (p.restSpin σ))
    ∃E : NativeDynamicCanonicalExteriorSource n P.live.test.exterior.length pre mid tail p.tree
      (p.tree.cavityLeftSlot (p.embed P.live.test.target)) G v q x,
    ∃(t : E.D.Slot) (e : E.Ei.Slot),
      (∀η ζ δ,p.restSpin (E.read η ζ δ)=E.D.atSlot δ t) ∧
      (∀η ζ δ,T.cavityLeft.atSlot (p.restRestrict (E.read η ζ δ)) (T.cavityLeftSlot e₀)=
        E.Ei.atSlot η e) ∧
      pre.length+mid.length+E.D.splitIndex E.target t=
        p.tree.splitIndex (p.embed P.live.test.target) p.mark ∧
    let dq:=cumulativeIncrements (q 0) (fun l=>q (l+1))
    let qi:=fun l=>dq (pre.length+l)
    let qs:=fun l=>dq (pre.length+(mid.length+l))
    let Y:=fun y=>nativeStarCenteredProjection n tail qs center y
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed P.live.test.target)) (pre.length+mid.length) v q
      (fun y σ=>(Y y (p.restSpin σ)-Y y
        (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot P.live.test.target)))*
        (B σ*Y y (p.restSpin σ)^d-G₀.restProduct σ*Y y
          (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot P.live.test.target))^d)) x=
      (∫z,nativeTwoLevelIncomingProduct n 0 d E.Ei E.Es E.D E.H e E.target t qi qs center
        (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x)+
      ∑j∈Finset.range d,∫z,nativeTwoLevelPowerProduct n j (d-1-j) E.Ei E.Es E.D
        (fun η ζ δ=>G₀.restProduct (E.read η ζ δ)) E.target t qi qs center
        (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
  dsimp only
  have hlen : U≤(pre++(mid++tail)).length:=hh.trans (p.tree.splitIndex_le_clockLength _ _)
  have hself : U≤T.splitIndex P.live.test.target P.live.test.target:=by rw [T.splitIndex_self];exact hlen
  obtain ⟨E⟩:=native_actual_observed_generated_dynamic_exterior_source_original_q n pre mid tail hP hmid hU
    r p hp P.live.test.target hh hself ho M v q x
  have hHigh : pre.length+mid.length<p.tree.cavityLeft.splitIndex
      (p.tree.cavityLeftSlot (p.embed P.live.test.target)) (p.tree.cavityLeftSlot p.mark) := by
    rw [cavityLeft_splitIndex,splitIndex_symm]
    exact hU.trans_le hh
  obtain ⟨t,htRead,htSplit⟩:=E.high (p.tree.cavityLeftSlot p.mark) hHigh
  have hLow : p.tree.cavityLeft.splitIndex (p.tree.cavityLeftSlot (p.embed P.live.test.target))
      (p.tree.cavityLeftSlot (p.embed e₀))=pre.length := by
    rw [cavityLeft_splitIndex,(T.markedAttach_embed_preserves r p hp).2,hi]
  obtain ⟨e,heRead⟩:=E.incoming_i (p.tree.cavityLeftSlot (p.embed e₀)) hLow
  refine ⟨E,t,e,htRead,?_,?_,?_⟩
  · intro η ζ δ
    rw [p.restRestrict_at]
    exact heRead η ζ δ
  · simpa only [cavityLeft_splitIndex] using htSplit
  · have H:=E.paired_incoming_i_allocation ho (p.tree.cavityLeftSlot p.mark)
      (p.tree.cavityLeftSlot (p.embed e₀)) t e htRead heRead _ _
      (fun σ=>native_generated_marked_reset_change_original_q n P.live.test P.live.ancestry ht
        (by omega) (hU.trans_le hlen) e₀ hIn M r p hp σ) d center
    simpa only [p.restRestrict_at,MarkedPlacement.restSpin] using H

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeResetPairedProjectionValue_original_q
    (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (p : MarkedPlacement T) (q : ℕ→RestCoordinate n→ℝ) (d : ℕ) (center : ℝ) : ℝ :=
  let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1))
    (partitionPoint 0 (pre++(mid++tail)) j)
  let Y:=nativeStarCenteredProjection n tail (nativeStarSuffixClock n pre mid q) center
  nativeStarFieldDisorderMean (restWeight n) (restFeature n) p.tree.cavityLeft
    (p.tree.cavityLeftSlot (p.embed P.target)) (pre.length+mid.length) 0 q
    (fun y σ=>
      (Y y (p.restSpin σ)-Y y (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot P.target)))*
      (nativeRestGeneratedTestValue T P R C
          (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) (p.restRestrict σ) (p.restSpin σ))*
        Y y (p.restSpin σ)^d-
        nativeRestGeneratedTestValue T P R C (p.restRestrict σ)*
        Y y (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot P.target))^d)) 0

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 22000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_actual_reset_power_paired_source_original_q
    (n : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length < U)
    (ht : P.live.test.teeth=[]) (hIn : P.live.test.incoming=[])
    (r : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach r)
    (hh : U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target))
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ)
    (d : ℕ) (center : ℝ) :
    let as:=pre++(mid++tail)
    let hlen : pre.length+mid.length<as.length:=
      hU.trans_le (hh.trans (p.tree.splitIndex_le_clockLength _ _))
    let G:=((nativeGeneratedExteriorShape n P.live.test P.live.ancestry (by omega) hlen).retainOnMarked r p hp).canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)
    let G₀:=((nativeGeneratedCompleteShape n P.live.test P.live.ancestry (by omega) hlen).retainOnMarked r p hp).canonicalOriginalQSource M (fun _=>NativeSourceFactorForm.centered)
    let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
    let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
    let B:=fun σ=>nativeRestGeneratedTestValue T P.live.test R C
      (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.live.test.target)
        (p.restRestrict σ) (p.restSpin σ))
    ∃E : NativeDynamicCanonicalExteriorSource n P.live.test.exterior.length pre mid tail p.tree
      (p.tree.cavityLeftSlot (p.embed P.live.test.target)) G v q x,
    ∃t : E.D.Slot,
      (∀η ζ δ,p.restSpin (E.read η ζ δ)=E.D.atSlot δ t) ∧
      pre.length+mid.length+E.D.splitIndex E.target t=
        p.tree.splitIndex (p.embed P.live.test.target) p.mark ∧
    let dq:=cumulativeIncrements (q 0) (fun l=>q (l+1))
    let qi:=fun l=>dq (pre.length+l)
    let qs:=fun l=>dq (pre.length+(mid.length+l))
    let Y:=fun y=>nativeStarCenteredProjection n tail qs center y
    nativeStarFieldDisorderMean (restWeight n) (restFeature n) p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed P.live.test.target)) (pre.length+mid.length) v q
      (fun y σ=>(Y y (p.restSpin σ)-Y y
        (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot P.live.test.target)))*
        (B σ*Y y (p.restSpin σ)^d-G₀.restProduct σ*Y y
          (T.cavityLeft.atSlot (p.restRestrict σ) (T.cavityLeftSlot P.live.test.target))^d)) x=
      ∑j∈Finset.range d,∫z,nativeTwoLevelPowerProduct n j (d-1-j) E.Ei E.Es E.D
        (fun η ζ δ=>G₀.restProduct (E.read η ζ δ)) E.target t qi qs center
        (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
  dsimp only
  have hlen : U≤(pre++(mid++tail)).length:=hh.trans (p.tree.splitIndex_le_clockLength _ _)
  have hself : U≤T.splitIndex P.live.test.target P.live.test.target:=by rw [T.splitIndex_self];exact hlen
  obtain ⟨E⟩:=native_actual_observed_generated_dynamic_exterior_source_original_q n pre mid tail hP hmid hU
    r p hp P.live.test.target hh hself ho M v q x
  have hHigh : pre.length+mid.length<p.tree.cavityLeft.splitIndex
      (p.tree.cavityLeftSlot (p.embed P.live.test.target)) (p.tree.cavityLeftSlot p.mark) := by
    rw [cavityLeft_splitIndex,splitIndex_symm]
    exact hU.trans_le hh
  obtain ⟨t,htRead,htSplit⟩:=E.high (p.tree.cavityLeftSlot p.mark) hHigh
  refine ⟨E,t,htRead,?_,?_⟩
  · simpa only [cavityLeft_splitIndex] using htSplit
  · have hB (σ : p.tree.cavityLeft.Assignment) :
        nativeRestGeneratedTestValue T P.live.test
          (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
          (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
            (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1))
            (partitionPoint 0 (pre++(mid++tail)) j))
          (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.live.test.target)
            (p.restRestrict σ) (p.restSpin σ))=
        (((nativeGeneratedCompleteShape n P.live.test P.live.ancestry (by omega) (hU.trans_le hlen)).retainOnMarked r p hp).canonicalOriginalQSource M
          (fun _=>NativeSourceFactorForm.centered)).restProduct σ := by
      rw [native_generated_marked_canonical_rest_product_original_q]
      apply sub_eq_zero.mp
      have H:=native_rest_generated_reset_replace_sub P.live.test P.live.ancestry ht
        (by omega) (hU.trans_le hlen)
        (fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false)))
        (fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1))
          (partitionPoint 0 (pre++(mid++tail)) j)) (p.restRestrict σ) (p.restSpin σ)
      simpa only [hIn,List.map_nil,List.sum_nil,mul_zero] using H
    have H:=E.paired_no_incoming_allocation ho (p.tree.cavityLeftSlot p.mark) t htRead
      (((nativeGeneratedCompleteShape n P.live.test P.live.ancestry (by omega) (hU.trans_le hlen)).retainOnMarked r p hp).canonicalOriginalQSource M
        (fun _=>NativeSourceFactorForm.centered)).restProduct d center
    simp_rw [hB]
    simpa only [p.restRestrict_at,MarkedPlacement.restSpin] using H

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem actual_minimum_radius_band_edgeBudget_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 ≤ cu) {mesh v : ℝ} (hv : 0 ≤ v) (hz : M.z ≤ v)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (he : partitionEnd 0 as=1) (hm : PartitionMesh mesh 0 as)
    (hmesh : 0 ≤ mesh) :
    ClockTree.edgeBudget 0 as (nativeRadiusRowBand M.sweepRadius as v) ≤ 2*cu*v+mesh := by
  have H:=native_edgeBudget_supported_mass_le as ho he hm
    (nativeRadiusRowBand M.sweepRadius as v) (nativeRadiusRowBand_nonneg _ _ _)
    (nativeRadiusRowBand_le_one _ _ _) (B:=2*cu*v) (by
      intro j hj
      unfold nativeRadiusRowBand
      split_ifs with hband
      · have hR:=M.shiftedNativeModel.R_bounds (partitionPoint 0 as j)
        have hreg:=(M.regular (M.sweepRadius (partitionPoint 0 as j)) ⟨hz.trans hband.1,hR.2⟩).2
        have hspec : partitionPoint 0 as j ≤ M.alpha.val.val (M.sweepRadius (partitionPoint 0 as j)) := by
          by_cases hsu : M.data.s≤partitionPoint 0 as j
          · have HS : M.alpha.val.val (M.sweepRadius (partitionPoint 0 as j))=partitionPoint 0 as j :=
              M.shiftedNativeModel.R_spec ⟨hsu,(partitionPoint_mem as ho j).2⟩
            exact HS.symm.le
          · have HB := (inverseConstraintMap M.alpha
              ⟨M.sweepRadius (partitionPoint 0 as j),M.shiftedNativeModel.R_bounds (partitionPoint 0 as j)⟩).property.1
            exact (le_of_not_ge hsu).trans HB
        have H:=mul_le_mul_of_nonneg_left hband.2 hcu
        nlinarith
      · rfl)
  simpa only [sub_zero,max_eq_left (by positivity : 0 ≤ 2*cu*v+mesh)] using H

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity

theorem eventually_actual_minimum_radius_dyadic_cover_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀V : ℝ,M.xs ≤ V → V ≤ 1 →
        ((comparisonMassDyadicIndices V).card:ℝ) ≤
          (2/Real.log 2+2)*Real.log ((n+1:ℕ):ℝ) ∧
        ∀(as : List PositiveMass) (cut : ℕ),V ≤ M.sweepRadius (partitionPoint 0 as cut) →
          ∃j : comparisonMassDyadicIndices V,
            nativeRadiusRowBand M.sweepRadius as (V*(2:ℝ)^(j:ℕ)) cut=1 := by
  have Hlower:=ActualThetaZeroOverlapMinimum.eventually_actual_minimum_scale_polynomial_lower_original_q
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0
  have Hlog : ∀ᶠn : ℕ in atTop,1 ≤ Real.log ((n+1:ℕ):ℝ) :=
    (tendsto_add_atTop_nat 1).eventually
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
  filter_upwards [Hlower,Hlog,eventually_gt_atTop (0:ℕ)] with n hn hlog hn0
  intro M V hxV hV1
  have hV:=M.hxs.trans_le hxV
  refine ⟨native_radius_dyadic_card_le (by exact_mod_cast (show 1 < n+1 by omega))
    hlog hV hV1 ((hn M).trans hxV),?_⟩
  intro as cut hlo
  exact native_original_radius_dyadic_cover hV cut hlo
    (M.shiftedNativeModel.R_bounds (partitionPoint 0 as cut)).2

end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_reset_paired_value_diagonal_original_q (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (p : MarkedPlacement T) (q : ℕ→RestCoordinate n→ℝ) (d : ℕ) (center : ℝ)
    (ho : MassOrdered 0 (pre++(mid++tail))) (hd : p.embed P.target=p.mark) :
    nativeResetPairedProjectionValue_original_q n T P M p q d center=0 := by
  simp only [nativeResetPairedProjectionValue_original_q,p.restRestrict_at,MarkedPlacement.restSpin,
    hd,sub_self,zero_mul]
  rw [native_star_field_disorder_field_independent _ _ _ (restWeight_pos n) (restFeature n) ho]
  simp [ClockTree.disorderExpect]

def nativeResetProjectedGammaRow_original_q (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (U : ℕ) (V : ℝ) (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) (d : ℕ) (center : ℝ) : ℝ :=
  ((T.markedAttach 0).map fun p=>p.coeff*
    fullScalarCutGamma p.tree U K (p.embed P.target) p.mark*
    (if U ≤ p.tree.splitIndex (p.embed P.target) p.mark ∧
        V ≤ M.sweepRadius (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed P.target) p.mark)) then
      nativeResetPairedProjectionValue_original_q n T P M p q d center else 0)).sum

theorem native_reset_projected_gamma_row_abs_le_original_q (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (U : ℕ) (V : ℝ) (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) (d : ℕ) (center : ℝ)
    (ho : MassOrdered 0 (pre++(mid++tail))) (ε Ai Ap p0 : ℝ) (fi fp : ℕ→ℝ)
    (hε : 0 ≤ ε) (hAi : 0 ≤ Ai) (hAp : 0 ≤ Ap) (hp0 : 0 ≤ p0)
    (hfi : ∀j,0 ≤ fi j) (hfp : ∀j,0 ≤ fp j)
    (hF : ∀p∈T.markedAttach 0,U ≤ p.tree.splitIndex (p.embed P.target) p.mark →
      V ≤ M.sweepRadius (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed P.target) p.mark)) →
      |nativeResetPairedProjectionValue_original_q n T P M p q d center| ≤
        ε*(Ai*fi (p.tree.splitIndex (p.embed P.target) p.mark)+
          Ap*fp (p.tree.splitIndex (p.embed P.target) p.mark))*p0) :
    |nativeResetProjectedGammaRow_original_q n T P M U V q K d center| ≤
      ε*(Ai*((T.markedAttach 0).map (fun p=>|p.coeff| *|fullScalarCutGamma p.tree U K (p.embed P.target) p.mark| *
        nativeTargetOffDiagonalProfile T P.target
          (fun j=>if V ≤ M.sweepRadius (partitionPoint 0 (pre++(mid++tail)) j) then fi j else 0) p)).sum+
        Ap*((T.markedAttach 0).map (fun p=>|p.coeff| *|fullScalarCutGamma p.tree U K (p.embed P.target) p.mark| *
        nativeTargetOffDiagonalProfile T P.target
          (fun j=>if V ≤ M.sweepRadius (partitionPoint 0 (pre++(mid++tail)) j) then fp j else 0) p)).sum)*p0 := by
  have H:=native_paired_list_row_abs_le (T.markedAttach 0)
    (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed P.target) p.mark)
    (fun p=>if U ≤ p.tree.splitIndex (p.embed P.target) p.mark ∧
        V ≤ M.sweepRadius (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed P.target) p.mark)) then
      nativeResetPairedProjectionValue_original_q n T P M p q d center else 0)
    (nativeTargetOffDiagonalProfile T P.target
      (fun j=>if V ≤ M.sweepRadius (partitionPoint 0 (pre++(mid++tail)) j) then fi j else 0))
    (nativeTargetOffDiagonalProfile T P.target
      (fun j=>if V ≤ M.sweepRadius (partitionPoint 0 (pre++(mid++tail)) j) then fp j else 0)) ε Ai Ap p0 (by
        intro p hp
        unfold nativeTargetOffDiagonalProfile
        by_cases hd:p.embed P.target=p.mark
        · simp only [hd,ite_true,native_reset_paired_value_diagonal_original_q n T P M p q d center ho hd]
          split_ifs <;> simp
        · simp only [hd,ite_false]
          split_ifs with hhigh hrad hrad
          · exact hF p hp hhigh.1 hhigh.2
          · exact False.elim (hrad hhigh.2)
          · simp only [abs_zero]
            exact mul_nonneg (mul_nonneg hε (add_nonneg (mul_nonneg hAi (hfi _)) (mul_nonneg hAp (hfp _)))) hp0
          · simp)
  simpa only [nativeResetProjectedGammaRow_original_q,abs_mul] using H

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_fresh_star_exterior_fourth_bound_original_q
    (Bclock Temp Cf Cmass : ℝ) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
        let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(pre mid tail : List PositiveMass),pre ++ (mid ++ tail)=as →
        ∀W : ℝ,M.xs ≤ W → partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W →
          nativeTwinStarExteriorFourth n pre mid tail 0 q 0 ≤ (C*W)^4 ∧
          nativeCommonStarExteriorFourth n pre mid tail 0 q 0 ≤ (C*W)^4 := by
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_minimum_inherited_rest_even_bound_original_q 2 (by norm_num) Bclock Temp Cf hCf hm hdelta hroom
    hcl hcu hAz hC0 hCt
  refine ⟨Cr*(1+Cmass),by positivity,?_⟩
  filter_upwards [HR,eventually_gt_atTop (0:ℕ)] with n hn hn0
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut W hW hmass
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hop : MassOrdered 0 (pre ++ (mid ++ tail)) := hcut.symm ▸ ho
  have hj : pre.length+mid.length ≤ as.length := by
    change pre.length+mid.length ≤ (finiteCutMasses us k).length
    rw [←hcut]
    simp
  have Hraw:=hk (pre.length+mid.length) hj
  norm_num only [show 2*2=4 by norm_num] at Hraw
  have hsize : M.xs+partitionPoint 0 as (pre.length+mid.length) ≤ (1+Cmass)*W := by
    linarith
  have hbase : 0 ≤ Cr*(M.xs+partitionPoint 0 as (pre.length+mid.length)) :=
    mul_nonneg hCr.le (add_nonneg M.hxs.le (partitionPoint_mem as ho _).1)
  have HB := Hraw.trans (pow_le_pow_left₀ hbase
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsize hCr.le) 4)
  rw [native_twin_star_exterior_fourth_eq_original_pair n hn0 pre mid tail hop,
    native_common_star_exterior_fourth_eq_original_pair n hn0 pre mid tail hop,hcut]
  constructor <;> simpa only [mul_assoc] using HB

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_star_subtree_projection_fourth_original_q
    (Bclock Temp Cf Cmass c₀ : ℝ) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hc₀ : 0<c₀)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀W : ℝ,M.xs ≤ W → partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W →
        ∀(T : ClockTree (Spin n) tail) (s t : T.Slot),s≠t →
        ∀r v : ℝ,0<r → M.xs ≤ v → (n:ℝ)^(-(1:ℝ)/6+m) ≤ r →
          M.sweepRadius (partitionPoint 0 as (pre.length+mid.length+T.splitIndex s t))=v →
          M.sweepRadius (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → M.z ≤ v/2 →
          c₀*W^3/Real.log (n:ℝ) ≤ laplaceComparisonStrength M.data.d M.lam v*v/
            (12*Real.log M.data.N) →
          let qs:=nativeStarSuffixClock n pre mid q
          (∫z,nativeSubtreeExteriorProjectionFourth n T s t (ClockTree.single tail) (fun _=>1)
            (ClockTree.singleSlot tail) qs qs (twinPrefixBRoot z) (twinPrefixDRoot z)
            ∂nativeTwinPrefixDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
              ((n:ℝ)/(n+1:ℕ))^4*(2*(n:ℝ)^(-eta)*savedWeightedExteriorScale r W v (C*W))^4 ∧
          (∫z,nativeSubtreeExteriorProjectionFourth n T s t (ClockTree.single tail) (fun _=>1)
            (ClockTree.singleSlot tail) qs qs (exteriorForestStarRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
              ((n:ℝ)/(n+1:ℕ))^4*(2*(n:ℝ)^(-eta)*savedWeightedExteriorScale r W v (C*W))^4 := by
  obtain ⟨C,hC,hraw⟩:=eventually_actual_minimum_inherited_fresh_star_exterior_fourth_bound_original_q
    Bclock Temp Cf Cmass hCf hCmass hm hdelta hroom hcl hcu hAz hC0 hCt
  have hlog : ∀ᶠn : ℕ in atTop,1 ≤ Real.log ((n+1:ℕ):ℝ) :=
    (tendsto_add_atTop_nat 1).eventually
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
  have hdepth := (tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  refine ⟨C,hC,?_⟩
  filter_upwards [hraw,hlog,hdepth,eventually_gt_atTop (0:ℕ),
    eventually_native_subtree_exterior_fourth_from_primitives Bclock (cl/2) c₀
      (by positivity) hc₀ hgap] with n hnraw hnlog hndepth hn hnrate
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  have hnd : 1/M.data.N ≤ M.data.d := by
    have H:=hndepth M.data.E M.data.d M.data.hE M.data.hd M.hlower
    have H' : comparisonLowerScale ((n+1:ℕ):ℝ) M.data.E M.data.d ≤ M.data.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ M.data.hd).mpr (by simpa only [pow_two] using M.hupper)
    exact H.trans H'
  have hfinemesh : ∀ᶠk : ℕ in atTop,(((k+1:ℕ):ℝ)⁻¹)/M.data.floor ≤ M.xs/16 := by
    apply ((uniformMasses_mesh_tendsto.div_const M.data.floor).eventually
      (gt_mem_nhds (show 0/M.data.floor<M.xs/16 by simpa only [zero_div] using
        (show 0<M.xs/16 from div_pos M.hxs (by norm_num))))).mono
    intro k hk
    simpa using hk.le
  filter_upwards [hnraw M hs0 hsxs hsource hxs L us hus hret hmesh,hfinemesh] with k hk hkm
  dsimp only at hk ⊢
  intro pre mid tail hcut W hW hmass T s t hst r v hr hxv hcritical hvr hlow hz hduration
  let as:=finiteCutMasses us k
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
  let qs:=nativeStarSuffixClock n pre mid q
  let steps:=nativeSampledPhysicalSteps n M.sweepBf M.sweepHf as
  let star:=pre.length+mid.length
  let high:=star+T.splitIndex s t
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hop : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ ho
  have hot:=hop.suffix_end.suffix_end
  have hhigh : high ≤ as.length := by
    have H:=T.splitIndex_le_clockLength s t
    dsimp only [high,star,as]
    rw [←hcut]
    simp only [List.length_append]
    omega
  have hv : 0<v:=M.hxs.trans_le hxv
  have hWpos : 0<W:=M.hxs.trans_le hW
  obtain ⟨start,hstart,hbefore,ha,hpos,hdur,hB,hprefix,htail,hord,d,hd,hds,hdclock⟩:=
    ActualThetaZeroOverlapMinimum.exists_observed_rest_finite_innovation_original_q n hn M hcl hnlog hnd
      as ho (by positivity : 0 ≤ (((k+1:ℕ):ℝ)⁻¹)) (finiteCutMasses_mesh us hus k)
      hv (hkm.trans (div_le_div_of_nonneg_right hxv (by norm_num))) hhigh hvr hlow hz
  have heq : clockSteps tail (fun j=>restFiniteVariance n (qs j))=steps.drop star :=
    native_star_suffix_clock_eq_drop n M.sweepBf M.sweepHf (M.sweep_bf_monotone)
      (M.sweep_hf_monotone) as pre mid tail ho hcut
  have hsplit : high-star=T.splitIndex s t:=by dsimp [high];omega
  have hpr : (clockSteps tail (fun j=>restFiniteVariance n (qs j))).take (T.splitIndex s t)=
      cutSlice steps star start++cutSlice steps start high := by
    rw [heq,←hsplit]
    exact hprefix
  have hta : (clockSteps tail (fun j=>restFiniteVariance n (qs j))).drop (T.splitIndex s t)=steps.drop high := by
    rw [heq,←hsplit]
    exact htail
  have horder : OrderedSteps (cl*v/2) (cutSlice steps start high++
      (clockSteps tail (fun j=>restFiniteVariance n (qs j))).drop (T.splitIndex s t)) := by
    rw [hta]
    exact hord
  have Hraw:=hk pre mid tail hcut W hW hmass
  let :=  nativeTwinPrefixDisorderRootLaw_probability (restWeight_pos n) (restFeature n)
    pre mid tail hop 0 q 0
  let :=  nativeExteriorForestDisorderRootLaw_probability (restWeight_pos n) (restFeature n)
    pre mid tail hop 0 q 0
  have hHtw : (∫z,(ClockTree.single (S:=Spin n) tail).expect (restWeight n) (restFeature n)
      qs (fun _=>|(1:ℝ)|^8) (twinPrefixBRoot z)
      ∂nativeTwinPrefixDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤ (1:ℝ)^8 := by
    rw [native_twin_star_fresh_hweight_eighth_eq_one n pre mid tail hop]
    norm_num
  have hHco : (∫z,(ClockTree.single (S:=Spin n) tail).expect (restWeight n) (restFeature n)
      qs (fun _=>|(1:ℝ)|^8) (exteriorForestStarRoot z)
      ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤ (1:ℝ)^8 := by
    rw [native_common_star_fresh_hweight_eighth_eq_one n pre mid tail hop]
    norm_num
  constructor
  · have H:=hnrate tail tail _ _ hot hot T s t (ClockTree.single tail) (fun _=>1)
      (ClockTree.singleSlot tail) qs qs hst (cutSlice steps start high) (cutSlice steps star start)
      (cl*v/2) _ 1 (C*W) r W v hpr (by positivity) hpos hB (by norm_num) (by positivity)
      hr hWpos hv (by ring_nf;exact le_rfl) (hduration.trans hdur) hcritical horder _
      (nativeTwinPrefixDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0)
      twinPrefixBRoot twinPrefixDRoot twinPrefixBRoot_measurable twinPrefixDRoot_measurable
      d hd hds hdclock hHtw Hraw.1
    simpa only [mul_one] using H
  · have H:=hnrate tail tail _ _ hot hot T s t (ClockTree.single tail) (fun _=>1)
      (ClockTree.singleSlot tail) qs qs hst (cutSlice steps start high) (cutSlice steps star start)
      (cl*v/2) _ 1 (C*W) r W v hpr (by positivity) hpos hB (by norm_num) (by positivity)
      hr hWpos hv (by ring_nf;exact le_rfl) (hduration.trans hdur) hcritical horder _
      (nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0)
      exteriorForestStarRoot exteriorForestStarRoot departedAnchorExteriorRoot_measurable
      departedAnchorExteriorRoot_measurable d hd hds hdclock hHco Hraw.2
    simpa only [mul_one] using H

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_calibrated_minimum_inherited_star_subtree_projection_fourth_original_q
    (Bclock Temp Cf Cmass Ccal : ℝ) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcal : 1 ≤ Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0<delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0 ≤ Az) (hC0 : 0<C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.data.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
          partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W →
        ∀(T : ClockTree (Spin n) tail) (s t : T.Slot),s≠t →
        ∀v : ℝ,W ≤ v →
          M.sweepRadius (partitionPoint 0 as (pre.length+mid.length+T.splitIndex s t))=v →
          M.sweepRadius (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → M.z ≤ v/2 →
          let qs:=nativeStarSuffixClock n pre mid q
          (∫z,nativeSubtreeExteriorProjectionFourth n T s t (ClockTree.single tail) (fun _=>1)
            (ClockTree.singleSlot tail) qs qs (twinPrefixBRoot z) (twinPrefixDRoot z)
            ∂nativeTwinPrefixDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
              ((n:ℝ)/(n+1:ℕ))^4*(C*(n:ℝ)^(-eta)*savedProjectedScale M.xs W v)^4 ∧
          (∫z,nativeSubtreeExteriorProjectionFourth n T s t (ClockTree.single tail) (fun _=>1)
            (ClockTree.singleSlot tail) qs qs (exteriorForestStarRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
              ((n:ℝ)/(n+1:ℕ))^4*(C*(n:ℝ)^(-eta)*savedProjectedScale M.xs W v)^4 := by
  have hCcal0 : 0<Ccal:=zero_lt_one.trans_le hCcal
  obtain ⟨Cr,hCr,H⟩:=eventually_actual_minimum_inherited_star_subtree_projection_fourth_original_q
    Bclock Temp Cf Cmass (1/(24*Ccal^3)) hCf hCmass (by positivity)
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨2*(2*C0)^3*Real.sqrt Cr,by positivity,?_⟩
  filter_upwards [H,eventually_ge_atTop (2:ℕ)] with n hn hn2
  intro M hs0 hsxs hsource hxs hcompare L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut hmass T s t hst v hWv hvr hlow hz
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
  have hW : 0<W:=M.hxs.trans_le (le_max_left _ _)
  have hv : 0<v:=hW.trans_le hWv
  have hv1 : v ≤ 1 := by
    rw [←hvr]
    exact (M.shiftedNativeModel.R_bounds _).2
  obtain ⟨hcritical,hduration⟩:=native_minimum_observed_calibration_scales_original_q
    M hn2 hm.le hC0 hCcal hcompare hWv hv1
  have Hfour:=hk pre mid tail hcut W (le_max_left _ _) hmass T s t hst
    ((2*C0)*M.xs) v (by exact mul_pos (by positivity) M.hxs)
    ((le_max_left _ _).trans hWv) hcritical hvr hlow hz hduration
  have he : 2*(n:ℝ)^(-eta)*savedWeightedExteriorScale ((2*C0)*M.xs) W v (Cr*W)=
      (2*(2*C0)^3*Real.sqrt Cr)*(n:ℝ)^(-eta)*savedProjectedScale M.xs W v := by
    rw [savedWeightedExteriorScale_scaled_raw hW hv hCr.le]
    ring
  simpa only [he] using Hfour

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_exterior_eighth_original_q
    (a : ℕ) (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail)))
          (G : ActualNaturalBoundaryShape n a T) (f : Fin a → NativeSourceFactorForm)
          (initial : Finset (Fin a)) (x W : ℝ),
          M.xs ≤ x → x ≤ W → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(s : T.cavityLeft.Slot)
          (E : NativeCanonicalExteriorSource n a pre mid tail T s (G.canonicalOriginalQSource M f) 0 q 0),
          (∫z,nativeExteriorForestMean E.Ei E.Es (restWeight n) (restFeature n)
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
            (fun η ζ=>|E.H η ζ|^8) (exteriorForestIRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
            (C^a*sourceMonomialScale x W initial)^8 := by
  by_cases ha : a=0
  · subst a
    refine ⟨1,by norm_num,Filter.Eventually.of_forall ?_⟩
    intro n M hs0 hsxs hsource hxs L us hus hret hmesh
    apply Filter.Eventually.of_forall
    intro k
    dsimp only
    intro pre mid tail hcut T G f initial x W hxsx hxW hmass s E
    rw [←E.exterior_law (fun y=>|y|^8)]
    have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
    have hI : initial=∅:=Subsingleton.elim _ _
    simp [ActualNaturalBoundaryShape.restProduct,sourceMonomialScale,hI,
      T.cavityLeft.disorderExpect_one (restWeight_pos n) (restFeature n) ho]
  · obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_canonical_rest_even_moment_original_q
      a 4 (by omega) (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCm
      hm hdelta hroom hcl hcu hAz hC0 hCt
    refine ⟨C,hC,?_⟩
    filter_upwards [H] with n hn
    intro M hs0 hsxs hsource hxs L us hus hret hmesh
    filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with k hk
    dsimp only at hk ⊢
    intro pre mid tail hcut T G f initial x W hxsx hxW hmass s E
    rw [←E.exterior_law (fun y=>|y|^8)]
    have HK (bs : List PositiveMass) (he : bs=finiteCutMasses us k)
        (V : ClockTree (Spin n×Bool) bs) (A : ActualNaturalBoundaryShape n a V)
        (hf : Fin a → NativeSourceFactorForm) (I : Finset (Fin a))
        (hx : M.xs ≤ x) (hW : x ≤ W)
        (hA : ∀e,A.sourceLowMass e ≤ Cmass*sourceFactorScale x W I e) :
        V.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0
          (fun j=>Sum.elim (fun _=>(M.sweepBf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
            (fun _=>(M.sweepHf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)))
          (fun σ=>|(A.canonicalOriginalQSource M hf).restProduct σ|^8) 0 ≤
          (C^a*sourceMonomialScale x W I)^8 := by
      subst bs
      exact hk V A hf I x W hx hW hA
    exact HK (pre++(mid++tail)) hcut T G f initial hxsx hxW hmass

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_i_exterior_fourth_bound_original_q
    (Bclock Temp Cf : ℝ) (hCf : 0 ≤ Cf) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀(Ei : ClockTree (Spin n) (mid++tail)) (e : Ei.Slot),
          (∫z,(Ei.fork Ei).expect (restWeight n) (restFeature n)
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
            (fun η=>|deletedOverlap n (joinSpin (Ei.atSlot η.1 e,false))
              (joinSpin (Ei.atSlot η.2 e,false))|^4) (exteriorForestIRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
            (C*(M.xs+partitionPoint 0 as pre.length))^4 := by
  obtain ⟨C,hC,HR⟩:=eventually_actual_minimum_inherited_rest_even_bound_original_q
    (D:=D) 2 (by norm_num) Bclock Temp Cf hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HR] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut Ei e
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
    (fun _=>(M.sweepBf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
    (fun _=>(M.sweepHf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
  rw [native_common_i_pair_marginal n pre mid tail ho Ei e 0 q
    (fun σ τ=>|deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))|^4) 0]
  apply (native_pair_deleted_even_le_ordered n 2 ho pre.length 0 _ 0).trans
  have hj : pre.length ≤ (finiteCutMasses us k).length := by
    rw [←hcut]
    simp only [List.length_append]
    omega
  have HK (bs : List PositiveMass) (hbs : bs=finiteCutMasses us k) :
      (ClockTree.pairClock bs pre.length).disorderExpect (restWeight n) (restFeature n) 0 q
        (fun σ=>|orderedOverlap n (ClockTree.pairSpin bs pre.length σ).1
          (ClockTree.pairSpin bs pre.length σ).2|^4) 0 ≤
        (C*(M.xs+partitionPoint 0 (finiteCutMasses us k) pre.length))^4 := by
    subst bs
    simpa only [q,show 2*2=4 by norm_num] using hk pre.length hj
  exact HK (pre++(mid++tail)) hcut

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_two_level_projection_fourth_original_q
    (Bclock Temp Cf Ccal : ℝ) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.data.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀(Ei : ClockTree (Spin n) (mid++tail)) (Es T : ClockTree (Spin n) tail)
          (H : Ei.Assignment → Es.Assignment → ℝ) (e : Ei.Slot) (s t : T.Slot),s ≠ t →
        ∀v : ℝ,W ≤ v →
          M.sweepRadius (partitionPoint 0 as (pre.length+mid.length+T.splitIndex s t))=v →
          M.sweepRadius (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → M.z ≤ v/2 →
          let qi:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j)
          let qs:=nativeStarSuffixClock n pre mid q
          (∫z,nativeTwoLevelProjectionFourth n Ei Es T H e s t qi qs qs
            (exteriorForestIRoot z) (exteriorForestStarRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
            (C*(n:ℝ)^(-eta)*savedWeightedExteriorScale M.xs W v
              (M.xs+partitionPoint 0 as pre.length))^4*
              Real.sqrt (∫z,nativeExteriorForestMean Ei Es (restWeight n) (restFeature n) qi qs
                (fun η ζ=>|H η ζ|^8) (exteriorForestIRoot z) (exteriorForestStarRoot z)
                ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) := by
  have hCcal0 : 0 < Ccal:=zero_lt_one.trans_le hCcal
  obtain ⟨Cr,hCr,Hraw⟩:=eventually_actual_minimum_inherited_i_exterior_fourth_bound_original_q
    (D:=D) Bclock Temp Cf hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have hlog : ∀ᶠn : ℕ in atTop,1 ≤ Real.log ((n+1:ℕ):ℝ) :=
    (tendsto_add_atTop_nat 1).eventually
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
  have hdepth := (tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  refine ⟨2*(2*C0)^3*Real.sqrt Cr,by positivity,?_⟩
  filter_upwards [Hraw,hlog,hdepth,eventually_ge_atTop (2:ℕ),
    eventually_native_two_level_fourth_from_primitives Bclock (cl/2) (1/(24*Ccal^3))
      (by positivity) (by positivity) hgap] with n hnraw hnlog hndepth hn2 hnrate
  intro M hs0 hsxs hsource hxs hcompare L us hus hret hmesh
  have hn : 0 < n := by omega
  have hnd : 1/M.data.N ≤ M.data.d := by
    have H:=hndepth M.data.E M.data.d M.data.hE M.data.hd M.hlower
    have H' : comparisonLowerScale ((n+1:ℕ):ℝ) M.data.E M.data.d ≤ M.data.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ M.data.hd).mpr (by simpa only [pow_two] using M.hupper)
    exact H.trans H'
  have hfinemesh : ∀ᶠk : ℕ in atTop,(((k+1:ℕ):ℝ)⁻¹)/M.data.floor ≤ M.xs/16 := by
    apply ((uniformMasses_mesh_tendsto.div_const M.data.floor).eventually
      (gt_mem_nhds (show 0/M.data.floor < M.xs/16 by simpa only [zero_div] using
        (show 0 < M.xs/16 from div_pos M.hxs (by norm_num))))).mono
    intro k hk
    simpa using hk.le
  filter_upwards [hnraw M hs0 hsxs hsource hxs L us hus hret hmesh,hfinemesh] with k hk hkm
  dsimp only at hk ⊢
  intro pre mid tail hcut Ei Es T H e s t hst v hWv hvr hlow hz
  let as:=finiteCutMasses us k
  let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
    (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
  let qi:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j)
  let qs:=nativeStarSuffixClock n pre mid q
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
  let steps:=nativeSampledPhysicalSteps n M.sweepBf M.sweepHf as
  let star:=pre.length+mid.length
  let high:=star+T.splitIndex s t
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hop : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ ho
  have hot:=hop.suffix_end.suffix_end
  have hhigh : high ≤ as.length := by
    have HH:=T.splitIndex_le_clockLength s t
    dsimp only [high,star,as]
    rw [←hcut]
    simp only [List.length_append]
    omega
  have hW : 0 < W:=M.hxs.trans_le (le_max_left _ _)
  have hxv : M.xs ≤ v:=(le_max_left _ _).trans hWv
  have hv : 0 < v:=M.hxs.trans_le hxv
  have hv1 : v ≤ 1 := by
    rw [←hvr]
    exact (M.shiftedNativeModel.R_bounds _).2
  obtain ⟨hcritical,hduration⟩:=native_minimum_observed_calibration_scales_original_q
    M hn2 hm.le hC0 hCcal hcompare hWv hv1
  obtain ⟨start,hstart,hbefore,ha,hpos,hdur,hB,hprefix,htail,hord,d,hd,hds,hdclock⟩:=
    ActualThetaZeroOverlapMinimum.exists_observed_rest_finite_innovation_original_q n hn M hcl hnlog hnd
      as ho (by positivity : 0 ≤ (((k+1:ℕ):ℝ)⁻¹)) (finiteCutMasses_mesh us hus k)
      hv (hkm.trans (div_le_div_of_nonneg_right hxv (by norm_num))) hhigh hvr hlow hz
  have heq : clockSteps tail (fun j=>restFiniteVariance n (qs j))=steps.drop star :=
    native_star_suffix_clock_eq_drop n M.sweepBf M.sweepHf (M.sweep_bf_monotone)
      (M.sweep_hf_monotone) as pre mid tail ho hcut
  have hsplit : high-star=T.splitIndex s t:=by dsimp [high];omega
  have hpr : (clockSteps tail (fun j=>restFiniteVariance n (qs j))).take (T.splitIndex s t)=
      cutSlice steps star start++cutSlice steps start high := by
    rw [heq,←hsplit]
    exact hprefix
  have hta : (clockSteps tail (fun j=>restFiniteVariance n (qs j))).drop (T.splitIndex s t)=steps.drop high := by
    rw [heq,←hsplit]
    exact htail
  have horder : OrderedSteps (cl*v/2) (cutSlice steps start high++
      (clockSteps tail (fun j=>restFiniteVariance n (qs j))).drop (T.splitIndex s t)) := by
    rw [hta]
    exact hord
  have hsipos : 0 < Cr*(M.xs+partitionPoint 0 as pre.length) :=
    mul_pos hCr (add_pos_of_pos_of_nonneg M.hxs (partitionPoint_mem as ho pre.length).1)
  let :=  nativeExteriorForestDisorderRootLaw_probability (restWeight_pos n) (restFeature n)
    pre mid tail hop 0 q 0
  have HF:=hnrate (mid++tail) tail tail _ _ _ hop.suffix_end hot hot Ei Es T H e s t hst qi qs qs
    (cutSlice steps start high) (cutSlice steps star start) (cl*v/2) _
    (Cr*(M.xs+partitionPoint 0 as pre.length)) ((2*C0)*M.xs) W v hpr
    (by positivity) hpos hB hsipos.le (by exact mul_pos (by positivity) M.hxs) hW hv
    (by ring_nf;exact le_rfl) (hduration.trans hdur) hcritical horder _
    (nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0)
    exteriorForestIRoot exteriorForestStarRoot exteriorForestStarRoot
    departedAnchorTargetRoot_measurable departedAnchorExteriorRoot_measurable departedAnchorExteriorRoot_measurable
    d hd hds hdclock (hk pre mid tail hcut Ei e)
  have he : 2*(n:ℝ)^(-eta)*savedWeightedExteriorScale ((2*C0)*M.xs) W v
      (Cr*(M.xs+partitionPoint 0 as pre.length)) =
      (2*(2*C0)^3*Real.sqrt Cr)*(n:ℝ)^(-eta)*savedWeightedExteriorScale M.xs W v
        (M.xs+partitionPoint 0 as pre.length) := by
    rw [savedWeightedExteriorScale_scaled_incoming hCr.le]
    ring
  simpa only [he] using HF

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_two_level_projection_fourth_original_q
    (a : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ) (hCf : 0 ≤ Cf) (hTemp : 0 ≤ Temp)
    (hCm : 0 ≤ Cmass) (hCcal : 1 ≤ Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.data.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail)))
          (G : ActualNaturalBoundaryShape n a T) (f : Fin a → NativeSourceFactorForm)
          (initial : Finset (Fin a)) (x : ℝ),
          M.xs ≤ x → x ≤ W → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(s : T.cavityLeft.Slot)
          (E : NativeCanonicalExteriorSource n a pre mid tail T s (G.canonicalOriginalQSource M f) 0 q 0)
          (e : E.Ei.Slot) (t : E.D.Slot),E.target ≠ t →
        ∀v : ℝ,W ≤ v →
          M.sweepRadius (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
          M.sweepRadius (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → M.z ≤ v/2 →
          let qi:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j)
          let qs:=nativeStarSuffixClock n pre mid q
          (∫z,nativeTwoLevelProjectionFourth n E.Ei E.Es E.D E.H e E.target t qi qs qs
            (exteriorForestIRoot z) (exteriorForestStarRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
            (Cp*(n:ℝ)^(-eta)*savedWeightedExteriorScale M.xs W v
              (M.xs+partitionPoint 0 as pre.length)*(Ch^a*sourceMonomialScale x W initial))^4 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_two_level_projection_fourth_original_q
    (D:=D) Bclock Temp Cf Ccal hCf hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Ch,hCh,HH⟩:=eventually_actual_minimum_inherited_canonical_exterior_eighth_original_q
    (D:=D) a Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,Ch,hCh,?_⟩
  filter_upwards [HP,HH] with n hp hh
  intro M hs0 hsxs hsource hxs hcompare L us hus hret hmesh
  filter_upwards [hp M hs0 hsxs hsource hxs hcompare L us hus hret hmesh,
    hh M hs0 hsxs hsource hxs L us hus hret hmesh] with k hkP hkH
  dsimp only at hkP hkH ⊢
  intro pre mid tail hcut T G f initial x hxsx hxW hmass s E e t hst v hWv hvr hstar hz
  have Hproj:=hkP pre mid tail hcut E.Ei E.Es E.D E.H e E.target t hst v hWv hvr hstar hz
  have Hmoment:=hkH pre mid tail hcut T G f initial x _ hxsx hxW hmass s E
  have Hsqrt:=Real.sqrt_le_sqrt Hmoment
  have hsquare (p : ℝ) : Real.sqrt (p^8)=p^4 := by
    rw [show p^8=(p^4)^2 by ring,Real.sqrt_sq (by positivity)]
  rw [hsquare] at Hsqrt
  have HB:=mul_le_mul_of_nonneg_left Hsqrt
    (show 0 ≤ (Cp*(n:ℝ)^(-eta)*savedWeightedExteriorScale M.xs
      (max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))) v
      (M.xs+partitionPoint 0 (finiteCutMasses us k) pre.length))^4 by positivity)
  calc
    _ ≤ _ := Hproj
    _ ≤ _ := HB
    _ = _ := by ring

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_star_exterior_fourth_bound_original_q
    (Bclock Temp Cf : ℝ) (hCf : 0 ≤ Cf) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀(Es : ClockTree (Spin n) tail) (e : Es.Slot),
          (∫z,(Es.fork Es).expect (restWeight n) (restFeature n)
            (nativeStarSuffixClock n pre mid q)
            (fun η=>|deletedOverlap n (joinSpin (Es.atSlot η.1 e,false))
              (joinSpin (Es.atSlot η.2 e,false))|^4) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
            (C*(M.xs+partitionPoint 0 as (pre.length+mid.length)))^4 := by
  obtain ⟨C,hC,HR⟩:=eventually_actual_minimum_inherited_rest_even_bound_original_q
    (D:=D) 2 (by norm_num) Bclock Temp Cf hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HR] with n hn
  intro M hs0 hsxs hsource hxs L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut Es e
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
    (fun _=>(M.sweepBf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
    (fun _=>(M.sweepHf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
  unfold nativeStarSuffixClock
  rw [native_common_star_pair_marginal n pre mid tail ho Es e 0 q
    (fun σ τ=>|deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))|^4) 0]
  apply (native_pair_deleted_even_le_ordered n 2 ho (pre.length+mid.length) 0 _ 0).trans
  have hj : pre.length+mid.length ≤ (finiteCutMasses us k).length := by
    rw [←hcut]
    simp only [List.length_append]
    omega
  have HK (bs : List PositiveMass) (hbs : bs=finiteCutMasses us k) :
      (ClockTree.pairClock bs (pre.length+mid.length)).disorderExpect (restWeight n) (restFeature n) 0 q
        (fun σ=>|orderedOverlap n (ClockTree.pairSpin bs (pre.length+mid.length) σ).1
          (ClockTree.pairSpin bs (pre.length+mid.length) σ).2|^4) 0 ≤
        (C*(M.xs+partitionPoint 0 (finiteCutMasses us k) (pre.length+mid.length)))^4 := by
    subst bs
    simpa only [q,show 2*2=4 by norm_num] using hk (pre.length+mid.length) hj
  exact HK (pre++(mid++tail)) hcut

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_star_two_level_projection_fourth_original_q
    (Bclock Temp Cf Ccal : ℝ) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.data.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀(Ei : ClockTree (Spin n) (mid++tail)) (Es T : ClockTree (Spin n) tail)
          (H : Ei.Assignment → Es.Assignment → ℝ) (e : Es.Slot) (s t : T.Slot),s ≠ t →
        ∀v : ℝ,W ≤ v →
          M.sweepRadius (partitionPoint 0 as (pre.length+mid.length+T.splitIndex s t))=v →
          M.sweepRadius (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → M.z ≤ v/2 →
          let qi:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j)
          let qs:=nativeStarSuffixClock n pre mid q
          (∫z,nativeTwoLevelProjectionFourth n Es Ei T (fun ζ η=>H η ζ) e s t qs qi qs
            (exteriorForestStarRoot z) (exteriorForestIRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
            (C*(n:ℝ)^(-eta)*savedWeightedExteriorScale M.xs W v
              (M.xs+partitionPoint 0 as (pre.length+mid.length)))^4*
              Real.sqrt (∫z,nativeExteriorForestMean Ei Es (restWeight n) (restFeature n) qi qs
                (fun η ζ=>|H η ζ|^8) (exteriorForestIRoot z) (exteriorForestStarRoot z)
                ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) := by
  have hCcal0 : 0 < Ccal:=zero_lt_one.trans_le hCcal
  obtain ⟨Cr,hCr,Hraw⟩:=eventually_actual_minimum_inherited_star_exterior_fourth_bound_original_q
    (D:=D) Bclock Temp Cf hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have hlog : ∀ᶠn : ℕ in atTop,1 ≤ Real.log ((n+1:ℕ):ℝ) :=
    (tendsto_add_atTop_nat 1).eventually
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
  have hdepth := (tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  refine ⟨2*(2*C0)^3*Real.sqrt Cr,by positivity,?_⟩
  filter_upwards [Hraw,hlog,hdepth,eventually_ge_atTop (2:ℕ),
    eventually_native_two_level_fourth_from_primitives Bclock (cl/2) (1/(24*Ccal^3))
      (by positivity) (by positivity) hgap] with n hnraw hnlog hndepth hn2 hnrate
  intro M hs0 hsxs hsource hxs hcompare L us hus hret hmesh
  have hn : 0 < n := by omega
  have hnd : 1/M.data.N ≤ M.data.d := by
    have H:=hndepth M.data.E M.data.d M.data.hE M.data.hd M.hlower
    have H' : comparisonLowerScale ((n+1:ℕ):ℝ) M.data.E M.data.d ≤ M.data.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ M.data.hd).mpr (by simpa only [pow_two] using M.hupper)
    exact H.trans H'
  have hfinemesh : ∀ᶠk : ℕ in atTop,(((k+1:ℕ):ℝ)⁻¹)/M.data.floor ≤ M.xs/16 := by
    apply ((uniformMasses_mesh_tendsto.div_const M.data.floor).eventually
      (gt_mem_nhds (show 0/M.data.floor < M.xs/16 by simpa only [zero_div] using
        (show 0 < M.xs/16 from div_pos M.hxs (by norm_num))))).mono
    intro k hk
    simpa using hk.le
  filter_upwards [hnraw M hs0 hsxs hsource hxs L us hus hret hmesh,hfinemesh] with k hk hkm
  dsimp only at hk ⊢
  intro pre mid tail hcut Ei Es T H e s t hst v hWv hvr hlow hz
  let as:=finiteCutMasses us k
  let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
    (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
  let qi:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j)
  let qs:=nativeStarSuffixClock n pre mid q
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
  let steps:=nativeSampledPhysicalSteps n M.sweepBf M.sweepHf as
  let star:=pre.length+mid.length
  let high:=star+T.splitIndex s t
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hop : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ ho
  have hot:=hop.suffix_end.suffix_end
  have hhigh : high ≤ as.length := by
    have HH:=T.splitIndex_le_clockLength s t
    dsimp only [high,star,as]
    rw [←hcut]
    simp only [List.length_append]
    omega
  have hW : 0 < W:=M.hxs.trans_le (le_max_left _ _)
  have hxv : M.xs ≤ v:=(le_max_left _ _).trans hWv
  have hv : 0 < v:=M.hxs.trans_le hxv
  have hv1 : v ≤ 1 := by
    rw [←hvr]
    exact (M.shiftedNativeModel.R_bounds _).2
  obtain ⟨hcritical,hduration⟩:=native_minimum_observed_calibration_scales_original_q
    M hn2 hm.le hC0 hCcal hcompare hWv hv1
  obtain ⟨start,hstart,hbefore,ha,hpos,hdur,hB,hprefix,htail,hord,d,hd,hds,hdclock⟩:=
    ActualThetaZeroOverlapMinimum.exists_observed_rest_finite_innovation_original_q n hn M hcl hnlog hnd
      as ho (by positivity : 0 ≤ (((k+1:ℕ):ℝ)⁻¹)) (finiteCutMasses_mesh us hus k)
      hv (hkm.trans (div_le_div_of_nonneg_right hxv (by norm_num))) hhigh hvr hlow hz
  have heq : clockSteps tail (fun j=>restFiniteVariance n (qs j))=steps.drop star :=
    native_star_suffix_clock_eq_drop n M.sweepBf M.sweepHf (M.sweep_bf_monotone)
      (M.sweep_hf_monotone) as pre mid tail ho hcut
  have hsplit : high-star=T.splitIndex s t:=by dsimp [high];omega
  have hpr : (clockSteps tail (fun j=>restFiniteVariance n (qs j))).take (T.splitIndex s t)=
      cutSlice steps star start++cutSlice steps start high := by
    rw [heq,←hsplit]
    exact hprefix
  have hta : (clockSteps tail (fun j=>restFiniteVariance n (qs j))).drop (T.splitIndex s t)=steps.drop high := by
    rw [heq,←hsplit]
    exact htail
  have horder : OrderedSteps (cl*v/2) (cutSlice steps start high++
      (clockSteps tail (fun j=>restFiniteVariance n (qs j))).drop (T.splitIndex s t)) := by
    rw [hta]
    exact hord
  have hsipos : 0 < Cr*(M.xs+partitionPoint 0 as (pre.length+mid.length)) :=
    mul_pos hCr (add_pos_of_pos_of_nonneg M.hxs (partitionPoint_mem as ho (pre.length+mid.length)).1)
  let := nativeExteriorForestDisorderRootLaw_probability (restWeight_pos n) (restFeature n)
    pre mid tail hop 0 q 0
  have HF:=hnrate tail (mid++tail) tail _ _ _ hot hop.suffix_end hot Es Ei T (fun ζ η=>H η ζ) e s t hst qs qi qs
    (cutSlice steps start high) (cutSlice steps star start) (cl*v/2) _
    (Cr*(M.xs+partitionPoint 0 as (pre.length+mid.length))) ((2*C0)*M.xs) W v hpr
    (by positivity) hpos hB hsipos.le (by exact mul_pos (by positivity) M.hxs) hW hv
    (by ring_nf;exact le_rfl) (hduration.trans hdur) hcritical horder _
    (nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0)
    exteriorForestStarRoot exteriorForestIRoot exteriorForestStarRoot
    departedAnchorExteriorRoot_measurable departedAnchorTargetRoot_measurable departedAnchorExteriorRoot_measurable
    d hd hds hdclock (hk pre mid tail hcut Es e)
  have he : 2*(n:ℝ)^(-eta)*savedWeightedExteriorScale ((2*C0)*M.xs) W v
      (Cr*(M.xs+partitionPoint 0 as (pre.length+mid.length))) =
      (2*(2*C0)^3*Real.sqrt Cr)*(n:ℝ)^(-eta)*savedWeightedExteriorScale M.xs W v
        (M.xs+partitionPoint 0 as (pre.length+mid.length)) := by
    rw [savedWeightedExteriorScale_scaled_star_incoming hCr.le]
    ring
  have Hmean :
      (∫z,nativeExteriorForestMean Es Ei (restWeight n) (restFeature n) qs qi
        (fun ζ η=>|H η ζ|^8) (exteriorForestStarRoot z) (exteriorForestIRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0)=
      (∫z,nativeExteriorForestMean Ei Es (restWeight n) (restFeature n) qi qs
        (fun η ζ=>|H η ζ|^8) (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0):=by
    apply integral_congr_ae
    exact Eventually.of_forall fun z=>native_exterior_forest_mean_star_flip n Ei Es
      (fun η ζ=>|H η ζ|^8) qi qs (exteriorForestIRoot z) (exteriorForestStarRoot z)
  rw [Hmean] at HF
  simpa only [he] using HF

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_star_two_level_projection_fourth_original_q
    (a : ℕ) (Bclock Temp Cf Cmass Ccal : ℝ) (hCf : 0 ≤ Cf) (hTemp : 0 ≤ Temp)
    (hCm : 0 ≤ Cmass) (hCcal : 1 ≤ Ccal)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.data.d M.lam M.xs →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail)))
          (G : ActualNaturalBoundaryShape n a T) (f : Fin a → NativeSourceFactorForm)
          (initial : Finset (Fin a)) (x : ℝ),
          M.xs ≤ x → x ≤ W → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(s : T.cavityLeft.Slot)
          (E : NativeCanonicalExteriorSource n a pre mid tail T s (G.canonicalOriginalQSource M f) 0 q 0)
          (e : E.Es.Slot) (t : E.D.Slot),E.target ≠ t →
        ∀v : ℝ,W ≤ v →
          M.sweepRadius (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
          M.sweepRadius (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → M.z ≤ v/2 →
          let qi:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j)
          let qs:=nativeStarSuffixClock n pre mid q
          (∫z,nativeTwoLevelProjectionFourth n E.Es E.Ei E.D (fun ζ η=>E.H η ζ) e E.target t qs qi qs
            (exteriorForestStarRoot z) (exteriorForestIRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
            (Cp*(n:ℝ)^(-eta)*savedWeightedExteriorScale M.xs W v
              (M.xs+partitionPoint 0 as (pre.length+mid.length))*(Ch^a*sourceMonomialScale x W initial))^4 := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_star_two_level_projection_fourth_original_q
    (D:=D) Bclock Temp Cf Ccal hCf hCcal hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  obtain ⟨Ch,hCh,HH⟩:=eventually_actual_minimum_inherited_canonical_exterior_eighth_original_q
    (D:=D) a Bclock Temp Cf Cmass hTemp hCf hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,Ch,hCh,?_⟩
  filter_upwards [HP,HH] with n hp hh
  intro M hs0 hsxs hsource hxs hcompare L us hus hret hmesh
  filter_upwards [hp M hs0 hsxs hsource hxs hcompare L us hus hret hmesh,
    hh M hs0 hsxs hsource hxs L us hus hret hmesh] with k hkP hkH
  dsimp only at hkP hkH ⊢
  intro pre mid tail hcut T G f initial x hxsx hxW hmass s E e t hst v hWv hvr hstar hz
  have Hproj:=hkP pre mid tail hcut E.Ei E.Es E.D E.H e E.target t hst v hWv hvr hstar hz
  have Hmoment:=hkH pre mid tail hcut T G f initial x _ hxsx hxW hmass s E
  have Hsqrt:=Real.sqrt_le_sqrt Hmoment
  have hsquare (p : ℝ) : Real.sqrt (p^8)=p^4 := by
    rw [show p^8=(p^4)^2 by ring,Real.sqrt_sq (by positivity)]
  rw [hsquare] at Hsqrt
  have HB:=mul_le_mul_of_nonneg_left Hsqrt
    (show 0 ≤ (Cp*(n:ℝ)^(-eta)*savedWeightedExteriorScale M.xs
      (max M.xs (Real.sqrt (laplaceComparisonStrength M.data.d M.lam M.xs))) v
      (M.xs+partitionPoint 0 (finiteCutMasses us k) (pre.length+mid.length)))^4 by positivity)
  calc
    _ ≤ _ := Hproj
    _ ≤ _ := HB
    _ = _ := by ring

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_reset_projected_gamma_row_high_form_original_q
    (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (U : ℕ) (V : ℝ) (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) (d : ℕ) (center : ℝ)
    (ho : MassOrdered 0 (pre++(mid++tail))) (hU : pre.length+mid.length < U) :
    nativeResetProjectedGammaRow_original_q n T P M U V q K d center=
      ((nativeHighMarkedRows T P.target (pre.length+mid.length) 0).map fun p=>
        p.coeff*nativeProjectedGammaTopology (pre++(mid++tail)) U V M.sweepRadius K
          (p.tree.splitIndex (p.embed P.target) p.mark) (decide (p.mark=p.embed P.target))*
        nativeResetPairedProjectionValue_original_q n T P M p q d center).sum := by
  unfold nativeResetProjectedGammaRow_original_q
  have HF:=native_list_sum_filter_of_zero (T.markedAttach 0)
    (fun p=>decide (pre.length+mid.length < p.tree.splitIndex (p.embed P.target) p.mark))
    (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed P.target) p.mark*
      (if U ≤ p.tree.splitIndex (p.embed P.target) p.mark ∧
          V ≤ M.sweepRadius (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed P.target) p.mark)) then
        nativeResetPairedProjectionValue_original_q n T P M p q d center else 0)) (by
      intro p _ hp
      have hn:¬pre.length+mid.length < p.tree.splitIndex (p.embed P.target) p.mark:=of_decide_eq_false hp
      have hx:¬U ≤ p.tree.splitIndex (p.embed P.target) p.mark:=fun h=>hn (hU.trans_le h)
      simp [hx])
  rw [←HF,←nativeHighMarkedRows_eq_filter]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  rw [fullScalarCutGamma_marked_eq_topology T ho]
  simp only [nativeProjectedGammaTopology,MarkedPlacement.hit,decide_eq_true_eq]
  split_ifs <;> ring

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 30000000
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_projected_gamma_row_spine_original_q
    (n : ℕ) {pre mid tail : List PositiveMass}
    {A T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T}
    (h : NativeProjectionSpine base (pre.length+mid.length) P)
    (hA : NativeTargetStarSingleton A base.target (pre.length+mid.length))
    (hT : NativeTargetStarSingleton T P.target (pre.length+mid.length))
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (U : ℕ) (V : ℝ) (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ)
    (ho : MassOrdered 0 (pre++(mid++tail))) (hU : pre.length+mid.length < U) :
    let center:=pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1))
      (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length))
    nativeResetProjectedGammaRow_original_q n T P M U V q K 0 center=
      nativeResetProjectedGammaRow_original_q n A base M U V q K h.toothCount center := by
  dsimp only
  let R:=fun s t=>deletedOverlap n (joinSpin (s,false)) (joinSpin (t,false))
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1))
    (partitionPoint 0 (pre++(mid++tail)) j)
  let Y:=nativeStarCenteredProjection n tail (nativeStarSuffixClock n pre mid q) (C (pre.length+mid.length))
  have HY (u : Spin n) : BddSmooth 0 (fun y=>Y y u):=
    native_star_centered_projection_smooth n ho.suffix_end.suffix_end _ _ u 0
  have HH:=h.paired_signed_disorder_row hA hT (restWeight_pos n) (restFeature n) 0 ho R C 0 q
    (fun y σ u=>Y y u-Y y (A.cavityLeft.atSlot σ (A.cavityLeftSlot base.target)))
    (fun σ u=>(HY u).sub (HY _)) 0
    (nativeProjectedGammaTopology (pre++(mid++tail)) U V M.sweepRadius K)
  have HF (y : RestCoordinate n→ℝ) (u : Spin n) :
      nativeStarPairFactor (restWeight n) (restFeature n) (pre++(mid++tail))
        (pre.length+mid.length) (cumulativeIncrements (q 0) (fun j=>q (j+1)))
        (fun u v=>R u v-C (pre.length+mid.length)) y u=Y y u :=
    nativeStarPairFactor_two_level_centered_projection n pre mid tail _ _ y u
  simp only [HF,h.restTargetRead] at HH
  rw [native_reset_projected_gamma_row_high_form_original_q n T P M U V q K 0 _ ho hU,
    native_reset_projected_gamma_row_high_form_original_q n A base M U V q K h.toothCount _ ho hU]
  simpa only [nativeResetPairedProjectionValue_original_q,pow_zero,mul_one,
    R,C,Y] using HH

end OAI.SKFluctuations.Cavity

set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_source_base_fourth_original_q
    (a : ℕ) (Bclock Temp Cf Cmass : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s≤1/4 → M.data.s≤M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.sweepBf (partitionPoint 0 as j):ℝ)) (fun _=>(M.sweepHf (partitionPoint 0 as j):ℝ))
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail)))
          (G : ActualNaturalBoundaryShape n a T) (forms : Fin a → NativeSourceFactorForm)
          (initial : Finset (Fin a)) (x W : ℝ),
          M.xs ≤ x → x ≤ W → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
        ∀(b : ℕ) (GH : ActualNaturalBoundaryShape n b T) (s : T.cavityLeft.Slot)
          (E : NativeCanonicalExteriorSource n b pre mid tail T s GH 0 q 0),
          (∫z,nativeExteriorForestConditionalTest E.Ei E.Es E.D (restWeight n) (restFeature n)
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
            (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j)))
            (fun η ζ δ=>(G.canonicalOriginalQSource M forms).restProduct (E.read η ζ δ)^4)
            (exteriorForestIRoot z) (exteriorForestStarRoot z)
            ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
            (C^a*sourceMonomialScale x W initial)^4 := by
  by_cases ha : a=0
  · subst a
    refine ⟨1,by norm_num,Filter.Eventually.of_forall ?_⟩
    intro n M hs0 hsxs hsource hxs L us hus hret hmesh
    apply Filter.Eventually.of_forall
    intro k
    dsimp only
    intro pre mid tail hcut T G forms initial x W hxsx hxW hmass b GH s E
    rw [←E.whole_law (fun σ=>(G.canonicalOriginalQSource M forms).restProduct σ^4)]
    have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
    have hI : initial=∅:=Subsingleton.elim _ _
    simp [ActualNaturalBoundaryShape.restProduct,sourceMonomialScale,hI,
      T.cavityLeft.disorderExpect_one (restWeight_pos n) (restFeature n) ho]
  · obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_canonical_rest_even_moment_original_q
      a 2 (by omega) (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCm
      hm hdelta hroom hcl hcu hAz hC0 hCt
    refine ⟨C,hC,?_⟩
    filter_upwards [H] with n hn
    intro M hs0 hsxs hsource hxs L us hus hret hmesh
    filter_upwards [hn M hs0 hsxs hsource hxs L us hus hret hmesh] with k hk
    dsimp only at hk ⊢
    intro pre mid tail hcut T G forms initial x W hxsx hxW hmass b GH s E
    rw [←E.whole_law (fun σ=>(G.canonicalOriginalQSource M forms).restProduct σ^4)]
    have HK (bs : List PositiveMass) (he : bs=finiteCutMasses us k)
        (V : ClockTree (Spin n×Bool) bs) (A : ActualNaturalBoundaryShape n a V)
        (hf : Fin a → NativeSourceFactorForm) (I : Finset (Fin a))
        (hA : ∀e,A.sourceLowMass e ≤ Cmass*sourceFactorScale x W I e) :
        V.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0
          (fun j=>Sum.elim (fun _=>(M.sweepBf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
            (fun _=>(M.sweepHf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)))
          (fun σ=>(A.canonicalOriginalQSource M hf).restProduct σ^4) 0 ≤
          (C^a*sourceMonomialScale x W I)^4 := by
      subst bs
      simpa only [show 2*2=4 by norm_num,(show Even 4 by decide).pow_abs] using hk V A hf I x W hxsx hxW hA
    exact HK (pre++(mid++tail)) hcut T G forms initial hmass

end OAI.SKFluctuations.Cavity
