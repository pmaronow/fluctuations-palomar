module

public import ComparisonSignedCavityCanonicalRestCloneTransport
public import ComparisonSignedCavitySecondLowUnweightedCCanonicalSource
public import ComparisonSignedCavitySecondLowOccupiedOldCanonicalOrientation
public import ComparisonSignedCavitySecondLowUnweightedCMarkedCanonicalSource
public import SKProof.Port.ComparisonActualOriginalQLowB0ObservedAffineReadoutSourceAlong
public import SKProof.Port.ComparisonActualOriginalQOriginalTargetB0

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 24000000
namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

theorem onCloneOld_canonical_restProduct_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (target : T.Slot) (cut : ℕ)
    (σ : (nativeCloneBlockAtSlot T target cut).tree.cavityLeft.Assignment) :
    ((G.onCloneOld target cut).canonicalOriginalQSource M forms).restProduct σ=
      (G.canonicalOriginalQSource M forms).restProduct
        ((nativeCloneBlockAtSlot T target cut).restOldRestrict σ) := by
  rw [←(G.canonicalOriginalQSource M forms).onCloneOld_restProduct target cut σ]
  unfold restProduct
  apply Finset.prod_congr rfl
  intro e _
  simp only [canonicalOriginalQSource,onCloneOld,sourceLowMass,
    (nativeCloneBlockAtSlot_within_copy_splits T target cut (G.i e) (G.j e)).1]

theorem onCloneOld_retarget_new_canonical_restProduct_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (target : T.Slot) (cut : ℕ) (hout : ∀e,T.splitIndex target (G.i e)<cut)
    (σ : (nativeCloneBlockAtSlot T target cut).tree.cavityLeft.Assignment) :
    (((G.onCloneOld target cut).retarget
      (fun e=>(nativeCloneBlockAtSlot T target cut).newEmbed (G.j e))
      (G.clone_new_targets_ne target cut hout)).canonicalOriginalQSource M forms).restProduct σ=
      (G.canonicalOriginalQSource M forms).restProduct
        ((nativeCloneBlockAtSlot T target cut).restNewRestrict σ) := by
  unfold restProduct
  apply Finset.prod_congr rfl
  intro e _
  have Hlow:=G.clone_new_targets_same_low target cut hout e
  have hanchor:=nativeCloneBlockAtSlot_exterior_shared T target cut (G.i e) (hout e)
  simp only [canonicalOriginalQSource,ActualNaturalBoundaryShape.retarget,onCloneOld,
    sourceLowMass] at Hlow ⊢
  rw [←Hlow,(nativeCloneBlockAtSlot_within_copy_splits T target cut (G.i e) (G.j e)).1]
  rw [NativeRetainedSubtreeClone.restNewRestrict_at,NativeRetainedSubtreeClone.restNewRestrict_at]
  rw [hanchor]

 theorem consTwoLowC_canonical_restProduct_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (f c z : T.Slot) (hfc : f≠c) (hzc : z≠c) (τ : T.cavityLeft.Assignment) :
    ((G.consTwoLowC f c z hfc hzc).canonicalOriginalQSource M (twoLowCForms forms)).restProduct τ=
      canonicalLowRestFactor_original_q M z c τ*canonicalLowRestFactor_original_q M f c τ*
        (G.canonicalOriginalQSource M forms).restProduct τ := by
  unfold consTwoLowC twoLowCForms
  rw [canonical_cons_restProduct_original_q,canonical_cons_restProduct_original_q]
  ring

 theorem consTwoLowC_complete_old_difference_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (f c z c' : T.Slot) (hfc : f≠c) (hzc : z≠c) (hfc' : f≠c') (hzc' : z≠c')
    (τ : T.cavityLeft.Assignment) :
    ((G.consTwoLowC f c z hfc hzc).canonicalOriginalQSource M (twoLowCForms forms)).restProduct τ-
      ((G.consTwoLowC f c' z hfc' hzc').canonicalOriginalQSource M (twoLowCForms forms)).restProduct τ=
      (G.canonicalOriginalQSource M forms).restProduct τ*
        (canonicalLowRestFactor_original_q M f c τ*canonicalLowRestFactor_original_q M z c τ-
          canonicalLowRestFactor_original_q M f c' τ*canonicalLowRestFactor_original_q M z c' τ) := by
  rw [consTwoLowC_canonical_restProduct_original_q,consTwoLowC_canonical_restProduct_original_q]
  ring

theorem orientAway_canonical_restProduct_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (s : T.Slot) (U : ℕ)
    (forms : Fin a→NativeSourceFactorForm) (σ : T.cavityLeft.Assignment) :
    ((G.orientAway s U).canonicalOriginalQSource M forms).restProduct σ=
      (G.canonicalOriginalQSource M forms).restProduct σ := by
  unfold restProduct
  apply Finset.prod_congr rfl
  intro e _
  simp only [canonicalOriginalQSource,G.orientAway_sourceLowMass]
  dsimp only [orientAway]
  split_ifs
  · exact fullBoundaryAffineFactor_swap n _ _ _ _
  · rfl

end ActualNaturalBoundaryShape

theorem native_second_low_fresh_observed_oriented_complete_rest_source_original_q
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T) (s : T.Slot) (star U : ℕ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0) (c : p.tree.Slot)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin a→NativeSourceFactorForm) (σ : p.tree.cavityLeft.Assignment) :
    (((nativeFreshObservedShape G s star p hp).orientAway c U).canonicalOriginalQSource M forms).restProduct σ=
      (G.canonicalOriginalQSource M forms).restProduct
        ((nativeFreshAtSlot T 0 s star).restRestrict (p.restRestrict σ)) := by
  rw [ActualNaturalBoundaryShape.orientAway_canonical_restProduct_original_q,nativeFreshObservedShape,
    ActualNaturalBoundaryShape.retained_canonical_restProduct_original_q,
    ActualNaturalBoundaryShape.retained_canonical_restProduct_original_q]

 theorem native_unweighted_c_canonical_row_eq_LOW_original_q
    (n U : ℕ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (f c : T.Slot) (hlow : T.splitIndex f c<U) (τ : T.cavityLeft.Assignment) :
    ActualNaturalBoundaryShape.canonicalLowRestFactor_original_q M f c τ=
      restLowKernel n U (fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ))
        (fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)) (T.splitIndex f c)
        (T.cavityLeft.atSlot τ (T.cavityLeftSlot f)) (T.cavityLeft.atSlot τ (T.cavityLeftSlot c)) := by
  simp only [ActualNaturalBoundaryShape.canonicalLowRestFactor_original_q,fullBoundaryAffineFactor,
    restLowKernel,hlow,ite_true,deletedOverlap,joinSpin,Fin.lastCases_castSucc]
  congr 3
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

end OAI.SKFluctuations.Cavity
