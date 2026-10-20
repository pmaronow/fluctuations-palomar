module

public import ComparisonSignedCavitySecondLowNativeSharedLayerGram

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

omit [Nonempty S] in
theorem native_shared_prefix_old_moment_eq_original_clone
    (pre : List PositiveMass) (hpre : pre≠[]) {tail : List PositiveMass}
    (A : ClockTree S tail) (E : ClockTree S (pre++tail)) (s : A.Slot)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (P : A.Assignment→E.Assignment→ℝ) (x : ι→ℝ) :
    nativeSharedPrefixOldMoment pre A E w φ q P x=
      nativeRetainedCloneCutMean w φ ((exteriorPrepend pre A).fork E)
        (.inl ((exteriorPrependSlotEquiv pre A).symm s)) pre.length q
        (fun σ τ=>(P (exteriorPrependAssignmentEquiv pre A σ.1) σ.2-
          P (exteriorPrependAssignmentEquiv pre A τ.1) τ.2)^2) x := by
  rw [native_retained_clone_shared_exterior_prefix_law pre hpre]
  simp only [Equiv.apply_symm_apply,nativeSharedPrefixOldMoment]

omit [Nonempty S] in
theorem native_shared_prefix_new_moment_eq_original_clone
    (pre : List PositiveMass) (hpre : pre≠[]) {tail : List PositiveMass}
    (A : ClockTree S tail) (E : ClockTree S (pre++tail)) (s : A.Slot)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (q : ℕ→ι→ℝ≥0)
    (F : E.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeSharedPrefixNewMoment pre A E s w φ q F x=
      nativeRetainedCloneCutMean w φ ((exteriorPrepend pre A).fork E)
        (.inl ((exteriorPrependSlotEquiv pre A).symm s)) pre.length q
        (fun σ τ=>(F σ.2 ((exteriorPrepend pre A).atSlot σ.1
          ((exteriorPrependSlotEquiv pre A).symm s))-
          F τ.2 ((exteriorPrepend pre A).atSlot τ.1
            ((exteriorPrependSlotEquiv pre A).symm s)))^2) x := by
  rw [native_retained_clone_shared_exterior_prefix_law pre hpre]
  simp only [exteriorPrepend_atSlot,Equiv.apply_symm_apply,nativeSharedPrefixNewMoment]

end OAI.SKFluctuations.Cavity
