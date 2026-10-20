module

public import ComparisonSignedCavityTwinPrefixNativeLaw
public import CavityNativeWeightedExterior

@[expose] public section

noncomputable section
set_option maxHeartbeats 7000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_weighted_target_difference_distinct_roots (n : ℕ)
    {es ds : List PositiveMass} (E : ClockTree (Spin n) es) (D : ClockTree (Spin n) ds)
    (H : E.Assignment → ℝ) (s : E.Slot)
    (qE qD : ℕ → RestCoordinate n → ℝ≥0) (xE xD : RestCoordinate n → ℝ)
    (Z : D.Assignment → ℝ) (old new : D.Assignment → Spin n) :
    E.expect (restWeight n) (restFeature n) qE (fun β =>
      D.expect (restWeight n) (restFeature n) qD (fun δ => Z δ*H β*
        (deletedOverlap n (joinSpin (old δ,false)) (joinSpin (E.atSlot β s,false))-
          deletedOverlap n (joinSpin (new δ,false)) (joinSpin (E.atSlot β s,false)))) xD) xE =
    D.expect (restWeight n) (restFeature n) qD (fun δ => Z δ*inner ℝ
      (WithLp.toLp 2 (normalizedSpin n (old δ))-WithLp.toLp 2 (normalizedSpin n (new δ)))
      (nativeWeightedExteriorAnchor n E H s qE xE)) xD := by
  simp_rw [deleted_overlap_join_eq_scaled]
  unfold ClockTree.expect nativeWeightedExteriorAnchor
  simp only [inner_smul_right,inner_sum,inner_sub_left,normalizedSpin_inner_eq_overlap,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro δ _
  apply Finset.sum_congr rfl
  intro β _
  ring

theorem native_joint_old_fresh_anchor_difference (n : ℕ)
    {bs fs ds : List PositiveMass} (Bold : ClockTree (Spin n) bs)
    (Fresh : ClockTree (Spin n) fs) (D : ClockTree (Spin n) ds) (s : Fresh.Slot)
    (qB qF qD : ℕ → RestCoordinate n → ℝ≥0) (xB xD : RestCoordinate n → ℝ)
    (Z : Bold.Assignment → D.Assignment → ℝ) (old new : D.Assignment → Spin n) :
    Bold.expect (restWeight n) (restFeature n) qB (fun β =>
      Fresh.expect (restWeight n) (restFeature n) qF (fun f =>
        D.expect (restWeight n) (restFeature n) qD (fun δ => Z β δ*
          (deletedOverlap n (joinSpin (old δ,false)) (joinSpin (Fresh.atSlot f s,false))-
            deletedOverlap n (joinSpin (new δ,false)) (joinSpin (Fresh.atSlot f s,false)))) xD) xB) xB =
    Bold.expect (restWeight n) (restFeature n) qB (fun β =>
      D.expect (restWeight n) (restFeature n) qD (fun δ => Z β δ*inner ℝ
        (WithLp.toLp 2 (normalizedSpin n (old δ))-WithLp.toLp 2 (normalizedSpin n (new δ)))
        (nativeWeightedExteriorAnchor n Fresh (fun _ => 1) s qF xB)) xD) xB := by
  apply congrArg (fun R => Bold.expect (restWeight n) (restFeature n) qB R xB)
  funext β
  have H := native_weighted_target_difference_distinct_roots n Fresh D (fun _ => 1) s
    qF qD xB xD (Z β) old new
  simpa only [mul_one] using H

theorem native_twin_conditional_fresh_anchor_difference (n : ℕ)
    {ias tas : List PositiveMass} (A : ClockTree (Spin n) ias)
    (Bold Fresh D : ClockTree (Spin n) tas) (s : Fresh.Slot)
    (qi qs : ℕ → RestCoordinate n → ℝ≥0)
    (Z : A.Assignment → Bold.Assignment → D.Assignment → ℝ)
    (old new : D.Assignment → Spin n) (xi xB xD : RestCoordinate n → ℝ) :
    nativeTwinForestConditionalTest A (Bold.fork Fresh) D (restWeight n) (restFeature n) qi qs
      (fun η β δ => Z η β.1 δ*
        (deletedOverlap n (joinSpin (old δ,false)) (joinSpin (Fresh.atSlot β.2 s,false))-
          deletedOverlap n (joinSpin (new δ,false)) (joinSpin (Fresh.atSlot β.2 s,false)))) xi xB xD =
    A.expect (restWeight n) (restFeature n) qi (fun η =>
      Bold.expect (restWeight n) (restFeature n) qs (fun β =>
        D.expect (restWeight n) (restFeature n) qs (fun δ => Z η β δ*inner ℝ
          (WithLp.toLp 2 (normalizedSpin n (old δ))-WithLp.toLp 2 (normalizedSpin n (new δ)))
          (nativeWeightedExteriorAnchor n Fresh (fun _ => 1) s qs xB)) xD) xB) xi := by
  unfold nativeTwinForestConditionalTest
  simp only [ClockTree.expect_fork]
  apply congrArg (fun R => A.expect (restWeight n) (restFeature n) qi R xi)
  funext η
  exact native_joint_old_fresh_anchor_difference n Bold Fresh D s qs qs qs xB xD (Z η) old new

theorem native_twin_source_fresh_anchor_difference (n : ℕ) (pre mid : List PositiveMass)
    {tail : List PositiveMass} (A : ClockTree (Spin n) (mid++tail))
    (Bold Fresh D : ClockTree (Spin n) tail) (s : Fresh.Slot)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ)
    (Z : A.Assignment → Bold.Assignment → D.Assignment → ℝ)
    (old new : D.Assignment → Spin n) (x : RestCoordinate n → ℝ) :
    let qi := fun j => cumulativeIncrements (q 0) (fun k => q (k+1)) (pre.length+j)
    let qs := fun j => cumulativeIncrements (q 0) (fun k => q (k+1)) (pre.length+(mid.length+j))
    (nativeTwinForestTree pre mid A (Bold.fork Fresh) D).disorderExpect (restWeight n)
      (restFeature n) v q (nativeTwinForestRead pre mid A (Bold.fork Fresh) D
        (fun η β δ => Z η β.1 δ*
          (deletedOverlap n (joinSpin (old δ,false)) (joinSpin (Fresh.atSlot β.2 s,false))-
            deletedOverlap n (joinSpin (new δ,false)) (joinSpin (Fresh.atSlot β.2 s,false))))) x =
      ∫ z,A.expect (restWeight n) (restFeature n) qi (fun η =>
        Bold.expect (restWeight n) (restFeature n) qs (fun β =>
          D.expect (restWeight n) (restFeature n) qs (fun δ => Z η β δ*inner ℝ
            (WithLp.toLp 2 (normalizedSpin n (old δ))-WithLp.toLp 2 (normalizedSpin n (new δ)))
            (nativeWeightedExteriorAnchor n Fresh (fun _ => 1) s qs (twinPrefixBRoot z)))
              (twinPrefixDRoot z)) (twinPrefixBRoot z)) (twinPrefixSharedRoot z)
        ∂nativeTwinPrefixDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x := by
  dsimp only
  rw [nativeTwinForest_disorder_law_eq_conditional pre mid A (Bold.fork Fresh) D
    (restWeight_pos n) (restFeature n) ho v q _ x]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => native_twin_conditional_fresh_anchor_difference n
    A Bold Fresh D s _ _ Z old new (twinPrefixSharedRoot z) (twinPrefixBRoot z) (twinPrefixDRoot z))

end OAI.SKFluctuations.Cavity
