module

public import ComparisonSignedCavitySavedDifferences

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_incoming_projection_fourth_le_raw (n : ℕ)
    {as : List PositiveMass} {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) (center : ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n × Bool) as)) :
    nativeIncomingProjectionFourth n q x center p ≤
      16*nativeIncomingRawTargetMoment n 2 as q x center := by
  let T := p.tree.cavityLeft
  let Y := nativeCenteredProjectedDeletedOverlap n as q x center
  have hnew : T.expect (restWeight n) (restFeature n) q
      (fun σ => Y (p.restSpin σ)^4) x ≤
        nativeIncomingRawTargetMoment n 2 as q x center := by
    simpa only [nativeIncomingRawTargetMoment, Y, T, ClockTree.MarkedPlacement.restSpin, show 2*2=4 by norm_num,
      (show Even 4 by decide).pow_abs] using
      native_projected_target_power_moment_le n 4 T ho
        (p.tree.cavityLeftSlot p.mark) q x center
  have hold : T.expect (restWeight n) (restFeature n) q
      (fun σ => Y (nativeAttachmentOld p σ)^4) x ≤
        nativeIncomingRawTargetMoment n 2 as q x center := by
    simpa only [nativeIncomingRawTargetMoment, Y, T, nativeAttachmentOld,
      show 2*2=4 by norm_num, (show Even 4 by decide).pow_abs] using
      native_projected_target_power_moment_le n 4 T ho
        (ClockTree.cavityLeftSlot p.tree (p.embed (ClockTree.singleSlot (S := Spin n×Bool) as)))
        q x center
  have hpoint (σ : T.Assignment) :
      (Y (p.restSpin σ)-Y (nativeAttachmentOld p σ))^4 ≤
        8*(Y (p.restSpin σ)^4+Y (nativeAttachmentOld p σ)^4) := by
    simpa only [sub_eq_add_neg, neg_pow, show (-1:ℝ)^4=1 by norm_num, one_mul,
      show (2:ℝ)^(4-1)=8 by norm_num] using
      (show Even 4 by decide).add_pow_le (a := Y (p.restSpin σ)) (b := -Y (nativeAttachmentOld p σ))
  have hsum : nativeIncomingProjectionFourth n q x center p ≤
      8*(T.expect (restWeight n) (restFeature n) q (fun σ => Y (p.restSpin σ)^4) x+
        T.expect (restWeight n) (restFeature n) q (fun σ => Y (nativeAttachmentOld p σ)^4) x) := by
    unfold nativeIncomingProjectionFourth nativeIncomingProjectionDifference
    change T.expect (restWeight n) (restFeature n) q
      (fun σ => (Y (p.restSpin σ)-Y (nativeAttachmentOld p σ))^4) x ≤ _
    unfold ClockTree.expect
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro σ _
    have hw := (T.weight_probability (restWeight_pos n) (restFeature n) ho q x).1 σ
    convert mul_le_mul_of_nonneg_left (hpoint σ) hw using 1; ring
  have hb := mul_le_mul_of_nonneg_left (add_le_add hnew hold) (by norm_num : (0:ℝ)≤8)
  exact hsum.trans (hb.trans_eq (by ring))

private theorem native_normalized_spin_norm_le_one (n : ℕ) (σ : Spin n) :
    ‖WithLp.toLp 2 (normalizedSpin n σ)‖ ≤ 1 := by
  have hinner : ‖WithLp.toLp 2 (normalizedSpin n σ)‖^2=orderedOverlap n σ σ := by
    rw [← real_inner_self_eq_norm_sq, normalizedSpin_inner_eq_overlap]
  have habs := orderedOverlap_abs_le_one n σ σ
  have hn := norm_nonneg (WithLp.toLp 2 (normalizedSpin n σ))
  nlinarith [(le_abs_self (orderedOverlap n σ σ)).trans habs]

theorem native_incoming_anchor_fourth_le_anchor (n : ℕ)
    {as : List PositiveMass} (E : ClockTree (Spin n) as) {a : ℝ}
    (ho : MassOrdered a as) (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n × Bool) as)) :
    nativeIncomingAnchorFourth n E H s q x p ≤
      16*‖nativeWeightedExteriorAnchor n E H s q x‖^4 := by
  let V := nativeWeightedExteriorAnchor n E H s q x
  have hpoint (σ : p.tree.cavityLeft.Assignment) :
      nativeIncomingAnchorDifference n E H s q x p σ^4 ≤ 16*‖V‖^4 := by
    let W := WithLp.toLp 2 (normalizedSpin n (nativeAttachmentOld p σ))-
      WithLp.toLp 2 (normalizedSpin n (p.restSpin σ))
    have hW : ‖W‖≤2 := by
      have hs := norm_sub_le
        (WithLp.toLp 2 (normalizedSpin n (nativeAttachmentOld p σ)))
        (WithLp.toLp 2 (normalizedSpin n (p.restSpin σ)))
      exact hs.trans (by linarith [native_normalized_spin_norm_le_one n (nativeAttachmentOld p σ),
        native_normalized_spin_norm_le_one n (p.restSpin σ)])
    have hi : |inner ℝ W V|≤2*‖V‖ := (abs_real_inner_le_norm W V).trans
      (mul_le_mul_of_nonneg_right hW (norm_nonneg V))
    have hp := pow_le_pow_left₀ (abs_nonneg (inner ℝ W V)) hi 4
    simpa only [nativeIncomingAnchorDifference, W, V, (show Even 4 by decide).pow_abs,
      mul_pow, show (2:ℝ)^4=16 by norm_num] using hp
  calc
    nativeIncomingAnchorFourth n E H s q x p ≤
        p.tree.cavityLeft.expect (restWeight n) (restFeature n) q (fun _ => 16*‖V‖^4) x := by
      unfold nativeIncomingAnchorFourth ClockTree.expect
      apply Finset.sum_le_sum
      intro σ _
      exact mul_le_mul_of_nonneg_left (hpoint σ)
        ((p.tree.cavityLeft.weight_probability (restWeight_pos n) (restFeature n) ho q x).1 σ)
    _ = 16*‖V‖^4 := p.tree.cavityLeft.expect_const (restWeight_pos n) (restFeature n) ho q _ x

theorem native_incoming_anchor_fourth_le_exterior_raw (n : ℕ)
    {as : List PositiveMass} (E : ClockTree (Spin n) as) {a : ℝ}
    (ho : MassOrdered a as) (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n × Bool) as)) :
    nativeIncomingAnchorFourth n E H s q x p ≤
      16*(E.expect (restWeight n) (restFeature n) q (fun σ => |H σ|^4) x*
        (E.fork E).expect (restWeight n) (restFeature n) q (fun σ =>
          |deletedOverlap n (joinSpin (E.atSlot σ.1 s,false))
            (joinSpin (E.atSlot σ.2 s,false))|^2) x) := by
  apply (native_incoming_anchor_fourth_le_anchor n E ho H s q x p).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simpa only [show 4*1=4 by norm_num, show 2*1=2 by norm_num] using
    native_weighted_exterior_anchor_moment n 1 E ho H s q x

theorem native_incoming_anchor_placement_raw_projection (n k : ℕ)
    {as : List PositiveMass} (E : ClockTree (Spin n) as) {a : ℝ}
    (ho : MassOrdered a as) (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) (center : ℝ)
    (p : ClockTree.MarkedPlacement (ClockTree.single (S := Spin n × Bool) as)) :
    |nativeIncomingAnchorPlacement n k E H s q x center p| ≤
      Real.sqrt (Real.sqrt (16*nativeIncomingRawTargetMoment n 2 as q x center*
        nativeIncomingAnchorFourth n E H s q x p) *
        nativeIncomingRawTargetMoment n k as q x center) := by
  have hM : 0 ≤ nativeIncomingRawTargetMoment n k as q x center := by
    unfold nativeIncomingRawTargetMoment ClockTree.pairMean ClockTree.singleMean ClockTree.expect
    apply Finset.sum_nonneg
    intro σ _
    apply mul_nonneg
    · exact ((ClockTree.single as).weight_probability (restWeight_pos n) (restFeature n) ho q x).1 σ
    · apply Finset.sum_nonneg
      intro τ _
      exact mul_nonneg
        (((ClockTree.single as).weight_probability (restWeight_pos n) (restFeature n) ho q x).1 τ)
        (by positivity)
  apply (native_incoming_anchor_placement_saved_differences n k E ho H s q x center p).trans
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_right _ hM
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_right (native_incoming_projection_fourth_le_raw n ho q x center p)
  unfold nativeIncomingAnchorFourth ClockTree.expect
  exact Finset.sum_nonneg fun σ _ => mul_nonneg
    ((p.tree.cavityLeft.weight_probability (restWeight_pos n) (restFeature n) ho q x).1 σ)
    (by positivity)

end OAI.SKFluctuations.Cavity
