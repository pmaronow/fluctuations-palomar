module

public import ComparisonSignedCavityTwinPrefixNativeLaw
public import CavityNativeWeightedExterior

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_unweighted_exterior_anchor_eighth_le_raw_pair (n : ℕ)
    {as : List PositiveMass} (E : ClockTree (Spin n) as) {a : ℝ} (ho : MassOrdered a as)
    (s : E.Slot) (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) :
    ‖nativeWeightedExteriorAnchor n E (fun _ => 1) s q x‖^8 ≤
      (E.fork E).expect (restWeight n) (restFeature n) q (fun σ =>
        |deletedOverlap n (joinSpin (E.atSlot σ.1 s,false))
          (joinSpin (E.atSlot σ.2 s,false))|^4) x := by
  have H := native_weighted_exterior_anchor_moment n 2 E ho (fun _ => 1) s q x
  have hone : E.expect (restWeight n) (restFeature n) q (fun _ => 1) x=1 := by
    simpa only [ClockTree.expect,mul_one] using
      (E.weight_probability (restWeight_pos n) (restFeature n) ho q x).2
  simpa only [show 4*2=8 by norm_num,show 2*2=4 by norm_num,abs_one,one_pow,
    hone,one_mul] using H

theorem native_unweighted_raw_pair_fourth_le_one (n : ℕ)
    {as : List PositiveMass} (E : ClockTree (Spin n) as) {a : ℝ} (ho : MassOrdered a as)
    (s : E.Slot) (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) :
    (E.fork E).expect (restWeight n) (restFeature n) q (fun σ =>
      |deletedOverlap n (joinSpin (E.atSlot σ.1 s,false))
        (joinSpin (E.atSlot σ.2 s,false))|^4) x ≤ 1 := by
  have hw := (E.fork E).weight_probability (restWeight_pos n) (restFeature n) ho q x
  unfold ClockTree.expect
  calc
    _ ≤ ∑ σ,(E.fork E).weight (restWeight n) (restFeature n) q σ x*1 := by
      apply Finset.sum_le_sum
      intro σ _
      apply mul_le_mul_of_nonneg_left _ (hw.1 σ)
      exact pow_le_one₀ (abs_nonneg _) (abs_deletedOverlap_le_one n _ _)
    _ = 1 := by simpa only [mul_one] using hw.2

theorem native_unweighted_exterior_anchor_continuous (n : ℕ)
    {as : List PositiveMass} (E : ClockTree (Spin n) as) {a : ℝ} (ho : MassOrdered a as)
    (s : E.Slot) (q : ℕ → RestCoordinate n → ℝ≥0) :
    Continuous (nativeWeightedExteriorAnchor n E (fun _ => 1) s q) := by
  unfold nativeWeightedExteriorAnchor
  have hSum : Continuous (fun x => ∑ σ,(E.weight (restWeight n) (restFeature n) q σ x*1) •
      WithLp.toLp 2 (normalizedSpin n (E.atSlot σ s))) := by
    apply continuous_finset_sum
    intro σ _
    exact (((E.weight_smooth (restWeight_pos n) (restFeature n) ho q σ 0).continuous).mul
      continuous_const).smul continuous_const
  exact hSum.const_smul ((n:ℝ)/(n+1 : ℕ))

theorem native_twin_B_anchor_eighth_le_original_star_raw (n : ℕ)
    (pre mid tail : List (GaussianStep (RestCoordinate n)))
    {a : ℝ} (hs : OrderedSteps a (pre ++ (mid ++ tail)))
    {as : List PositiveMass} (E : ClockTree (Spin n) as) {aE : ℝ} (ho : MassOrdered aE as)
    (s : E.Slot) (q : ℕ → RestCoordinate n → ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → RestCoordinate n → ℝ) (hx : Measurable x) :
    (∫ z,‖nativeWeightedExteriorAnchor n E (fun _ => 1) s q (twinPrefixBRoot z)‖^8
      ∂twinPrefixRootLaw (restWeight n) (restFeature n) pre mid tail μ x hx) ≤
      ∫ p,prefixTest (pre ++ mid) (gaussianHierarchy (restWeight n) (restFeature n) tail)
        (fun y => (E.fork E).expect (restWeight n) (restFeature n) q (fun σ =>
          |deletedOverlap n (joinSpin (E.atSlot σ.1 s,false))
            (joinSpin (E.atSlot σ.2 s,false))|^4) y) (x p) ∂μ := by
  let μjoint := twinPrefixRootLaw (restWeight n) (restFeature n) pre mid tail μ x hx
  let R := fun y => (E.fork E).expect (restWeight n) (restFeature n) q (fun σ =>
    |deletedOverlap n (joinSpin (E.atSlot σ.1 s,false))
      (joinSpin (E.atSlot σ.2 s,false))|^4) y
  have hμjoint : IsFiniteMeasure μjoint := twinPrefixRootLaw_finite (restWeight_pos n)
    (restFeature n) pre mid tail hs μ x hx
  letI := hμjoint
  have hR : BddSmooth 0 R := (E.fork E).nativeAnchor_expect_smooth (restWeight_pos n)
    (restFeature n) ho q _ 0
  have hmB : Measurable (twinPrefixBRoot (ι:=RestCoordinate n) (P:=P)) :=
    twinPrefixBRoot_measurable
  have hmAnchor : Measurable (fun z => ‖nativeWeightedExteriorAnchor n E (fun _ => 1) s q
      (twinPrefixBRoot z)‖^8) :=
    (((native_unweighted_exterior_anchor_continuous n E ho s q).measurable.comp
      hmB).norm).pow_const 8
  have hiAnchor : Integrable (fun z => ‖nativeWeightedExteriorAnchor n E (fun _ => 1) s q
      (twinPrefixBRoot z)‖^8) μjoint := by
    apply Integrable.of_bound hmAnchor.aestronglyMeasurable 1
    apply Eventually.of_forall
    intro z
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
    exact (native_unweighted_exterior_anchor_eighth_le_raw_pair n E ho s q _).trans
      (native_unweighted_raw_pair_fourth_le_one n E ho s q _)
  have hiR : Integrable (fun z => R (twinPrefixBRoot z)) μjoint := by
    obtain ⟨B,hB,hbound⟩ := hR.bound
    apply Integrable.of_bound (hR.continuous.measurable.comp hmB).aestronglyMeasurable B
    exact Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs,Function.comp_apply] using hbound (twinPrefixBRoot z))
  have H := integral_mono hiAnchor hiR (fun z =>
    native_unweighted_exterior_anchor_eighth_le_raw_pair n E ho s q (twinPrefixBRoot z))
  rw [integral_twinPrefixRootLaw_B_test (restWeight_pos n) (restFeature n) pre mid tail hs
    μ x hx hR] at H
  exact H

end OAI.SKFluctuations.Cavity
