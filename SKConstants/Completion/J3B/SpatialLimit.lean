module

public import SKConstants.Completion.J3B.DiffusionMoments
public import SKConstants.BrownianDyadicGrid

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.J3B
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic
variable {Ω : Type*} [MeasurableSpace Ω]

attribute [local irreducible] actualParisiFullCurvature actualParisiFullMagnetization

theorem finiteSum_meanSquare_le {ι : Type*} (μ : Measure Ω) (s : Finset ι)
    (F : ι → Ω → ℝ) (hm : ∀ i ∈ s, Measurable (F i))
    (hi : ∀ i ∈ s, Integrable (fun w => F i w ^ 2) μ) :
    Integrable (fun w => (∑ i ∈ s, F i w) ^ 2) μ ∧
      (∫ w, (∑ i ∈ s, F i w) ^ 2 ∂μ) ≤
        (s.card : ℝ) * ∑ i ∈ s, ∫ w, F i w ^ 2 ∂μ := by
  have hdom : Integrable (fun w => (s.card : ℝ) * ∑ i ∈ s, F i w ^ 2) μ :=
    (integrable_finsetSum s hi).const_mul _
  have hbound (w : Ω) : (∑ i ∈ s, F i w) ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, F i w ^ 2 := sq_sum_le_card_mul_sum_sq
  have hsum : Integrable (fun w => (∑ i ∈ s, F i w) ^ 2) μ := hdom.mono'
    ((Finset.measurable_sum s hm).pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using hbound w))
  refine ⟨hsum, (integral_mono hsum hdom hbound).trans_eq ?_⟩
  rw [integral_const_mul, integral_finsetSum _ hi]

def spatialCellRemainder (W : BrownianSystem Ω) (β : ℝ) (s t : ℝ≥0) (w : Ω) : ℝ :=
  actualSpatialRemainder β s (actualParisiFullScalarProcess W β s w)
    (actualParisiFullScalarProcess W β t w)

theorem measurable_spatialCellRemainder (W : BrownianSystem Ω) (β : ℝ) (hβ : β ≠ 0)
    (s t : ℝ≥0) (hs : (s : ℝ) < β ^ 2) : Measurable (spatialCellRemainder W β s t) := by
  have hU := (physicalValue_contDiff β hβ s ⟨s.coe_nonneg, hs⟩).continuous.measurable
  have hYs : Measurable (actualParisiFullScalarProcess W β s) :=
    (actualParisiFullScalarDrift β).solution_measurable W s
  have hYt : Measurable (actualParisiFullScalarProcess W β t) :=
    (actualParisiFullScalarDrift β).solution_measurable W t
  have hm : Measurable (fun w => actualParisiFullMagnetization β s
      (actualParisiFullScalarProcess W β s w)) := measurable_actualParisiMagnetizationObservable W β s
  have ha : Measurable (fun w => actualParisiFullCurvature β s
      (actualParisiFullScalarProcess W β s w)) := by
    have hc : Continuous (actualParisiFullCurvature β s) :=
      (continuous_actualParisiFullCurvature β).comp
        ((continuous_const : Continuous (fun _ : ℝ => (s : ℝ))).prodMk continuous_id)
    exact hc.measurable.comp hYs
  change Measurable (fun w =>
    parisiPhysicalValue β (parisiEquilibriumMeasure β) s (actualParisiFullScalarProcess W β t w) -
      parisiPhysicalValue β (parisiEquilibriumMeasure β) s (actualParisiFullScalarProcess W β s w) -
      actualParisiFullMagnetization β s (actualParisiFullScalarProcess W β s w) *
        (actualParisiFullScalarProcess W β t w - actualParisiFullScalarProcess W β s w) -
      actualParisiFullCurvature β s (actualParisiFullScalarProcess W β s w) *
        (actualParisiFullScalarProcess W β t w - actualParisiFullScalarProcess W β s w) ^ 2 / 2)
  exact (((hU.comp hYt).sub (hU.comp hYs)).sub (hm.mul (hYt.sub hYs))).sub
    ((ha.mul ((hYt.sub hYs).pow_const 2)).div_const 2)

theorem spatialCellRemainder_meanSquare_le (W : BrownianSystem Ω) (β : ℝ) (hβ : β ≠ 0)
    (s t : ℝ≥0) (hst : s ≤ t) (hs : (s : ℝ) < β ^ 2) :
    Integrable (fun w => spatialCellRemainder W β s t w ^ 2) W.law ∧
      (∫ w, spatialCellRemainder W β s t w ^ 2 ∂W.law) ≤
        32 * ((susceptibilityLipschitzConstant : ℝ) / 6) ^ 2 *
          (15 * ((t : ℝ) - s) ^ 3 + ((t : ℝ) - s) ^ 6) := by
  let C : ℝ := (susceptibilityLipschitzConstant : ℝ) / 6
  have h6 := actualScalar_increment_sixth W β s t hst
  have hbound (w : Ω) : spatialCellRemainder W β s t w ^ 2 ≤
      C ^ 2 * |actualParisiFullScalarProcess W β t w -
        actualParisiFullScalarProcess W β s w| ^ 6 := by
    have h := actualSpatialRemainder_bound β hβ s ⟨s.coe_nonneg, hs⟩
      (actualParisiFullScalarProcess W β s w) (actualParisiFullScalarProcess W β t w)
    have hp := pow_le_pow_left₀ (abs_nonneg _) h 2
    simpa only [spatialCellRemainder, sq_abs, mul_pow, ← pow_mul, Nat.reduceMul, C] using hp
  have hiB := h6.1.const_mul (C ^ 2)
  have hiR : Integrable (fun w => spatialCellRemainder W β s t w ^ 2) W.law := hiB.mono'
    ((measurable_spatialCellRemainder W β hβ s t hs).pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using hbound w))
  refine ⟨hiR, (integral_mono hiR hiB hbound).trans ?_⟩
  rw [integral_const_mul]
  calc
    _ ≤ C ^ 2 * (32 * (15 * ((t : ℝ) - s) ^ 3 + ((t : ℝ) - s) ^ 6)) :=
      mul_le_mul_of_nonneg_left h6.2 (sq_nonneg _)
    _ = _ := by dsimp only [C]; ring

theorem dyadic_cell_width (V : ℝ≥0) (l i : ℕ) :
    ((brownianDyadicGrid V).time l (i + 1) : ℝ) - (brownianDyadicGrid V).time l i =
      brownianDyadicWidth V l := by
  simp only [brownianDyadicGrid_time_coe, brownianDyadicWidth, Nat.cast_add, Nat.cast_one]
  ring

def dyadicSpatialRemainder (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) (l : ℕ) (w : Ω) : ℝ :=
  ∑ i ∈ Finset.range (2 ^ l), spatialCellRemainder W β
    ((brownianDyadicGrid V).time l i) ((brownianDyadicGrid V).time l (i + 1)) w

theorem dyadicSpatialRemainder_meanSquare_le (W : BrownianSystem Ω) (β : ℝ) (hβ : β ≠ 0)
    (V : ℝ≥0) (hV : (V : ℝ) < β ^ 2) (l : ℕ) :
    Integrable (fun w => dyadicSpatialRemainder W β V l w ^ 2) W.law ∧
      (∫ w, dyadicSpatialRemainder W β V l w ^ 2 ∂W.law) ≤
        32 * ((susceptibilityLipschitzConstant : ℝ) / 6) ^ 2 * (V : ℝ) ^ 2 *
          (15 * brownianDyadicWidth V l + brownianDyadicWidth V l ^ 4) := by
  let t := (brownianDyadicGrid V).time l
  have htn : t (2 ^ l) = V := by simp [t, brownianDyadicGrid]
  have hs (i : ℕ) (hi : i ∈ Finset.range (2 ^ l)) : (t i : ℝ) < β ^ 2 := by
    have hle := (brownianDyadicGrid V).monotone l (Finset.mem_range.mp hi).le
    exact (NNReal.coe_le_coe.mpr (hle.trans_eq htn)).trans_lt hV
  have hcell (i : ℕ) (hi : i ∈ Finset.range (2 ^ l)) :=
    spatialCellRemainder_meanSquare_le W β hβ (t i) (t (i + 1))
      ((brownianDyadicGrid V).monotone l (Nat.le_succ i)) (hs i hi)
  have hsum := finiteSum_meanSquare_le W.law (Finset.range (2 ^ l))
    (fun i => spatialCellRemainder W β (t i) (t (i + 1)))
    (fun i hi => measurable_spatialCellRemainder W β hβ _ _ (hs i hi))
    (fun i hi => (hcell i hi).1)
  refine ⟨hsum.1, hsum.2.trans ?_⟩
  calc
    _ ≤ ((2 ^ l : ℕ) : ℝ) * ∑ _i ∈ Finset.range (2 ^ l),
        (32 * ((susceptibilityLipschitzConstant : ℝ) / 6) ^ 2 *
          (15 * brownianDyadicWidth V l ^ 3 + brownianDyadicWidth V l ^ 6)) := by
      simp only [Finset.card_range]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro i hi
      simpa only [t, dyadic_cell_width] using (hcell i hi).2
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat,
        brownianDyadicWidth]
      field_simp

theorem dyadicSpatialRemainder_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (hβ : β ≠ 0)
    (V : ℝ≥0) (hV : (V : ℝ) < β ^ 2) :
    Tendsto (fun l => ∫ w, dyadicSpatialRemainder W β V l w ^ 2 ∂W.law)
      atTop (𝓝 0) := by
  have ht := (brownianDyadicWidth_tendsto V).const_mul 15 |>.add
    ((brownianDyadicWidth_tendsto V).pow 4)
  have ht' := ht.const_mul
    (32 * ((susceptibilityLipschitzConstant : ℝ) / 6) ^ 2 * (V : ℝ) ^ 2)
  apply squeeze_zero (fun l => integral_nonneg (fun w => sq_nonneg _))
    (fun l => (dyadicSpatialRemainder_meanSquare_le W β hβ V hV l).2)
  simpa only [mul_zero, zero_pow (by decide : 4 ≠ 0), add_zero] using ht'

end SKConstants.Completion.J3B
