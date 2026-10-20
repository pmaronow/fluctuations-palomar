module

public import SKConstants.Completion.N7.ScalarMean

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N7
open SKConstantsOAI.ZeroTemperatureSK LM4b LC1
attribute [local irreducible] BoundedLipschitzDrift.solution
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
local instance (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability
local instance (Z : BrownianSystem A) : IsProbabilityMeasure Z.law := Z.isProbability

theorem actual_linked_defect_secondMoment
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (S H : ℝ≥0) (hSH : S ≤ H) :
    (∫ u : (Bool × Ω) × A,
      (scalarHiddenSign u.1.1 - actualParisiMagnetizationObservable W β S u.1.2) ^ 2
      ∂actualParisiFullQuerySpinLaw W Z β H) = 1 - actualParisiFullOverlap W β S := by
  have he (u : (Bool × Ω) × A) :
      (scalarHiddenSign u.1.1 - actualParisiMagnetizationObservable W β S u.1.2) ^ 2 =
        1 - 2 * actualRowPotential W β S u := by
    have hs : (scalarHiddenSign u.1.1) ^ 2 = 1 := by
      cases u.1.1 <;> norm_num [scalarHiddenSign]
    dsimp only [actualRowPotential, rowPotential]
    nlinarith
  have hpot : Integrable (actualRowPotential (A := A) W β S)
      (actualParisiFullQuerySpinLaw W Z β H) :=
    Integrable.of_bound (measurable_actualRowPotential W β S).aestronglyMeasurable (3 / 2)
      (ae_of_all _ (fun u => by
        rw [Real.norm_eq_abs]
        exact actualRowPotential_abs_le W β S u))
  simp_rw [he]
  rw [integral_sub (integrable_const _) (hpot.const_mul 2), integral_const,
    probReal_univ, one_smul, integral_const_mul, actualRowPotential_mean W Z β hβ S H hSH]
  ring

theorem sigmaSquare_mul_defect_eq_susceptibility
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (t : ℝ≥0) :
    (actualParisiQuerySigma W β t) ^ 2 * (1 - actualParisiFullOverlap W β t) =
      (actualParisiQuerySigma W β t) ^ 2 * actualParisiFullSusceptibilityExpected W β t := by
  by_cases ht : (t : ℝ) ≤ parisiEquilibriumPhysicalEndpoint β
  · rw [actualParisiQuerySigma_eq_zero_pre W β hβ t ht]
    simp
  · have ht' : β ^ 2 * parisiEquilibriumSupportEndpoint β ≤ (t : ℝ) := by
      rw [← parisiEquilibriumPhysicalEndpoint_coe β hβ]
      exact le_of_not_ge ht
    have hp : actualParisiFullSusceptibilityExpected W β t =
        1 - actualParisiFullOverlap W β t := by
      have he (w : Ω) : actualParisiFullCurvature β t (actualParisiFullScalarProcess W β t w) =
          1 - (actualParisiMagnetizationObservable W β t w) ^ 2 := by
        rw [actualParisiFullCurvature_eq_tanh_after_support β hβ t _ ht']
        unfold actualParisiMagnetizationObservable
        rw [actualParisiFullMagnetization_eq_tanh_after_support β hβ t ht']
      unfold actualParisiFullSusceptibilityExpected
      simp only [Real.toNNReal_coe]
      simp_rw [he]
      rw [integral_sub (integrable_const _) (by
        simpa only [pow_two] using integrable_actualParisiMagnetization_pair W β t t),
        integral_const, probReal_univ, one_smul]
      rfl
    rw [hp]

theorem actualRowDCoefficient_secondMoment
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (S H : ℝ≥0) (hSH : S ≤ H) :
    (∫ u, (actualRowDCoefficient (A := A) W β S u) ^ 2
      ∂actualParisiFullQuerySpinLaw W Z β H) =
      (actualParisiQuerySigma W β S) ^ 2 * actualParisiFullSusceptibilityExpected W β S := by
  simp_rw [actualRowDCoefficient_eq_defect W β hβ, mul_pow]
  rw [integral_const_mul, actual_linked_defect_secondMoment W Z β hβ S H hSH,
    sigmaSquare_mul_defect_eq_susceptibility W β hβ S]

theorem measurable_actualRowDCoefficient_real
    (W : BrownianSystem Ω) (β : ℝ) :
    Measurable (fun p : ℝ × ((Bool × Ω) × A) =>
      actualRowDCoefficient W β p.1.toNNReal p.2) := by
  dsimp only [actualRowDCoefficient, actualParisiSpinLinkCoefficient]
  have hy : Measurable (fun p : ℝ × ((Bool × Ω) × A) =>
      actualParisiFullScalarProcess W β p.1.toNNReal p.2.1.2) := by
    have hm := measurable_fullScalar_real_shift W β 0
    simp only [zero_add] at hm
    have hp : Measurable (fun p : ℝ × ((Bool × Ω) × A) => (p.1, p.2.1.2)) :=
      measurable_fst.prodMk measurable_snd.fst.snd
    simpa only [Function.comp_def] using hm.comp hp
  have ht : Measurable (fun p : ℝ × ((Bool × Ω) × A) => (p.1.toNNReal : ℝ)) :=
    measurable_subtype_coe.comp (measurable_real_toNNReal.comp measurable_fst)
  have hs : Measurable (fun p : ℝ × ((Bool × Ω) × A) => scalarHiddenSign p.2.1.1) :=
    (measurable_of_finite scalarHiddenSign).comp measurable_snd.fst.fst
  have hm := (continuous_actualParisiFullMagnetization β).measurable.comp (ht.prodMk hy)
  have ha := (continuous_actualParisiFullCurvature β).measurable.comp (ht.prodMk hy)
  have hsig := (continuous_actualParisiQuerySigma W β).measurable.comp ht
  exact hsig.mul ((hs.mul ha).div (measurable_const.add (hs.mul hm)))

theorem actualRowDBracket_mean
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) :
    (∫ u, actualRowDBracket (A := A) W β V u ∂actualParisiFullQuerySpinLaw W Z β V) =
      ∫ t in (0 : ℝ)..(V : ℝ), (actualParisiQuerySigma W β t) ^ 2 *
        actualParisiFullSusceptibilityExpected W β t := by
  let ν := actualParisiFullQuerySpinLaw W Z β V
  let μ := volume.restrict (Ioc (0 : ℝ) V)
  let F : ℝ × ((Bool × Ω) × A) → ℝ := fun p =>
    (actualRowDCoefficient W β p.1.toNNReal p.2) ^ 2
  have hF : Integrable F (μ.prod ν) :=
    Integrable.of_bound ((measurable_actualRowDCoefficient_real (A := A) W β).pow_const 2).aestronglyMeasurable
      4 (ae_of_all _ (fun p => by
        change ‖(actualRowDCoefficient W β p.1.toNNReal p.2) ^ 2‖ ≤ 4
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have hb := actualRowDCoefficient_bound W β hβ p.1.toNNReal p.2
        simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using
          pow_le_pow_left₀ (abs_nonneg _) hb 2))
  unfold actualRowDBracket
  simp_rw [intervalIntegral.integral_of_le V.coe_nonneg]
  calc
    _ = ∫ t, ∫ u, F (t, u) ∂ν ∂μ :=
      (integral_integral_swap (μ := μ) (ν := ν) (f := fun t u => F (t, u)) hF).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have htV : t.toNNReal ≤ V := by
        apply NNReal.coe_le_coe.mp
        rw [Real.coe_toNNReal t ht.1.le]
        exact ht.2
      dsimp only [F, ν]
      rw [actualRowDCoefficient_secondMoment W Z β hβ _ V htV,
        Real.coe_toNNReal t ht.1.le]

end SKConstants.Completion.N7
