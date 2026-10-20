module

public import SKConstants.ParisiFullMixedRows
public import SKConstants.ScalarOrthogonalDriverMarkov

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants.Completion.LC1
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem actualQuery_increment_indep_adapted
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (a v : ℝ≥0) (F : Ω → ℝ)
    (hF : Measurable[Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable) a] F) :
    IndepFun (fun u : Ω × A =>
      (actualParisiQueryBrownianSystem W Z β hβ).B (a+v) u -
        (actualParisiQueryBrownianSystem W Z β hβ).B a u)
      (fun u => F u.1) (W.law.prod Z.law) := by
  rw [Filtration.natural_eq_comap] at hF
  obtain ⟨G, hG, he⟩ := hF.exists_eq_measurable_comp
  have hi := (actualParisiQuery_future_indep_originalPast W Z β hβ a).comp
    (measurable_pi_apply v) (hG.comp measurable_fst)
  simpa only [he, Function.comp_def] using hi

theorem actualQuery_increment_integral_adapted
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (a v : ℝ≥0) (F : Ω → ℝ)
    (hF : Measurable[Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable) a] F)
    (hFi : Integrable F W.law) :
    (∫ u : Ω × A, F u.1 *
      ((actualParisiQueryBrownianSystem W Z β hβ).B (a+v) u -
        (actualParisiQueryBrownianSystem W Z β hβ).B a u) ∂W.law.prod Z.law) = 0 := by
  let := W.isProbability
  let := Z.isProbability
  let Q := actualParisiQueryBrownianSystem W Z β hβ
  have hQ : AEStronglyMeasurable (fun u => Q.B (a+v) u - Q.B a u) (W.law.prod Z.law) :=
    ((Q.measurable _).sub (Q.measurable _)).aestronglyMeasurable
  have hi := (actualQuery_increment_indep_adapted W Z β hβ a v F hF).symm
  rw [hi.integral_fun_mul_eq_mul_integral
    (hFi.comp_fst Z.law).aestronglyMeasurable hQ]
  have hz : (∫ u, Q.B (a+v) u - Q.B a u ∂W.law.prod Z.law) = 0 := by
    change (∫ u, Q.B (a+v) u - Q.B a u ∂Q.law) = 0
    rw [integral_sub (Q.brownian.integrable_eval _) (Q.brownian.integrable_eval _),
      Q.brownian.toIsPreBrownianReal.integral_eval,
      Q.brownian.toIsPreBrownianReal.integral_eval, sub_self]
  rw [hz, mul_zero]

lemma actualMagnetization_adapted_le (W : BrownianSystem Ω) (β : ℝ)
    (t a : ℝ≥0) (hta : t ≤ a) :
    Measurable[Filtration.natural W.B (fun s => (W.measurable s).stronglyMeasurable) a]
      (actualParisiMagnetizationObservable W β t) := by
  have hy := (actualParisiFullScalarDrift β).solution_adapted W t
  have hy' := hy.mono ((Filtration.natural W.B
    (fun s => (W.measurable s).stronglyMeasurable)).mono hta) le_rfl
  exact ((continuous_actualParisiFullMagnetization β).comp
    (continuous_const.prodMk continuous_id)).measurable.comp hy'

theorem actualPosterior_query_upper_moment
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (S T a v : ℝ≥0) (hST : S ≤ T) (hTa : T ≤ a) :
    (∫ u : Ω × A, actualParisiMagnetizationIncrement W β S T u.1 *
      ((actualParisiQueryBrownianSystem W Z β hβ).B (a+v) u -
        (actualParisiQueryBrownianSystem W Z β hβ).B a u) ∂W.law.prod Z.law) = 0 := by
  apply actualQuery_increment_integral_adapted W Z β hβ a v
  · exact (actualMagnetization_adapted_le W β T a hTa).sub
      (actualMagnetization_adapted_le W β S a (hST.trans hTa))
  · exact (integrable_actualParisiMagnetizationObservable W β T).sub
      (integrable_actualParisiMagnetizationObservable W β S)

theorem actualQuerySpinLaw_posterior_query_upper_moment
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (S T a v H : ℝ≥0) (hST : S ≤ T) (hTa : T ≤ a) :
    (∫ u, actualParisiMagnetizationIncrement W β S T u.1.2 *
      ((actualParisiQueryBrownianSystem W Z β hβ).B (a+v) (u.1.2,u.2) -
        (actualParisiQueryBrownianSystem W Z β hβ).B a (u.1.2,u.2))
      ∂actualParisiFullQuerySpinLaw W Z β H) = 0 := by
  have hm : Measurable (fun u : Ω × A => actualParisiMagnetizationIncrement W β S T u.1 *
      ((actualParisiQueryBrownianSystem W Z β hβ).B (a+v) u -
        (actualParisiQueryBrownianSystem W Z β hβ).B a u)) :=
    ((measurable_actualParisiMagnetizationIncrement W β S T).comp measurable_fst).mul
      (((actualParisiQueryBrownianSystem W Z β hβ).measurable _).sub
        ((actualParisiQueryBrownianSystem W Z β hβ).measurable _))
  exact ((actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).integral_comp
    hm.aestronglyMeasurable).trans (actualPosterior_query_upper_moment W Z β hβ S T a v hST hTa)

theorem actualQuerySpinLaw_normalized_upper_moment
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t q : ℕ → ℝ≥0) (d : ℕ) (i j : Fin d) (H : ℝ≥0)
    (ht : t i ≤ t (i+1)) (hq : q j ≤ q (j+1)) (hij : t (i+1) ≤ q j) :
    (∫ u, actualParisiNormalizedPosteriorRow W β t d u.1.2 i *
      scalarNormalizedBrownianRow (d:=d) (actualParisiQueryBrownianSystem W Z β hβ).B q
        (u.1.2,u.2) j ∂actualParisiFullQuerySpinLaw W Z β H) = 0 := by
  have he (u : (Bool × Ω) × A) :
      actualParisiNormalizedPosteriorRow W β t d u.1.2 i *
        scalarNormalizedBrownianRow (d:=d) (actualParisiQueryBrownianSystem W Z β hβ).B q
          (u.1.2,u.2) j =
      (actualParisiMagnetizationIncrement W β (t i) (t (i+1)) u.1.2 *
        ((actualParisiQueryBrownianSystem W Z β hβ).B (q (j+1)) (u.1.2,u.2) -
          (actualParisiQueryBrownianSystem W Z β hβ).B (q j) (u.1.2,u.2))) /
        (actualParisiPosteriorIntervalScale W β (t i) (t (i+1)) : ℝ) /
        Real.sqrt ((q (j+1) : ℝ) - (q j : ℝ)) := by
    simp only [actualParisiNormalizedPosteriorRow, scalarNormalizedBrownianRow]
    ring
  simp_rw [he]
  rw [integral_div, integral_div]
  have hz := actualQuerySpinLaw_posterior_query_upper_moment W Z β hβ
    (t i) (t (i+1)) (q j) (q (j+1)-q j) H ht hij
  rw [add_tsub_cancel_of_le hq] at hz
  rw [hz, zero_div, zero_div]

theorem actualQuerySpinLaw_shifted_upper_block
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (d : ℕ) (H : ℝ≥0) :
    ∀ i j : Fin d, i ≤ j →
      (∫ u, actualParisiNormalizedPosteriorRow W β t d u.1.2 i *
        scalarNormalizedBrownianRow (d:=d) (actualParisiQueryBrownianSystem W Z β hβ).B
          (fun k => t (k+1)) (u.1.2,u.2) j ∂actualParisiFullQuerySpinLaw W Z β H) = 0 := by
  intro i j hij
  apply actualQuerySpinLaw_normalized_upper_moment
  · exact ht (Nat.le_succ _)
  · exact ht (Nat.le_succ _)
  · exact ht (Nat.add_le_add_right hij 1)

end SKConstants.Completion.LC1
