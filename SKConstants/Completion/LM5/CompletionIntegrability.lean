module

public import SKConstants.Completion.LC5.CompletionLaws
public import SKConstants.Completion.LC0.TerminalLinkLaw
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Completion.LM5
open GaussianProposal LC5

theorem measurable_completionEnergy {Ω : Type*} [MeasurableSpace Ω] {n k : ℕ}
    (N : ℝ) (c : Ω → Fin k → ℝ) (y : Ω → Fin n → ℝ)
    (hc : Measurable c) (hy : Measurable y) :
    Measurable (fun z : Ω × (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin n × Fin n)) =>
      completionEnergy N (c z.1) (y z.1) z.2) := by
  simp only [completionEnergy, discardedDiagonalEnergy, quadraticEnergy_goe,
    goeBilinear, linearForm]
  fun_prop

theorem completion_second_moment {n k : ℕ} (N : ℝ) (hN : 0 < N)
    (c : Fin k → ℝ) (y : Fin n → ℝ) :
    ∫ z, (completionEnergy N c y z)^2 ∂completionNoiseLaw n k =
      completionVariance N c y := by
  have hv := completion_variance N hN c y
  rw [variance_eq_integral (completion_law N hN c y).aemeasurable,
    completion_mean N hN c y] at hv
  simpa only [sub_zero] using hv

theorem completionEnergy_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {n k : ℕ} (N : ℝ) (hN : 0 < N)
    (c : Ω → Fin k → ℝ) (y : Ω → Fin n → ℝ)
    (hc : Measurable c) (hy : Measurable y)
    (hbudget : ∀ a, (∑ j, c a j^2) ≤ 1)
    (hnorm : ∀ a, N⁻¹ * dot (y a) (y a) = 1-∑ j, c a j^2) :
    MemLp (fun z : Ω × _ => completionEnergy N (c z.1) (y z.1) z.2) 2
      (μ.prod (completionNoiseLaw n k)) := by
  have hm := measurable_completionEnergy N c y hc hy
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  apply (integrable_prod_iff (hm.pow_const 2).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun a =>
      (completion_law N hN (c a) (y a)).hasGaussianLaw.memLp_two.integrable_sq
  · have he (a : Ω) :
        (∫ z, ‖(completionEnergy N (c a) (y a) z)^2‖ ∂completionNoiseLaw n k) =
        completionVariance N (c a) (y a) := by
      simp only [Real.norm_eq_abs, abs_sq]
      exact completion_second_moment N hN _ _
    simp_rw [he]
    apply (integrable_const ((1/2 : ℝ)*N⁻¹)).mono'
    · unfold completionVariance dot
      fun_prop
    · exact Filter.Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ completionVariance N (c a) (y a) by
          unfold completionVariance; positivity)]
        exact completionVariance_le N hN _ _ (hbudget a) (hnorm a)

theorem bounded_transcript_completion_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {n k : ℕ} (N : ℝ) (hN : 0 < N)
    (c : Ω → Fin k → ℝ) (y : Ω → Fin n → ℝ)
    (hc : Measurable c) (hy : Measurable y)
    (hbudget : ∀ a, (∑ j, c a j^2) ≤ 1)
    (hnorm : ∀ a, N⁻¹ * dot (y a) (y a) = 1-∑ j, c a j^2)
    (φ : Ω → ℝ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ a, |φ a| ≤ C) :
    Integrable (fun z : Ω × _ => φ z.1 * completionEnergy N (c z.1) (y z.1) z.2)
      (μ.prod (completionNoiseLaw n k)) := by
  have hi := (completionEnergy_memLp_two μ N hN c y hc hy hbudget hnorm).integrable
    (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h := hi.bdd_smul C
    (hφ.comp measurable_fst).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => (show ‖φ z.1‖ ≤ C by simpa using hC z.1))
  convert h using 1
  funext z
  rfl

theorem bounded_transcript_completion_centered {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {n k : ℕ} (N : ℝ) (hN : 0 < N)
    (c : Ω → Fin k → ℝ) (y : Ω → Fin n → ℝ)
    (hc : Measurable c) (hy : Measurable y)
    (hbudget : ∀ a, (∑ j, c a j^2) ≤ 1)
    (hnorm : ∀ a, N⁻¹ * dot (y a) (y a) = 1-∑ j, c a j^2)
    (φ : Ω → ℝ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ a, |φ a| ≤ C) :
    ∫ z, φ z.1 * completionEnergy N (c z.1) (y z.1) z.2
      ∂μ.prod (completionNoiseLaw n k) = 0 :=
  transcript_completion_centered_test μ N hN c y φ
    (bounded_transcript_completion_integrable μ N hN c y hc hy hbudget hnorm φ hφ C hC)

theorem terminalLinked_completion_centered {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {n k : ℕ}
    (β : ℝ) (H : ℝ≥0) (Y : S → Fin n → ℝ) (hY : Measurable Y)
    (N : ℝ) (hN : 0 < N)
    (c : (Fin n → Bool) × S → Fin k → ℝ)
    (y : (Fin n → Bool) × S → Fin n → ℝ)
    (hc : Measurable c) (hy : Measurable y)
    (hbudget : ∀ a, (∑ j, c a j^2) ≤ 1)
    (hnorm : ∀ a, N⁻¹ * dot (y a) (y a) = 1-∑ j, c a j^2)
    (φ : (Fin n → Bool) × S → ℝ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ a, |φ a| ≤ C) :
    ∫ z, φ z.1 * completionEnergy N (c z.1) (y z.1) z.2
      ∂(M1.TerminalLinkedLaw β H μ Y).prod (completionNoiseLaw n k) = 0 := by
  let := M1.terminalLinkedLaw_probability β H μ Y hY
  exact bounded_transcript_completion_centered _ N hN c y hc hy hbudget hnorm φ hφ C hC

end SKConstants.Completion.LM5
