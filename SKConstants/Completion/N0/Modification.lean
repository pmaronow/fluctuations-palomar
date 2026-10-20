module

public import SKConstants.Completion.N0.Canonical
public import BrownianMotion.Continuity.KolmogorovChentsov
public import SKConstants.ScalarProcessPosteriorIncrement

@[expose] public section

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace SKConstants.N0

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

theorem lintegral_increment_fourth (hX : IsPreBrownianReal X P) (s t : ℝ≥0) :
    (∫⁻ ω, edist (X s ω) (X t ω) ^ (4 : ℝ) ∂P) = 3 * edist s t ^ (2 : ℝ) := by
  norm_cast
  simp_rw [edist_dist, Real.dist_eq]
  change (∫⁻ ω, (fun x : ℝ => (ENNReal.ofReal |x|) ^ (4 : ℕ))
    ((X s - X t) ω) ∂P) = _
  rw [(hX.hasLaw_sub s t).lintegral_comp
    (f := fun x : ℝ => (ENNReal.ofReal |x|) ^ (4 : ℕ)) (by fun_prop)]
  simp_rw [← ENNReal.ofReal_pow (abs_nonneg _), (by decide : Even (4 : ℕ)).pow_abs]
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [gaussianReal_integral_fourth]
    simp only [zero_pow (by decide : (4 : ℕ) ≠ 0), zero_pow (by decide : (2 : ℕ) ≠ 0),
      mul_zero, zero_add]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
    simp
    rfl
  · exact gaussianReal_integrable_pow 0 _ 4
  · exact ae_of_all _ fun x => (by decide : Even (4 : ℕ)).pow_nonneg x

theorem isKolmogorovProcess_fourth (hX : IsPreBrownianReal X P)
    (hm : ∀ t, Measurable (X t)) : IsKolmogorovProcess X P 4 2 3 := by
  apply IsKolmogorovProcess.mk_of_secondCountableTopology hm
  · intro s t
    exact (lintegral_increment_fourth hX s t).le
  · norm_num
  · norm_num

theorem exists_continuous_modification (hX : IsPreBrownianReal X P)
    (hm : ∀ t, Measurable (X t)) :
    ∃ Y : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t) ∧
      ∀ ω, Continuous (Y · ω) := by
  have := (hX.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨Y, hYm, hYX, hY⟩ := exists_modification_holder'
    isCoverWithBoundedCoveringNumber_Ico_nnreal
    (isKolmogorovProcess_fourth hX hm).IsAEKolmogorovProcess
    (fun n => by finiteness) (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
  refine ⟨Y, hYm, hYX, fun ω => continuous_iff_continuousAt.mpr fun t => ?_⟩
  obtain ⟨U, hUt, hU⟩ := hY ω t
  obtain ⟨C, hC⟩ := hU (1 / 8) (by norm_num) (by norm_num)
  exact (hC.continuousOn (by norm_num)).continuousAt hUt

def brownian : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ :=
  (exists_continuous_modification isPreBrownianReal_preBrownian measurable_preBrownian).choose

@[fun_prop]
theorem measurable_brownian (t : ℝ≥0) : Measurable (brownian t) :=
  (exists_continuous_modification isPreBrownianReal_preBrownian
    measurable_preBrownian).choose_spec.1 t

theorem brownian_ae_eq (t : ℝ≥0) : brownian t =ᵐ[gaussianPathLaw] preBrownian t :=
  (exists_continuous_modification isPreBrownianReal_preBrownian
    measurable_preBrownian).choose_spec.2.1 t

theorem continuous_brownian (ω : ℝ≥0 → ℝ) : Continuous (brownian · ω) :=
  (exists_continuous_modification isPreBrownianReal_preBrownian
    measurable_preBrownian).choose_spec.2.2 ω

theorem isBrownianReal_brownian : IsBrownianReal brownian gaussianPathLaw where
  toIsPreBrownianReal := isPreBrownianReal_preBrownian.congr fun t => (brownian_ae_eq t).symm
  cont := ae_of_all _ continuous_brownian

end SKConstants.N0
