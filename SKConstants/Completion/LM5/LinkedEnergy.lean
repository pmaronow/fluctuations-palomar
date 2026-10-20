module

public import SKConstants.Completion.LM5.ActualCompletion
public import SKConstants.Completion.LM5.CompletionIntegrability
public import SKConstants.Completion.LM5.TraceMeasurability
public import SKConstants.Completion.LM5.TerminalSourceLaw
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix ENNReal NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Completion.LM5
open GaussianProposal LC5
variable {S Past : Type*} [MeasurableSpace S] [MeasurableSpace Past]

def visibleSpinCoefficients (r K : ℕ) (N : ℝ)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (initial : S → Past) (t : (Fin (r+K) → Bool) × (S × PaperCompletionNoise (r+K) K)) :=
  paperSpinCoefficients r K N target update (initial t.2.1)
    (visibleSource (r+K) K t.2.2) (signSpin t.1)

def visibleResidualSpin (r K : ℕ)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (initial : S → Past) (t : (Fin (r+K) → Bool) × (S × PaperCompletionNoise (r+K) K)) :=
  paperResidualSpin r K target update (initial t.2.1)
    (visibleSource (r+K) K t.2.2) (signSpin t.1)

def sourceDiscardedEnergy (r K : ℕ) (N : ℝ)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (initial : S → Past) (z : (Fin (r+K) → Bool) × (S × StoppedNoise (Fin (r+K)) K)) : ℝ :=
  quadraticEnergy N (signSpin z.1)
    (paperTensorProposal r (r+K) (skSigma N) target update K (initial z.2.1,1) z.2.2) -
      paperQueryEnergy r (r+K) N target update K (initial z.2.1,1) z.2.2 (signSpin z.1)

theorem measurable_visibleSpinCoefficients (r K : ℕ) (N : ℝ)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (initial : S → Past) (hi : Measurable initial)
    (htarget : ∀ k i, Measurable (fun a => target k a i))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k))) :
    Measurable (visibleSpinCoefficients r K N target update initial) :=
  (measurable_paperSpinCoefficients r K N target update htarget hupdate).comp
    (((hi.comp measurable_snd.fst).prodMk
      ((measurable_visibleSource (r+K) K).comp measurable_snd.snd)).prodMk
        ((measurable_signSpin (r+K)).comp measurable_fst))

theorem measurable_visibleResidualSpin (r K : ℕ)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (initial : S → Past) (hi : Measurable initial)
    (htarget : ∀ k i, Measurable (fun a => target k a i))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k))) :
    Measurable (visibleResidualSpin r K target update initial) :=
  (measurable_paperResidualSpin r K target update htarget hupdate).comp
    (((hi.comp measurable_snd.fst).prodMk
      ((measurable_visibleSource (r+K) K).comp measurable_snd.snd)).prodMk
        ((measurable_signSpin (r+K)).comp measurable_fst))

theorem sourceDiscardedEnergy_eq_completion (r K : ℕ) (N : ℝ) (hN : 0 < N)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (hblind : ∀ j p z w, (∀ i, z (.inl i) = w (.inl i)) → update j p z = update j p w)
    (initial : S → Past) (z : (Fin (r+K) → Bool) × (S × StoppedNoise (Fin (r+K)) K)) :
    sourceDiscardedEnergy r K N target update initial z =
      completionEnergy N
        (visibleSpinCoefficients r K N target update initial (terminalSourceCompact (r+K) K z).1)
        (visibleResidualSpin r K target update initial (terminalSourceCompact (r+K) K z).1)
        (terminalSourceCompact (r+K) K z).2 := by
  unfold sourceDiscardedEnergy
  rw [actualPaper_energy_eq_query_add_completion r K N hN]
  rw [paperSpinCoefficients_factors_visible r K N target update hblind,
    paperResidualSpin_factors_visible r K target update hblind]
  simp only [add_sub_cancel_left]
  rfl

theorem visible_completion_memLp_two (μ : Measure S) [IsProbabilityMeasure μ]
    (r K : ℕ) (hN : 0 < r+K) (β : ℝ) (H : ℝ≥0)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (initial : S → Past) (hi : Measurable initial)
    (htarget : ∀ k i, Measurable (fun a => target k a i))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k)))
    (Y : S × PaperCompletionNoise (r+K) K → Fin (r+K) → ℝ) (hY : Measurable Y) :
    MemLp (fun z => completionEnergy (r+K : ℕ)
      (visibleSpinCoefficients r K (r+K : ℕ) target update initial z.1)
      (visibleResidualSpin r K target update initial z.1) z.2) 2
      ((M1.TerminalLinkedLaw β H (μ.prod (paperCompletionNoiseLaw (r+K) K)) Y).prod
        (completionNoiseLaw (r+K) K)) := by
  have hp : (0 : ℝ) < (r+K : ℕ) := by exact_mod_cast hN
  let := M1.terminalLinkedLaw_probability β H (μ.prod (paperCompletionNoiseLaw (r+K) K)) Y hY
  apply completionEnergy_memLp_two _ _ hp _ _
    (measurable_visibleSpinCoefficients r K _ target update initial hi htarget hupdate)
    (measurable_visibleResidualSpin r K target update initial hi htarget hupdate)
  · intro t
    exact actualPaper_coefficient_budget r K _ hp target update _ _ _ (signSpin_norm_sq t.1)
  · intro t
    exact actualPaper_residual_norm_identity r K _ hp target update _ _ _ (signSpin_norm_sq t.1)

theorem sourceDiscardedEnergy_memLp_two (μ : Measure S) [IsProbabilityMeasure μ]
    (r K : ℕ) (hN : 0 < r+K) (β : ℝ) (H : ℝ≥0)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (initial : S → Past) (hi : Measurable initial)
    (htarget : ∀ k i, Measurable (fun a => target k a i))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k)))
    (hblind : ∀ j p z w, (∀ i, z (.inl i) = w (.inl i)) → update j p z = update j p w)
    (Y : S × PaperCompletionNoise (r+K) K → Fin (r+K) → ℝ) (hY : Measurable Y) :
    MemLp (sourceDiscardedEnergy r K (r+K : ℕ) target update initial) 2
      (terminalSourceLaw μ (r+K) K β H Y) := by
  have hp : (0 : ℝ) < (r+K : ℕ) := by exact_mod_cast hN
  have hmp : MeasurePreserving (terminalSourceCompact (r+K) K)
      (terminalSourceLaw μ (r+K) K β H Y)
      ((M1.TerminalLinkedLaw β H (μ.prod (paperCompletionNoiseLaw (r+K) K)) Y).prod
        (completionNoiseLaw (r+K) K)) :=
    ⟨measurable_terminalSourceCompact _ _, terminalSourceCompact_law μ _ _ β H Y hY⟩
  have h := (visible_completion_memLp_two μ r K hN β H target update initial hi htarget hupdate
    Y hY).comp_measurePreserving hmp
  have he : sourceDiscardedEnergy r K (r+K : ℕ) target update initial =
      (fun z => completionEnergy (r+K : ℕ)
        (visibleSpinCoefficients r K (r+K : ℕ) target update initial z.1)
        (visibleResidualSpin r K target update initial z.1) z.2) ∘ terminalSourceCompact (r+K) K :=
    funext fun z => sourceDiscardedEnergy_eq_completion r K _ hp target update hblind initial z
  rw [he]
  exact h

theorem sourceDiscardedEnergy_centered_test (μ : Measure S) [IsProbabilityMeasure μ]
    (r K : ℕ) (hN : 0 < r+K) (β : ℝ) (H : ℝ≥0)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (initial : S → Past) (hi : Measurable initial)
    (htarget : ∀ k i, Measurable (fun a => target k a i))
    (hupdate : ∀ k, Measurable (Function.uncurry (update k)))
    (hblind : ∀ j p z w, (∀ i, z (.inl i) = w (.inl i)) → update j p z = update j p w)
    (Y : S × PaperCompletionNoise (r+K) K → Fin (r+K) → ℝ) (hY : Measurable Y)
    (φ : (Fin (r+K) → Bool) × (S × PaperCompletionNoise (r+K) K) → ℝ)
    (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, |φ t| ≤ C) :
    Integrable (fun z => φ (terminalSourceCompact (r+K) K z).1 *
      sourceDiscardedEnergy r K (r+K : ℕ) target update initial z)
      (terminalSourceLaw μ (r+K) K β H Y) ∧
    (∫ z, φ (terminalSourceCompact (r+K) K z).1 *
      sourceDiscardedEnergy r K (r+K : ℕ) target update initial z
      ∂terminalSourceLaw μ (r+K) K β H Y) = 0 := by
  have hp : (0 : ℝ) < (r+K : ℕ) := by exact_mod_cast hN
  let ν := M1.TerminalLinkedLaw β H (μ.prod (paperCompletionNoiseLaw (r+K) K)) Y
  let := M1.terminalLinkedLaw_probability β H (μ.prod (paperCompletionNoiseLaw (r+K) K)) Y hY
  let c := visibleSpinCoefficients r K (r+K : ℕ) target update initial
  let y := visibleResidualSpin r K target update initial
  have hc := measurable_visibleSpinCoefficients r K (r+K : ℕ) target update initial hi htarget hupdate
  have hy := measurable_visibleResidualSpin r K target update initial hi htarget hupdate
  have hb : ∀ t, (∑ j, c t j^2) ≤ 1 := fun t =>
    actualPaper_coefficient_budget r K _ hp target update _ _ _ (signSpin_norm_sq t.1)
  have hn : ∀ t, ((r+K : ℕ) : ℝ)⁻¹ * dot (y t) (y t) = 1-∑ j, c t j^2 := fun t =>
    actualPaper_residual_norm_identity r K _ hp target update _ _ _ (signSpin_norm_sq t.1)
  have hint := bounded_transcript_completion_integrable ν _ hp c y hc hy hb hn φ hφ C hC
  have hzero := bounded_transcript_completion_centered ν _ hp c y hc hy hb hn φ hφ C hC
  have hmp : MeasurePreserving (terminalSourceCompact (r+K) K)
      (terminalSourceLaw μ (r+K) K β H Y) (ν.prod (completionNoiseLaw (r+K) K)) :=
    ⟨measurable_terminalSourceCompact _ _, terminalSourceCompact_law μ _ _ β H Y hY⟩
  have he : (fun z => φ (terminalSourceCompact (r+K) K z).1 *
      sourceDiscardedEnergy r K (r+K : ℕ) target update initial z) =
      (fun z => φ z.1 * completionEnergy (r+K : ℕ) (c z.1) (y z.1) z.2) ∘
        terminalSourceCompact (r+K) K := by
    funext z
    rw [sourceDiscardedEnergy_eq_completion r K _ hp target update hblind]
    rfl
  rw [he]
  exact ⟨hmp.integrable_comp_of_integrable hint,
    (hmp.hasLaw.integral_comp hint.aestronglyMeasurable).trans hzero⟩

end SKConstants.Completion.LM5
