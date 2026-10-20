module

public import SKConstants.Completion.LM5.GrowingLinkedEnergy
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open SKConstantsOAI.ZeroTemperatureSK
open scoped BigOperators Matrix NNReal ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Completion.LM5
open GaussianProposal LC5
variable {Ω : Type*} [MeasurableSpace Ω]

def growingSourceCompact (δ : ℝ≥0) (r K : ℕ)
    (z : (Fin (r+K) → Bool) × M1.SourceInput δ r K) :=
  terminalSourceCompact (r+K) K (z.1,growingProjectOriginal δ r K z.2)

theorem measurable_growingSourceCompact (δ : ℝ≥0) (r K : ℕ) :
    Measurable (growingSourceCompact δ r K) :=
  (measurable_terminalSourceCompact (r+K) K).comp
    (measurable_id.prodMap (measurable_growingProjectOriginal δ r K))

theorem growingSourceCompact_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) :
    (M1.SourceLinkedLaw W β hβ δ r K).map (growingSourceCompact δ r K) =
      (M1.TerminalLinkedLaw β (M1.Horizon δ K)
        ((scalarGrowingPaperInitialDataLaw W (M1.Horizon δ K) δ (r+K)).prod
          (paperCompletionNoiseLaw (r+K) K)) (growingVisibleField W β hβ δ r K)).prod
            (completionNoiseLaw (r+K) K) := by
  change (M1.SourceLinkedLaw W β hβ δ r K).map
    (terminalSourceCompact (r+K) K ∘ Prod.map id (growingProjectOriginal δ r K)) = _
  rw [← Measure.map_map (measurable_terminalSourceCompact (r+K) K)
    (measurable_id.prodMap (measurable_growingProjectOriginal δ r K)),
    growingSource_linked_original_law,
    terminalSourceCompact_law _ _ _ β (M1.Horizon δ K) _
      (measurable_growingVisibleField W β hβ δ r K)]

theorem growingSourceDiscardedEnergy_eq_completion (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) (hN : 0 < r+K)
    (z : (Fin (r+K) → Bool) × M1.SourceInput δ r K) :
    growingSourceDiscardedEnergy W β hβ δ r K z =
      completionEnergy (r+K : ℕ)
        (visibleSpinCoefficients r K (r+K : ℕ) (M1.Target W β hβ δ r K) (M1.Update δ r K)
          (growingInitial δ r K) (growingSourceCompact δ r K z).1)
        (visibleResidualSpin r K (M1.Target W β hβ δ r K) (M1.Update δ r K)
          (growingInitial δ r K) (growingSourceCompact δ r K z).1)
        (growingSourceCompact δ r K z).2 := by
  have hp : (0 : ℝ) < (r+K : ℕ) := by exact_mod_cast hN
  exact sourceDiscardedEnergy_eq_completion r K _ hp (M1.Target W β hβ δ r K)
    (M1.Update δ r K) (growingUpdate_blind δ r K) (growingInitial δ r K) _

theorem growingSource_completion_gaussian (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (hN : 0 < r+K)
    (t : (Fin (r+K) → Bool) × GrowingVisible δ r K) :
    let c := visibleSpinCoefficients r K (r+K : ℕ) (M1.Target W β hβ δ r K) (M1.Update δ r K)
      (growingInitial δ r K) t
    let y := visibleResidualSpin r K (M1.Target W β hβ δ r K) (M1.Update δ r K)
      (growingInitial δ r K) t
    HasLaw (completionEnergy (r+K : ℕ) c y)
      (gaussianReal 0 (completionVariance (r+K : ℕ) c y).toNNReal)
      (completionNoiseLaw (r+K) K) ∧
      completionVariance (r+K : ℕ) c y ≤ (1/2 : ℝ)*((r+K : ℕ) : ℝ)⁻¹ :=
  actualPaper_sign_completion_law r K hN (M1.Target W β hβ δ r K) (M1.Update δ r K)
    (growingInitial δ r K t.2.1) t.2.2 t.1

theorem growingSource_completion_tail (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (hN : 0 < r+K)
    (t : (Fin (r+K) → Bool) × GrowingVisible δ r K) (u : ℝ) (hu : 0 < u) :
    (completionNoiseLaw (r+K) K).real {w | u ≤ |completionEnergy (r+K : ℕ)
      (visibleSpinCoefficients r K (r+K : ℕ) (M1.Target W β hβ δ r K) (M1.Update δ r K)
        (growingInitial δ r K) t)
      (visibleResidualSpin r K (M1.Target W β hβ δ r K) (M1.Update δ r K)
        (growingInitial δ r K) t) w|} ≤ 2*Real.exp (-((r+K : ℕ) : ℝ)*u^2) :=
  actualPaper_sign_completion_tail r K hN (M1.Target W β hβ δ r K) (M1.Update δ r K)
    (growingInitial δ r K t.2.1) t.2.2 t.1 u hu

theorem completionEnergy_joint_second_moment_le {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {n k : ℕ} (N : ℝ) (hN : 0 < N)
    (c : S → Fin k → ℝ) (y : S → Fin n → ℝ) (hc : Measurable c) (hy : Measurable y)
    (hb : ∀ t, (∑ j, c t j^2) ≤ 1)
    (hn : ∀ t, N⁻¹*dot (y t) (y t) = 1-∑ j, c t j^2) :
    (∫ z, (completionEnergy N (c z.1) (y z.1) z.2)^2 ∂μ.prod (completionNoiseLaw n k)) ≤
      (1/2 : ℝ)*N⁻¹ := by
  have hi := (completionEnergy_memLp_two μ N hN c y hc hy hb hn).integrable_sq
  have hiv := hi.integral_prod_left
  rw [integral_prod _ hi]
  simp_rw [completion_second_moment N hN] at hiv ⊢
  calc
    _ ≤ ∫ _ : S, (1/2 : ℝ)*N⁻¹ ∂μ := integral_mono hiv (integrable_const _)
      (fun t => completionVariance_le N hN _ _ (hb t) (hn t))
    _ = _ := by simp

theorem growingSourceDiscardedEnergy_mean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (hN : 0 < r+K) :
    (∫ z, growingSourceDiscardedEnergy W β hβ δ r K z ∂M1.SourceLinkedLaw W β hβ δ r K) = 0 := by
  have h := growingSourceDiscardedEnergy_centered_test W β hβ δ r K hN
    (fun _ => 1) measurable_const 1 (fun _ => by norm_num)
  simpa only [one_mul] using h.2

theorem growingSourceDiscardedEnergy_second_moment_le (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) (hN : 0 < r+K) :
    (∫ z, (growingSourceDiscardedEnergy W β hβ δ r K z)^2
      ∂M1.SourceLinkedLaw W β hβ δ r K) ≤ (1/2 : ℝ)*((r+K : ℕ) : ℝ)⁻¹ := by
  have hp : (0 : ℝ) < (r+K : ℕ) := by exact_mod_cast hN
  let ν := M1.TerminalLinkedLaw β (M1.Horizon δ K)
    ((scalarGrowingPaperInitialDataLaw W (M1.Horizon δ K) δ (r+K)).prod
      (paperCompletionNoiseLaw (r+K) K)) (growingVisibleField W β hβ δ r K)
  let c := visibleSpinCoefficients r K (r+K : ℕ) (M1.Target W β hβ δ r K) (M1.Update δ r K)
    (growingInitial δ r K)
  let y := visibleResidualSpin r K (M1.Target W β hβ δ r K) (M1.Update δ r K)
    (growingInitial δ r K)
  let := M1.terminalLinkedLaw_probability β (M1.Horizon δ K)
    ((scalarGrowingPaperInitialDataLaw W (M1.Horizon δ K) δ (r+K)).prod
      (paperCompletionNoiseLaw (r+K) K)) (growingVisibleField W β hβ δ r K)
        (measurable_growingVisibleField W β hβ δ r K)
  have hc : Measurable c := measurable_visibleSpinCoefficients r K _ _ _ _
    (measurable_scalarGrowingPaperInitialState _ _ _) (measurable_growingTarget W β hβ δ r K)
    (measurable_growingUpdate δ r K)
  have hy : Measurable y := measurable_visibleResidualSpin r K _ _ _
    (measurable_scalarGrowingPaperInitialState _ _ _) (measurable_growingTarget W β hβ δ r K)
    (measurable_growingUpdate δ r K)
  have hb : ∀ t, (∑ j, c t j^2) ≤ 1 := fun t => actualPaper_coefficient_budget r K _ hp
    (M1.Target W β hβ δ r K) (M1.Update δ r K) _ _ _ (signSpin_norm_sq t.1)
  have hn : ∀ t, ((r+K : ℕ) : ℝ)⁻¹*dot (y t) (y t) = 1-∑ j, c t j^2 := fun t =>
    actualPaper_residual_norm_identity r K _ hp (M1.Target W β hβ δ r K)
      (M1.Update δ r K) _ _ _ (signSpin_norm_sq t.1)
  have hmp : MeasurePreserving (growingSourceCompact δ r K)
      (M1.SourceLinkedLaw W β hβ δ r K) (ν.prod (completionNoiseLaw (r+K) K)) :=
    ⟨measurable_growingSourceCompact δ r K, growingSourceCompact_law W β hβ δ r K⟩
  have hi := (completionEnergy_memLp_two ν _ hp c y hc hy hb hn).integrable_sq
  have he : (fun z => (growingSourceDiscardedEnergy W β hβ δ r K z)^2) =
      (fun z => (completionEnergy (r+K : ℕ) (c z.1) (y z.1) z.2)^2) ∘
        growingSourceCompact δ r K := by
    funext z
    rw [growingSourceDiscardedEnergy_eq_completion W β hβ δ r K hN]
    rfl
  rw [he]
  exact (hmp.hasLaw.integral_comp hi.aestronglyMeasurable).trans_le
    (completionEnergy_joint_second_moment_le ν _ hp c y hc hy hb hn)

theorem growingSourceDiscardedEnergy_variance_le (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) (hN : 0 < r+K) :
    Var[growingSourceDiscardedEnergy W β hβ δ r K; M1.SourceLinkedLaw W β hβ δ r K] ≤
      (1/2 : ℝ)*((r+K : ℕ) : ℝ)⁻¹ := by
  rw [variance_eq_integral (growingSourceDiscardedEnergy_memLp_two W β hβ δ r K hN).aemeasurable,
    growingSourceDiscardedEnergy_mean W β hβ δ r K hN]
  simpa only [sub_zero] using growingSourceDiscardedEnergy_second_moment_le W β hβ δ r K hN

end SKConstants.Completion.LM5
