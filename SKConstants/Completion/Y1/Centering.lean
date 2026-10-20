module

public import SKConstants.Completion.Y1.SourceMoments
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace SKConstants.Completion.Y1
open SKConstantsOAI.ZeroTemperatureSK LFine N9b M1
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem actualIncrement_past_test_zero (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ≥0) (hst : s ≤ t) (F : (Iic s → ℝ) → ℝ)
    (hF : Measurable F) (hcap : ∀ p, |F p| ≤ 1) :
    (∫ w, F (brownianFullPast W.B s w)*actualParisiMagnetizationIncrement W β s t w ∂W.law) = 0 := by
  let b := actualParisiFullScalarDrift β
  let G := F ∘ LC1.boundedDriftRecoverBrownianPast b s
  have hG : Measurable G := hF.comp (LC1.measurable_boundedDriftRecoverBrownianPast b s)
  have h := actualParisiFullProcess_martingale_test W β hβ s (t-s) G hG 1 (fun p => hcap _)
  rw [add_tsub_cancel_of_le hst] at h
  have hr : (s : ℝ)+((t-s : ℝ≥0) : ℝ) = (t : ℝ) := by
    exact_mod_cast add_tsub_cancel_of_le hst
  rw [hr] at h
  refine (integral_congr_ae ?_).trans h
  filter_upwards [LC1.boundedDriftRecoverBrownianPast_actual W b s] with w hw
  change F _ * _ = F _ * _
  rw [hw]
  rfl

theorem actualIncrement_static_past_test_zero
    (W : BrownianSystem Ω) (P : Measure A) [IsProbabilityMeasure P]
    (β : ℝ) (hβ : 1 < β) (s t : ℝ≥0) (hst : s ≤ t)
    (F : (Iic s → ℝ) × A → ℝ) (hF : Measurable F) (hcap : ∀ p, |F p| ≤ 1) :
    (∫ u, F (brownianFullPast W.B s u.1,u.2)*
      actualParisiMagnetizationIncrement W β s t u.1 ∂W.law.prod P) = 0 := by
  let := W.isProbability
  have hm : Measurable (fun u : Ω × A => F (brownianFullPast W.B s u.1,u.2)*
      actualParisiMagnetizationIncrement W β s t u.1) :=
    (hF.comp (((Measurable.of_eval fun v : Iic s => W.measurable v).comp measurable_fst).prodMk
      measurable_snd)).mul ((measurable_actualParisiMagnetizationIncrement W β s t).comp measurable_fst)
  have hi : Integrable (fun u : Ω × A => F (brownianFullPast W.B s u.1,u.2)*
      actualParisiMagnetizationIncrement W β s t u.1) (W.law.prod P) :=
    Integrable.of_bound hm.aestronglyMeasurable 2 (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs,abs_mul]
      exact (mul_le_mul (hcap _) (actualParisiMagnetizationIncrement_abs_le W β s t u.1)
        (abs_nonneg _) (by norm_num)).trans_eq (by norm_num))
  rw [integral_prod_symm _ hi]
  simp only [actualIncrement_past_test_zero W β hβ s t hst
    (fun p => F (p,_)) (hF.comp (measurable_id.prodMk measurable_const)) (fun p => hcap _),
    integral_zero]

theorem normalizedIncrement_driverPast_test_zero
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ≥0) (hst : s ≤ t)
    (F : ScalarContinuousPath s × ScalarContinuousPath s → ℝ)
    (hF : Measurable F) (hcap : ∀ p, |F p| ≤ 1) :
    (∫ u, F (modelDriverPast W Z β hβ s u)*normalizedIncrement W β s t u.1
      ∂W.law.prod Z.law) = 0 := by
  let := Z.isProbability
  let T := WeightedPair (actualParisiNegativeRhoStieltjes W β hβ)
    (actualParisiSigmaStieltjes W β hβ) (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ) s
  let G : (Iic s → ℝ) × A → ℝ := fun p =>
    F (T (scalarPathFromPast s p.1,scalarPrimitiveBrownianPathVersion Z s p.2))
  have hG : Measurable G := hF.comp ((measurable_WeightedPair _ _ _ _ s).comp
    (((measurable_scalarPathFromPast s).comp measurable_fst).prodMk
      ((measurable_scalarPrimitiveBrownianPathVersion Z s).comp measurable_snd)))
  have he : (fun u => F (modelDriverPast W Z β hβ s u)*normalizedIncrement W β s t u.1) =ᵐ[
      W.law.prod Z.law] (fun u => G (brownianFullPast W.B s u.1,u.2)*normalizedIncrement W β s t u.1) :=
    (modelDriverPast_eq_weighted_ae W Z β hβ s).mono fun u hu =>
      congrArg (fun p => F p*normalizedIncrement W β s t u.1) hu
  rw [integral_congr_ae he]
  simp only [normalizedIncrement,← mul_div_assoc,integral_div,
    actualIncrement_static_past_test_zero W Z.law β hβ s t hst G hG (fun p => hcap _),zero_div]

theorem sourceTarget_past_test_zero (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) (i : Fin (r+K))
    (F : ScalarContinuousPath (growingQueryTime δ e.val) ×
      ScalarContinuousPath (growingQueryTime δ e.val) → ℝ)
    (hF : Measurable F) (hcap : ∀ p, |F p| ≤ 1) :
    (∫ z, F (N9c.historyDriverPast (growingQueryTime δ e.val) (Horizon δ K)
      ((growingQueryTime_strictMono δ hδ).monotone (by omega))
      (SourceHistories W β hβ δ r K z i))*SourceTargets W β hβ δ r K z.2 e i
        ∂SourceLinkedLaw W β hβ δ r K) = 0 := by
  rw [sourcePastTarget_integral_eq_model W β hβ δ hδ r K e i (fun p => F p.1*p.2) (by fun_prop)]
  exact normalizedIncrement_driverPast_test_zero W W β hβ _ _
    ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ _)) F hF hcap

end SKConstants.Completion.Y1
