module

public import SKConstants.Completion.N9Y1.Node
public import SKConstants.Completion.N9c.Node
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace SKConstants.Completion.Y1
open SKConstantsOAI.ZeroTemperatureSK LFine N9b M1
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem actualIncrement_static_past_weighted_moments_le
    (W : BrownianSystem Ω) (P : Measure A) [IsProbabilityMeasure P]
    (β : ℝ) (hβ : 1 < β) (s t : ℝ≥0) (hst : s ≤ t)
    (F : (Iic s → ℝ) × A → ℝ) (hF : Measurable F)
    (hcap : ∀ u, |F u| ≤ 1) :
    (∫ u, (F (brownianFullPast W.B s u.1,u.2) *
        actualParisiMagnetizationIncrement W β s t u.1)^2 ∂W.law.prod P) ≤
      ((t : ℝ)-s) * (∫ u, F (brownianFullPast W.B s u.1,u.2)^2 ∂W.law.prod P) ∧
    (∫ u, (F (brownianFullPast W.B s u.1,u.2) *
        actualParisiMagnetizationIncrement W β s t u.1)^4 ∂W.law.prod P) ≤
      3*((t : ℝ)-s)^2 * (∫ u, F (brownianFullPast W.B s u.1,u.2)^2 ∂W.law.prod P) := by
  let := W.isProbability
  let f := fun u : Ω × A => F (brownianFullPast W.B s u.1,u.2)
  let X := fun u : Ω × A => actualParisiMagnetizationIncrement W β s t u.1
  have hfm : Measurable f := hF.comp
    (((Measurable.of_eval fun v : Iic s => W.measurable v).comp measurable_fst).prodMk
      measurable_snd)
  have hXm : Measurable X := (measurable_actualParisiMagnetizationIncrement W β s t).comp measurable_fst
  have hXcap (u : Ω × A) : |X u| ≤ 2 := actualParisiMagnetizationIncrement_abs_le W β s t u.1
  have hfXcap (u : Ω × A) : |f u * X u| ≤ 2 := by
    rw [abs_mul]
    exact (mul_le_mul (hcap _) (hXcap u) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hi (k : ℕ) : Integrable (fun u => (f u*X u)^k) (W.law.prod P) :=
    Integrable.of_bound ((hfm.mul hXm).pow_const k).aestronglyMeasurable (2^k)
      (ae_of_all _ fun u => by
        rw [Real.norm_eq_abs,abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hfXcap u) k)
  have hfi : Integrable (fun u => f u^2) (W.law.prod P) :=
    Integrable.of_bound (hfm.pow_const 2).aestronglyMeasurable 1
      (ae_of_all _ fun u => by
        rw [Real.norm_eq_abs,abs_pow]
        simpa using pow_le_pow_left₀ (abs_nonneg (f u)) (hcap _) 2)
  have hbound (a : A) := N9Y1.actualIncrement_past_weighted_moments_le W β hβ s t hst
    (fun p => F (p,a)) (hF.comp (measurable_id.prodMk measurable_const)) (fun p => hcap (p,a))
  change (∫ u, (f u*X u)^2 ∂W.law.prod P) ≤ _ ∧
    (∫ u, (f u*X u)^4 ∂W.law.prod P) ≤ _
  rw [integral_prod_symm _ (hi 2),integral_prod_symm _ (hi 4),
    integral_prod_symm _ hfi,← integral_const_mul,← integral_const_mul]
  exact ⟨integral_mono_ae (hi 2).integral_prod_right
      (hfi.integral_prod_right.const_mul _) (ae_of_all _ fun a => (hbound a).1),
    integral_mono_ae (hi 4).integral_prod_right
      (hfi.integral_prod_right.const_mul _) (ae_of_all _ fun a => (hbound a).2)⟩

theorem scalarPathFromPast_brownian_ae (W : BrownianSystem Ω) (s : ℝ≥0) :
    (fun w => scalarPathFromPast s (brownianFullPast W.B s w)) =ᵐ[W.law]
      scalarPrimitiveBrownianPathVersion W s := by
  filter_upwards [scalarPrimitiveBrownianPathVersion_ae W s] with w hw
  have hs : (fun k => W.B
      ⟨scalarPathDenseTimes s k,(scalarPathDenseTimes s k).property.1⟩ w) =
      scalarPathDenseSamples s (scalarPrimitiveBrownianPathVersion W s w) := by
    funext k
    exact (hw (scalarPathDenseTimes s k)).symm
  change scalarPathFromDenseSamples s _ = _
  exact (congrArg (scalarPathFromDenseSamples s) hs).trans
    (scalarPathFromDenseSamples_leftInverse s _)

def modelDriverPast (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (s : ℝ≥0) (u : Ω × A) :
    ScalarContinuousPath s × ScalarContinuousPath s :=
  (brownianFinitePath (actualParisiQueryBrownianSystem W Z β hβ) s u,
    brownianFinitePath (actualParisiAuxBrownianSystem W Z β hβ) s u)

theorem measurable_modelDriverPast (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (s : ℝ≥0) : Measurable (modelDriverPast W Z β hβ s) :=
  (measurable_brownianFinitePath _ s).prodMk (measurable_brownianFinitePath _ s)

theorem modelDriverPast_eq_weighted_ae (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (s : ℝ≥0) :
    modelDriverPast W Z β hβ s =ᵐ[W.law.prod Z.law]
      (fun u => WeightedPair (actualParisiNegativeRhoStieltjes W β hβ)
        (actualParisiSigmaStieltjes W β hβ) (continuous_actualParisiNegativeRhoStieltjes W β hβ)
        (continuous_actualParisiSigmaStieltjes W β hβ) s
        (scalarPathFromPast s (brownianFullPast W.B s u.1),
          scalarPrimitiveBrownianPathVersion Z s u.2)) := by
  let := W.isProbability
  let := Z.isProbability
  have hp := (measurePreserving_fst (μ := W.law) (ν := Z.law)).quasiMeasurePreserving.ae
    (scalarPathFromPast_brownian_ae W s)
  filter_upwards [hp,actualParisiQueryAux_primitive_path_version W Z β hβ s,
    brownianFinitePath_version (actualParisiQueryBrownianSystem W Z β hβ) s,
    brownianFinitePath_version (actualParisiAuxBrownianSystem W Z β hβ) s] with u hu hrot hB hD
  rw [hu]
  apply Prod.ext
  · exact ContinuousMap.ext (fun t => (hB t).trans (congrArg Prod.fst (hrot t)))
  · exact ContinuousMap.ext (fun t => (hD t).trans (congrArg Prod.snd (hrot t)))

theorem actualIncrement_driverPast_weighted_moments_le
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ≥0) (hst : s ≤ t)
    (F : ScalarContinuousPath s × ScalarContinuousPath s → ℝ)
    (hF : Measurable F) (hcap : ∀ p, |F p| ≤ 1) :
    (∫ u, (F (modelDriverPast W Z β hβ s u) *
        actualParisiMagnetizationIncrement W β s t u.1)^2 ∂W.law.prod Z.law) ≤
      ((t : ℝ)-s) * (∫ u, F (modelDriverPast W Z β hβ s u)^2 ∂W.law.prod Z.law) ∧
    (∫ u, (F (modelDriverPast W Z β hβ s u) *
        actualParisiMagnetizationIncrement W β s t u.1)^4 ∂W.law.prod Z.law) ≤
      3*((t : ℝ)-s)^2 * (∫ u, F (modelDriverPast W Z β hβ s u)^2 ∂W.law.prod Z.law) := by
  let := Z.isProbability
  let T := WeightedPair (actualParisiNegativeRhoStieltjes W β hβ)
    (actualParisiSigmaStieltjes W β hβ) (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ) s
  let G : (Iic s → ℝ) × A → ℝ := fun p =>
    F (T (scalarPathFromPast s p.1,scalarPrimitiveBrownianPathVersion Z s p.2))
  have hG : Measurable G := hF.comp ((measurable_WeightedPair _ _ _ _ s).comp
    (((measurable_scalarPathFromPast s).comp measurable_fst).prodMk
      ((measurable_scalarPrimitiveBrownianPathVersion Z s).comp measurable_snd)))
  have h := actualIncrement_static_past_weighted_moments_le W Z.law β hβ s t hst G hG
    (fun p => hcap _)
  have he := modelDriverPast_eq_weighted_ae W Z β hβ s
  have he2 : (fun u => (F (modelDriverPast W Z β hβ s u) *
      actualParisiMagnetizationIncrement W β s t u.1)^2) =ᵐ[W.law.prod Z.law]
      (fun u => (G (brownianFullPast W.B s u.1,u.2) *
        actualParisiMagnetizationIncrement W β s t u.1)^2) :=
    he.mono fun u hu => congrArg (fun p =>
      (F p * actualParisiMagnetizationIncrement W β s t u.1)^2) hu
  have he4 : (fun u => (F (modelDriverPast W Z β hβ s u) *
      actualParisiMagnetizationIncrement W β s t u.1)^4) =ᵐ[W.law.prod Z.law]
      (fun u => (G (brownianFullPast W.B s u.1,u.2) *
        actualParisiMagnetizationIncrement W β s t u.1)^4) :=
    he.mono fun u hu => congrArg (fun p =>
      (F p * actualParisiMagnetizationIncrement W β s t u.1)^4) hu
  have hef : (fun u => F (modelDriverPast W Z β hβ s u)^2) =ᵐ[W.law.prod Z.law]
      (fun u => G (brownianFullPast W.B s u.1,u.2)^2) :=
    he.mono fun u hu => congrArg (fun p => F p^2) hu
  simpa only [← integral_congr_ae he2,← integral_congr_ae he4,← integral_congr_ae hef] using h

theorem normalizedIncrement_driverPast_weighted_moments_le
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (s t : ℝ≥0) (hst : s ≤ t)
    (F : ScalarContinuousPath s × ScalarContinuousPath s → ℝ)
    (hF : Measurable F) (hcap : ∀ p, |F p| ≤ 1) :
    (∫ u, (F (modelDriverPast W Z β hβ s u)*normalizedIncrement W β s t u.1)^2
        ∂W.law.prod Z.law) ≤
      (((t : ℝ)-s)*(∫ u, F (modelDriverPast W Z β hβ s u)^2 ∂W.law.prod Z.law)) /
        (actualParisiPosteriorIntervalScale W β s t : ℝ)^2 ∧
    (∫ u, (F (modelDriverPast W Z β hβ s u)*normalizedIncrement W β s t u.1)^4
        ∂W.law.prod Z.law) ≤
      (3*((t : ℝ)-s)^2*(∫ u, F (modelDriverPast W Z β hβ s u)^2 ∂W.law.prod Z.law)) /
        (actualParisiPosteriorIntervalScale W β s t : ℝ)^4 := by
  have h := actualIncrement_driverPast_weighted_moments_le W Z β hβ s t hst F hF hcap
  constructor
  · simpa only [normalizedIncrement,← mul_div_assoc,div_pow,integral_div] using
      div_le_div_of_nonneg_right h.1 (sq_nonneg (actualParisiPosteriorIntervalScale W β s t : ℝ))
  · simpa only [normalizedIncrement,← mul_div_assoc,div_pow,integral_div] using
      div_le_div_of_nonneg_right h.2
        (by positivity : 0 ≤ (actualParisiPosteriorIntervalScale W β s t : ℝ)^4)

end SKConstants.Completion.Y1
