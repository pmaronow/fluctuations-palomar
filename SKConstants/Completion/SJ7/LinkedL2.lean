module

public import SKConstants.Completion.Blueprint4.NodesSharp
public import SKConstants.ScalarProcessRowMGFLimit

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.SJ7
open SKConstantsOAI.ZeroTemperatureSK SKConstants.Blueprint4

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem actualQuerySpinLaw_le_two (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (V : ℝ≥0) :
    actualParisiFullQuerySpinLaw W Z β V ≤ (2 : ℝ≥0∞) • LM4.actualRowBaseLaw W Z := by
  rw [← LM4.actual_linkedRowLaw_eq]
  exact LM4.linkedRowLaw_le_two (ae_of_all _ (fun u => (LM4.actualRowLink_bounds β W V u).2))

theorem integrable_actualQuerySpinLaw (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (V : ℝ≥0) {f : (Bool × Ω) × A → ℝ}
    (hf : Integrable f (LM4.actualRowBaseLaw W Z)) :
    Integrable f (actualParisiFullQuerySpinLaw W Z β V) :=
  (hf.smul_measure (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mono_measure
    (actualQuerySpinLaw_le_two W Z β V)

theorem integral_nonneg_actualQuerySpinLaw_le_two
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (V : ℝ≥0)
    {f : (Bool × Ω) × A → ℝ} (hf : Integrable f (LM4.actualRowBaseLaw W Z))
    (hf0 : ∀ u, 0 ≤ f u) :
    (∫ u, f u ∂actualParisiFullQuerySpinLaw W Z β V) ≤
      2 * ∫ u, f u ∂LM4.actualRowBaseLaw W Z := by
  have h := integral_mono_measure (actualQuerySpinLaw_le_two W Z β V)
    (ae_of_all _ hf0) (hf.smul_measure (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  simpa only [integral_smul_measure, ENNReal.toReal_ofNat, smul_eq_mul] using h

theorem jointRowIntegral_memLp_linked (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (Zv : (Bool × Ω) × A → ℝ)
    (hZv : IsJointRowIntegral W Z β hβ V Zv) :
    MemLp Zv 2 (actualParisiFullQuerySpinLaw W Z β V) :=
  (hZv.2.1.smul_measure (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mono_measure
    (actualQuerySpinLaw_le_two W Z β V)

theorem jointRowIntegral_integrable (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (Zv : (Bool × Ω) × A → ℝ)
    (hZv : IsJointRowIntegral W Z β hβ V Zv) :
    Integrable Zv (actualParisiFullQuerySpinLaw W Z β V) :=
  integrable_actualQuerySpinLaw W Z β V (hZv.2.1.integrable (by norm_num))

theorem jointRowIntegral_tendsto_L2_linked (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (Zv : (Bool × Ω) × A → ℝ)
    (hZv : IsJointRowIntegral W Z β hβ V Zv) :
    (∀ l, Integrable (fun u => (jointRowLeftSum W Z β hβ V l u - Zv u) ^ 2)
      (actualParisiFullQuerySpinLaw W Z β V)) ∧
    Tendsto (fun l => ∫ u, (jointRowLeftSum W Z β hβ V l u - Zv u) ^ 2
      ∂actualParisiFullQuerySpinLaw W Z β V) atTop (𝓝 0) := by
  refine ⟨fun l => integrable_actualQuerySpinLaw W Z β V (hZv.2.2.1 l), ?_⟩
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun l => integral_nonneg_actualQuerySpinLaw_le_two W Z β V (hZv.2.2.1 l)
      (fun _ => sq_nonneg _))
  simpa using hZv.2.2.2.const_mul 2

theorem jointRowIntegral_unique (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (Y Zv : (Bool × Ω) × A → ℝ)
    (hY : IsJointRowIntegral W Z β hβ V Y) (hZv : IsJointRowIntegral W Z β hβ V Zv) :
    Y =ᵐ[LM4.actualRowBaseLaw W Z] Zv :=
  tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_integral_sq hY.2.2.1 hY.2.2.2)
    (tendstoInMeasure_of_tendsto_integral_sq hZv.2.2.1 hZv.2.2.2)

theorem jointRowIntegral_unique_linked (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (Y Zv : (Bool × Ω) × A → ℝ)
    (hY : IsJointRowIntegral W Z β hβ V Y) (hZv : IsJointRowIntegral W Z β hβ V Zv) :
    Y =ᵐ[actualParisiFullQuerySpinLaw W Z β V] Zv := by
  rw [← LM4.actual_linkedRowLaw_eq]
  exact (LM4.linkedRowLaw_absolutelyContinuous _).ae_le
    (jointRowIntegral_unique W Z β hβ V Y Zv hY hZv)

theorem integral_tendsto_of_L2 {B : Type*} [MeasurableSpace B]
    (μ : Measure B) [IsProbabilityMeasure μ] (X : ℕ → B → ℝ) (Y : B → ℝ)
    (hXm : ∀ l, Measurable (X l)) (hYm : Measurable Y) (hY : MemLp Y 2 μ)
    (hi : ∀ l, Integrable (fun u => (X l u - Y u) ^ 2) μ)
    (hlim : Tendsto (fun l => ∫ u, (X l u - Y u) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun l => ∫ u, X l u ∂μ) atTop (𝓝 (∫ u, Y u ∂μ)) := by
  have hd (l : ℕ) : MemLp (fun u => X l u - Y u) 2 μ :=
    (memLp_two_iff_integrable_sq ((hXm l).sub hYm).aestronglyMeasurable).mpr (hi l)
  have hYi := hY.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hXi (l : ℕ) : Integrable (X l) μ := by
    refine (((hd l).integrable (by norm_num)).add hYi).congr (ae_of_all _ (fun u => ?_))
    change (X l u - Y u) + Y u = X l u
    ring
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun l => ?_)
    (show Tendsto (fun l => Real.sqrt (∫ u, (X l u - Y u) ^ 2 ∂μ)) atTop (𝓝 0) by
      simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hlim)
  have h := SKConstantsOAI.SK.Analytic.abs_integral_mul_le_sqrt_of_bound
    (fun u => X l u - Y u) (fun _ => (1 : ℝ)) (hd l)
    measurable_const.aestronglyMeasurable (ae_of_all _ (fun _ => by norm_num))
  simpa only [mul_one, integral_sub (hXi l) hYi, Real.norm_eq_abs] using h

end SKConstants.Completion.SJ7
