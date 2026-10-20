module
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Chebyshev

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

lemma tendstoInMeasure_of_tendsto_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hInt : ∀ n, Integrable (fun ω => (X n ω - Y ω)^2) μ)
    (hlim : Tendsto (fun n => ∫ ω, (X n ω - Y ω)^2 ∂μ) atTop (𝓝 0)) :
    TendstoInMeasure μ X atTop Y := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  apply squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_)
    (by simpa using hlim.div_const (ε ^ 2))
  have h := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (f := fun ω => (X n ω - Y ω)^2)
    (ae_of_all _ (fun ω => sq_nonneg _)) (hInt n) (ε^2)
  have he : {ω | ε^2 ≤ (X n ω - Y ω)^2} = {ω | ε ≤ ‖X n ω - Y ω‖} := by
    ext ω
    change ε ^ 2 ≤ (X n ω - Y ω)^2 ↔ ε ≤ ‖X n ω - Y ω‖
    rw [Real.norm_eq_abs]
    exact ⟨fun h => by nlinarith [abs_nonneg (X n ω - Y ω), sq_abs (X n ω - Y ω)], fun h => by nlinarith [abs_nonneg (X n ω - Y ω), sq_abs (X n ω - Y ω)]⟩
  rw [he] at h
  exact (le_div_iff₀ (sq_pos_of_pos hε)).mpr (by simpa [mul_comm] using h)

lemma hasSubgaussianMGF_of_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} {V : ℕ → ℝ≥0} {W : ℝ≥0}
    (hX : ∀ n, HasSubgaussianMGF (X n) (V n) μ)
    (hlim : TendstoInMeasure μ X atTop Y)
    (hV : Tendsto V atTop (𝓝 W)) : HasSubgaussianMGF Y W μ := by
  obtain ⟨ns, hns, hae⟩ := hlim.exists_seq_tendsto_ae
  have hYm := hlim.aestronglyMeasurable (fun n => (hX n).aestronglyMeasurable)
  have hbound (θ : ℝ) :
      (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Y ω)) ∂μ) ≤
        ENNReal.ofReal (Real.exp ((W : ℝ) * θ^2 / 2)) := by
    have hlimexp : ∀ᵐ ω ∂μ, Tendsto
        (fun n => ENNReal.ofReal (Real.exp (θ * X (ns n) ω))) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (θ * Y ω)))) := by
      filter_upwards [hae] with ω hω
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((Real.continuous_exp.tendsto _).comp
          ((tendsto_const_nhds : Tendsto (fun _ : ℕ => θ) atTop (𝓝 θ)).mul hω))
    calc
      _ = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (Real.exp (θ * X (ns n) ω))) atTop ∂μ :=
        lintegral_congr_ae (hlimexp.mono (fun ω hω => hω.liminf_eq.symm))
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X (ns n) ω)) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => ((hX (ns n)).integrable_exp_mul θ).aemeasurable.ennreal_ofReal)
      _ ≤ liminf (fun n => ENNReal.ofReal (Real.exp ((V (ns n) : ℝ) * θ^2 / 2))) atTop := by
        apply Filter.liminf_le_liminf (Filter.Eventually.of_forall (fun n => ?_))
        rw [← ofReal_integral_eq_lintegral_ofReal ((hX (ns n)).integrable_exp_mul θ)
          (ae_of_all _ (fun ω => (Real.exp_pos _).le))]
        exact ENNReal.ofReal_le_ofReal ((hX (ns n)).mgf_le θ)
      _ = _ := by
        apply Filter.Tendsto.liminf_eq
        exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          ((Real.continuous_exp.tendsto _).comp
            (((NNReal.continuous_coe.tendsto W).comp (hV.comp hns.tendsto_atTop)).mul_const
              (θ^2) |>.div_const 2))
  have hInt (θ : ℝ) : Integrable (fun ω => Real.exp (θ * Y ω)) μ := by
    refine ⟨(hYm.aemeasurable.const_mul θ).exp.aestronglyMeasurable, ?_⟩
    have he : (fun ω => ‖Real.exp (θ * Y ω)‖ₑ) =
        (fun ω => ENNReal.ofReal (Real.exp (θ * Y ω))) := by
      funext ω
      exact Real.enorm_eq_ofReal (Real.exp_pos _).le
    rw [hasFiniteIntegral_iff_enorm, he]
    exact (hbound θ).trans_lt ENNReal.ofReal_lt_top
  refine ⟨hInt, fun θ => ?_⟩
  have h := hbound θ
  rw [← ofReal_integral_eq_lintegral_ofReal (hInt θ)
    (ae_of_all _ (fun ω => (Real.exp_pos _).le))] at h
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp h

lemma hasSubgaussianMGF_of_tendsto_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    {V : ℕ → ℝ≥0} {W : ℝ≥0}
    (hX : ∀ n, HasSubgaussianMGF (X n) (V n) μ)
    (hInt : ∀ n, Integrable (fun ω => (X n ω - Y ω)^2) μ)
    (hlim : Tendsto (fun n => ∫ ω, (X n ω - Y ω)^2 ∂μ) atTop (𝓝 0))
    (hV : Tendsto V atTop (𝓝 W)) : HasSubgaussianMGF Y W μ :=
  hasSubgaussianMGF_of_tendstoInMeasure hX (tendstoInMeasure_of_tendsto_integral_sq hInt hlim) hV

lemma integrable_sq_sub {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : Ω → ℝ} (hXm : AEMeasurable X μ) (hYm : AEMeasurable Y μ)
    (hX : Integrable (fun ω => (X ω)^2) μ) (hY : Integrable (fun ω => (Y ω)^2) μ) :
    Integrable (fun ω => (X ω - Y ω)^2) μ := by
  apply ((hX.const_mul 2).add (hY.const_mul 2)).mono'
  · exact ((hXm.sub hYm).pow_const 2).aestronglyMeasurable
  · apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (X ω - Y ω)^2 ≤ 2*(X ω)^2 + 2*(Y ω)^2
    nlinarith [sq_nonneg (X ω + Y ω)]

lemma tendsto_integral_sq_sub {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y : ℕ → Ω → ℝ}
    (hXm : ∀ n, AEMeasurable (X n) μ) (hYm : ∀ n, AEMeasurable (Y n) μ)
    (hX : ∀ n, Integrable (fun ω => (X n ω)^2) μ)
    (hY : ∀ n, Integrable (fun ω => (Y n ω)^2) μ)
    (hXlim : Tendsto (fun n => ∫ ω, (X n ω)^2 ∂μ) atTop (𝓝 0))
    (hYlim : Tendsto (fun n => ∫ ω, (Y n ω)^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (X n ω - Y n ω)^2 ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => integral_nonneg (fun ω => sq_nonneg _)) (fun n => ?_)
    (by simpa using (hXlim.const_mul 2).add (hYlim.const_mul 2))
  have h := integral_mono (integrable_sq_sub (hXm n) (hYm n) (hX n) (hY n))
    (((hX n).const_mul 2).add ((hY n).const_mul 2))
    (fun ω => by
      change (X n ω - Y n ω)^2 ≤ 2*(X n ω)^2 + 2*(Y n ω)^2
      nlinarith [sq_nonneg (X n ω + Y n ω)])
  simp only [Pi.add_apply] at h
  simpa only [integral_add ((hX n).const_mul 2) ((hY n).const_mul 2), integral_const_mul] using h

lemma integrable_sq_finset_sum {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) {X : ι → Ω → ℝ} (hXm : ∀ i ∈ s, AEMeasurable (X i) μ)
    (hX : ∀ i ∈ s, Integrable (fun ω => (X i ω)^2) μ) :
    Integrable (fun ω => (∑ i ∈ s, X i ω)^2) μ := by
  apply ((integrable_finsetSum s hX).const_mul (s.card : ℝ)).mono'
  · exact ((Finset.aemeasurable_fun_sum s hXm).pow_const 2).aestronglyMeasurable
  · apply ae_of_all
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_sum_le_card_mul_sum_sq

lemma tendsto_integral_sq_finset_sum {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) {X : ι → ℕ → Ω → ℝ}
    (hXm : ∀ i ∈ s, ∀ n, AEMeasurable (X i n) μ)
    (hX : ∀ i ∈ s, ∀ n, Integrable (fun ω => (X i n ω)^2) μ)
    (hlim : ∀ i ∈ s, Tendsto (fun n => ∫ ω, (X i n ω)^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (∑ i ∈ s, X i n ω)^2 ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => integral_nonneg (fun ω => sq_nonneg _)) (fun n => ?_)
    (by simpa using (tendsto_finsetSum s hlim).const_mul (s.card : ℝ))
  have h := integral_mono
    (integrable_sq_finset_sum s (fun i hi => hXm i hi n) (fun i hi => hX i hi n))
    ((integrable_finsetSum s (fun i hi => hX i hi n)).const_mul (s.card : ℝ))
    (fun ω => sq_sum_le_card_mul_sum_sq)
  simpa only [integral_const_mul, integral_finsetSum s (fun i hi => hX i hi n)] using h

end SKConstants
