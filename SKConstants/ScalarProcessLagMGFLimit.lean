module
public import SKConstants.ConcentrationMGF
public import SKConstants.ScalarProcessRowMGFLimit

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace SKConstants

lemma localQuadraticMGF_of_tendsto_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} {v radius : ℝ}
    (hX : ∀ n, Concentration.LocalQuadraticMGF (X n) μ v radius)
    (hXm : ∀ n, AEStronglyMeasurable (X n) μ)
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Concentration.LocalQuadraticMGF Y μ v radius := by
  have hYm : AEStronglyMeasurable Y μ := aestronglyMeasurable_of_tendsto_ae atTop hXm hae
  have hbound (θ : ℝ) (hθ : |θ| ≤ radius) :
      (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Y ω)) ∂μ) ≤
        ENNReal.ofReal (Real.exp (v * θ^2)) := by
    have hlimexp : ∀ᵐ ω ∂μ, Tendsto
        (fun n => ENNReal.ofReal (Real.exp (θ * X n ω))) atTop
        (𝓝 (ENNReal.ofReal (Real.exp (θ * Y ω)))) := by
      filter_upwards [hae] with ω hω
      exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((Real.continuous_exp.tendsto _).comp
          ((tendsto_const_nhds : Tendsto (fun _ : ℕ => θ) atTop (𝓝 θ)).mul hω))
    calc
      _ = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (Real.exp (θ * X n ω))) atTop ∂μ :=
        lintegral_congr_ae (hlimexp.mono (fun ω hω => hω.liminf_eq.symm))
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X n ω)) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => ((hX n).integrable_exp_mul θ hθ).aemeasurable.ennreal_ofReal)
      _ ≤ liminf (fun _ : ℕ => ENNReal.ofReal (Real.exp (v * θ^2))) atTop := by
        apply Filter.liminf_le_liminf (Filter.Eventually.of_forall (fun n => ?_))
        rw [← ofReal_integral_eq_lintegral_ofReal ((hX n).integrable_exp_mul θ hθ)
          (ae_of_all _ (fun ω => (Real.exp_pos _).le))]
        exact ENNReal.ofReal_le_ofReal ((hX n).mgf_le θ hθ)
      _ = _ := tendsto_const_nhds.liminf_eq
  have hInt (θ : ℝ) (hθ : |θ| ≤ radius) : Integrable (fun ω => Real.exp (θ * Y ω)) μ := by
    refine ⟨(hYm.aemeasurable.const_mul θ).exp.aestronglyMeasurable, ?_⟩
    have he : (fun ω => ‖Real.exp (θ * Y ω)‖ₑ) =
        (fun ω => ENNReal.ofReal (Real.exp (θ * Y ω))) := by
      funext ω
      exact Real.enorm_eq_ofReal (Real.exp_pos _).le
    rw [hasFiniteIntegral_iff_enorm, he]
    exact (hbound θ hθ).trans_lt ENNReal.ofReal_lt_top
  refine ⟨hInt, fun θ hθ => ?_⟩
  have h := hbound θ hθ
  rw [← ofReal_integral_eq_lintegral_ofReal (hInt θ hθ)
    (ae_of_all _ (fun ω => (Real.exp_pos _).le))] at h
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).mp h

lemma localQuadraticMGF_of_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : ℕ → Ω → ℝ} {Y : Ω → ℝ} {v radius : ℝ}
    (hX : ∀ n, Concentration.LocalQuadraticMGF (X n) μ v radius)
    (hXm : ∀ n, AEStronglyMeasurable (X n) μ)
    (hlim : TendstoInMeasure μ X atTop Y) :
    Concentration.LocalQuadraticMGF Y μ v radius := by
  obtain ⟨ns, _, hae⟩ := hlim.exists_seq_tendsto_ae
  exact localQuadraticMGF_of_tendsto_ae (fun n => hX (ns n)) (fun n => hXm (ns n)) hae

lemma Concentration.LocalQuadraticMGF.comp_hasLaw {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
    {X : Ξ → ℝ} {f : Ω → Ξ} {v radius : ℝ}
    (h : Concentration.LocalQuadraticMGF X ν v radius)
    (hf : HasLaw f ν μ) : Concentration.LocalQuadraticMGF (X ∘ f) μ v radius := by
  refine ⟨fun θ hθ => hf.integrable_comp (h.integrable_exp_mul θ hθ), fun θ hθ => ?_⟩
  change (∫ ω, ((fun y => Real.exp (θ * X y)) ∘ f) ω ∂μ) ≤ Real.exp (v * θ^2)
  rw [hf.integral_comp ((h.integrable_exp_mul θ hθ).aestronglyMeasurable)]
  exact h.mgf_le θ hθ

lemma Concentration.LocalQuadraticMGF.congr_ae {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X Y : Ω → ℝ} {v radius : ℝ}
    (h : Concentration.LocalQuadraticMGF X μ v radius) (he : Y =ᵐ[μ] X) :
    Concentration.LocalQuadraticMGF Y μ v radius := by
  have heExp (θ:ℝ) : (fun ω => Real.exp (θ*Y ω)) =ᵐ[μ] (fun ω => Real.exp (θ*X ω)) :=
    he.mono (fun _ hω => congrArg (fun x:ℝ => Real.exp (θ*x)) hω)
  constructor
  · intro θ hθ
    exact (h.integrable_exp_mul θ hθ).congr (heExp θ).symm
  · intro θ hθ
    exact (integral_congr_ae (heExp θ)).trans_le (h.mgf_le θ hθ)

end SKConstants
