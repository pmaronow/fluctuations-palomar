module

public import SKConstants.ScalarProcessContinuous
public import SKConstants.ScalarProcessCharacteristic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace SKConstants

theorem map_eq_of_linear_characteristic {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X Y : ι → Ω → ℝ) (hX : ∀ i, AEMeasurable (X i) μ)
    (hY : ∀ i, AEMeasurable (Y i) μ)
    (hchar : ∀ θ : ι → ℝ,
      (∫ ω, Complex.exp (((∑ i, θ i * X i ω : ℝ) : ℂ) * Complex.I) ∂μ) =
      ∫ ω, Complex.exp (((∑ i, θ i * Y i ω : ℝ) : ℂ) * Complex.I) ∂μ) :
    μ.map (fun ω i => X i ω) = μ.map (fun ω i => Y i ω) := by
  let e := MeasurableEquiv.toLp 2 (ι → ℝ)
  have hmX : AEMeasurable (fun ω i => X i ω) μ := AEMeasurable.of_eval hX
  have hmY : AEMeasurable (fun ω i => Y i ω) μ := AEMeasurable.of_eval hY
  apply e.map_measurableEquiv_injective
  rw [AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hmX,
    AEMeasurable.map_map_of_aemeasurable e.measurable.aemeasurable hmY]
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply, charFun_apply,
    integral_map (e.measurable.comp_aemeasurable hmX) (by fun_prop),
    integral_map (e.measurable.comp_aemeasurable hmY) (by fun_prop)]
  have hx (ω : Ω) : inner ℝ (e (fun i => X i ω)) t = ∑ i, t i * X i ω := by
    simp [e, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hy (ω : Ω) : inner ℝ (e (fun i => Y i ω)) t = ∑ i, t i * Y i ω := by
    simp [e, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  simp only [Function.comp_def]
  simp_rw [hx, hy]
  exact hchar (fun i => t i)

theorem integral_characteristic_eq_of_mesh_comparison {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (F G : ℕ → Ω → ℝ) (f g : Ω → ℝ)
    (hF : ∀ n, AEMeasurable (F n) μ) (hG : ∀ n, AEMeasurable (G n) μ)
    (hflim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (f ω)))
    (hglim : ∀ᵐ ω ∂μ, Tendsto (fun n => G n ω) atTop (𝓝 (g ω)))
    (error : ℕ → ℝ) (herr : Tendsto error atTop (𝓝 0))
    (hbound : ∀ n,
      ‖(∫ ω, Complex.exp ((F n ω : ℂ) * Complex.I) ∂μ) -
        ∫ ω, Complex.exp ((G n ω : ℂ) * Complex.I) ∂μ‖ ≤ error n) :
    (∫ ω, Complex.exp ((f ω : ℂ) * Complex.I) ∂μ) =
      ∫ ω, Complex.exp ((g ω : ℂ) * Complex.I) ∂μ := by
  have hp := (integral_exp_imag_tendsto_of_ae_tendsto μ F f hF hflim).sub
    (integral_exp_imag_tendsto_of_ae_tendsto μ G g hG hglim)
  have hzero : Tendsto (fun n =>
      (∫ ω, Complex.exp ((F n ω : ℂ) * Complex.I) ∂μ) -
        ∫ ω, Complex.exp ((G n ω : ℂ) * Complex.I) ∂μ) atTop (𝓝 0) :=
    squeeze_zero_norm hbound herr
  exact sub_eq_zero.mp (tendsto_nhds_unique hp hzero)

end SKConstants
