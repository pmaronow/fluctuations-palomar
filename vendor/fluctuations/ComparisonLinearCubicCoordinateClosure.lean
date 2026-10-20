module

public import ComparisonOriginalMassCauchy

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 5000000

variable {Ω : Type*} [MeasurableSpace Ω]

theorem linear_cubic_modulus_normalized_integral_le
    (μ : Measure Ω) [IsFiniteMeasure μ] (D E : Ω→ℝ)
    (hD : Integrable D μ) (hE : Integrable E μ)
    {x C L site eta : ℝ} (hx : 0 < x) (hC : 0 ≤ C) (_hL : 0 ≤ L)
    (hs : 0 ≤ site) (he : 0 ≤ eta)
    (hmass : μ.real univ ≤ L*x)
    (hpoint : ∀ᵐ r∂μ, |E r| ≤ C*x^2*(|D r|+site)+eta*x^3) :
    (∫r,|E r|∂μ)/x^4 ≤ C*((∫r,|D r|∂μ)/x^2)+C*L*(site/x)+L*eta := by
  have H := integral_mono_ae hE.abs
    (((hD.abs.add (integrable_const site)).const_mul (C*x^2)).add
      (integrable_const (eta*x^3))) hpoint
  change (∫r,|E r|∂μ) ≤ ∫r,C*x^2*(|D r|+site)+eta*x^3∂μ at H
  have hA : Integrable (fun r=>C*x^2*(|D r|+site)) μ :=
    (hD.abs.add (integrable_const site)).const_mul (C*x^2)
  have he1:=integral_add hA (integrable_const (eta*x^3))
  have he2:=integral_add hD.abs (integrable_const site)
  rw [he1,integral_const_mul,he2,integral_const,integral_const] at H
  simp only [smul_eq_mul] at H
  have Hs:=mul_le_mul_of_nonneg_right hmass hs
  have He:=mul_le_mul_of_nonneg_right hmass (mul_nonneg he (pow_nonneg hx.le 3))
  have Hc:=mul_le_mul_of_nonneg_left Hs (mul_nonneg hC (sq_nonneg x))
  apply (div_le_iff₀ (pow_pos hx 4)).mpr
  have hid : (C*((∫r,|D r|∂μ)/x^2)+C*L*(site/x)+L*eta)*x^4 =
      C*x^2*((∫r,|D r|∂μ)+(L*x)*site)+(L*x)*(eta*x^3) := by
    field_simp
  rw [hid]
  nlinarith only [H,Hc,He]

theorem linear_cubic_modulus_normalized_L1_tendsto
    (μ : ℕ→Measure Ω) [∀n,IsFiniteMeasure (μ n)] (D E : ℕ→Ω→ℝ)
    (x site eta : ℕ→ℝ) {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hx : ∀n,0 < x n) (hs : ∀n,0 ≤ site n) (he : ∀n,0 ≤ eta n)
    (hD : ∀n,Integrable (D n) (μ n))
    (hD2 : ∀n,Integrable (fun r=>(D n r)^2) (μ n))
    (hE : ∀n,Integrable (E n) (μ n))
    (hmass : ∀n,(μ n).real univ ≤ L*x n)
    (hpoint : ∀ᶠn in atTop,∀ᵐ r∂μ n,
      |E n r| ≤ C*(x n)^2*(|D n r|+site n)+eta n*(x n)^3)
    (hthermal : Tendsto (fun n=>(∫r,(D n r)^2∂μ n)/(x n)^3) atTop (𝓝 0))
    (hsite : Tendsto (fun n=>site n/x n) atTop (𝓝 0))
    (heta : Tendsto eta atTop (𝓝 0)) :
    Tendsto (fun n=>(∫r,|E n r|∂μ n)/(x n)^4) atTop (𝓝 0) := by
  have HD : Tendsto (fun n=>(∫r,|D n r|∂μ n)/(x n)^2) atTop (𝓝 0) := by
    have H:=comparison_original_mass_normalized_L1_tendsto μ (fun _=>inferInstance)
      D x hx hL hD hD2 hmass hthermal
    simpa only [comparison_original_mass_normalized_error_exact _ _ (hx _)] using H
  have HB := ((HD.const_mul C).add (hsite.const_mul (C*L))).add (heta.const_mul L)
  simp only [mul_zero,add_zero] at HB
  apply squeeze_zero' _ _ HB
  · exact Eventually.of_forall (fun n=>div_nonneg
      (integral_nonneg (fun r=>abs_nonneg _)) (pow_nonneg (hx n).le 4))
  · filter_upwards [hpoint] with n hn
    exact linear_cubic_modulus_normalized_integral_le (μ n) (D n) (E n)
      (hD n) (hE n) (hx n) hC hL (hs n) (he n) (hmass n) hn

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem coordinate_sqrt_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω→ℝ)
    (hf : Integrable f μ) (hf0 : ∀ᵐr∂μ,0 ≤ f r) :
    Integrable (fun r=>Real.sqrt (f r)) μ ∧
      Integrable (fun r=>(Real.sqrt (f r))^2) μ := by
  have hs2 : Integrable (fun r=>(Real.sqrt (f r))^2) μ :=
    hf.congr (hf0.mono fun r hr=>(Real.sq_sqrt hr).symm)
  have hs : MemLp (fun r=>Real.sqrt (f r)) 2 μ :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hf.aestronglyMeasurable)).2 hs2
  exact ⟨hs.integrable (by norm_num),hs2⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
