module
public import SKConstants.BrownianContinuousReference
public import SKConstants.ScalarProcessVarianceBalance

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

lemma tendsto_toLp_of_meanSquare {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {S : ℕ → Ω → ℝ} {X : Ω → ℝ}
    (hS : ∀ n, MemLp (S n) 2 P) (hX : MemLp X 2 P)
    (hlim : Tendsto (fun n => ∫ ω, (S n ω-X ω)^2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => (hS n).toLp (S n)) atTop (𝓝 (hX.toLp X)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have he (n : ℕ) : ‖(hS n).toLp (S n)-hX.toLp X‖ =
      Real.sqrt (∫ ω, (S n ω-X ω)^2 ∂P) := by
    rw [← norm_toLp_difference_sq_eq_integral (hS n) hX,Real.sqrt_sq (norm_nonneg _)]
  simp_rw [he]
  simpa only [Real.sqrt_zero] using hlim.sqrt

theorem meanSquareLimit_eq_ae_of_cross_moments {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {S : ℕ → Ω → ℝ} {X I : Ω → ℝ}
    (hS : ∀ n, MemLp (S n) 2 P) (hX : MemLp X 2 P) (hI : MemLp I 2 P)
    (hIlim : Tendsto (fun n => ∫ ω, (S n ω-I ω)^2 ∂P) atTop (𝓝 0))
    (hsecond : Tendsto (fun n => ∫ ω, S n ω^2 ∂P) atTop (𝓝 (∫ ω, X ω^2 ∂P)))
    (hcross : Tendsto (fun n => ∫ ω, X ω*S n ω ∂P) atTop (𝓝 (∫ ω, X ω^2 ∂P))) :
    X =ᵐ[P] I := by
  have he (n : ℕ) : (∫ ω, (S n ω-X ω)^2 ∂P) =
      (∫ ω, S n ω^2 ∂P)-2*(∫ ω, X ω*S n ω ∂P)+(∫ ω, X ω^2 ∂P) := by
    have hi : Integrable (fun ω => X ω*S n ω) P := hX.integrable_mul (hS n)
    have hf : (fun ω => (S n ω-X ω)^2) =
        (fun ω => S n ω^2-2*(X ω*S n ω)+X ω^2) := by
      funext ω
      ring
    rw [hf,integral_add (f := fun ω => S n ω^2-2*(X ω*S n ω))
      (g := fun ω => X ω^2) ((hS n).integrable_sq.sub (hi.const_mul 2)) hX.integrable_sq,
      integral_sub (f := fun ω => S n ω^2) (g := fun ω => 2*(X ω*S n ω))
        (hS n).integrable_sq (hi.const_mul 2),integral_const_mul]
  have hXlim : Tendsto (fun n => ∫ ω, (S n ω-X ω)^2 ∂P) atTop (𝓝 0) := by
    simp_rw [he]
    convert (hsecond.sub (hcross.const_mul 2)).add_const (∫ ω, X ω^2 ∂P) using 1 <;> ring
  have hlp := tendsto_nhds_unique (tendsto_toLp_of_meanSquare hS hX hXlim)
    (tendsto_toLp_of_meanSquare hS hI hIlim)
  exact (hX.toLp_eq_toLp_iff hI).mp hlp

end SKConstants
