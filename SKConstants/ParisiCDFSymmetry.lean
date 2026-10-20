module
public import SKConstants.ParisiPhysicalNormalization
public import SKConstants.ParisiCDFDiffusion
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Scalar.ScalarSymmetry

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants
open SKConstantsOAI.SK.Analytic

theorem parisiCDFValue_even (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) : Function.Even (parisiCDFValue β α s t) := by
  intro x
  have hneg := (parisiDyadic_uniform_convergence β α ha hm s t ht).tendsto_at (-x)
  have hpos := (parisiDyadic_uniform_convergence β α ha hm s t ht).tendsto_at x
  have he (n : ℕ) :
      parisiGaussianIterate (parisiDyadicSteps β α n s t) (-x) =
        parisiGaussianIterate (parisiDyadicSteps β α n s t) x := by
    simp only [parisiDyadicSteps, parisiGaussianIterate_eq_upstream_timeChain,
      scalarTimeChain_eq_hierarchy]
    exact scalarHierarchy_spin_even _ _ _ x
  simp only [he] at hneg
  exact tendsto_nhds_unique hneg hpos

theorem parisiCDFGradient_odd (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    Function.Odd (scalarCDFGradient β α s t) := by
  intro x
  have h := (parisiCDFValue_spatial_derivatives β α ha hm s t ht).1 (-x)
  have hc := h.comp x (hasDerivAt_neg x)
  change HasDerivAt (fun y => parisiCDFValue β α s t (-y))
    (scalarCDFGradient β α s t (-x) * (-1)) x at hc
  have he : (fun y => parisiCDFValue β α s t (-y)) = parisiCDFValue β α s t :=
    funext (parisiCDFValue_even β ha hm s t ht)
  rw [he] at hc
  have H := hc.unique ((parisiCDFValue_spatial_derivatives β α ha hm s t ht).1 x)
  linarith

theorem parisiCDFHessian_even (β : ℝ) {α : ℝ → ℝ}
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    Function.Even (scalarCDFHessian β α s t) := by
  intro x
  have h := (parisiCDFValue_spatial_derivatives β α ha hm s t ht).2.1 (-x)
  have hc := h.comp x (hasDerivAt_neg x)
  change HasDerivAt (fun y => scalarCDFGradient β α s t (-y))
    (scalarCDFHessian β α s t (-x) * (-1)) x at hc
  have he : (fun y => scalarCDFGradient β α s t (-y)) =
      fun y => -scalarCDFGradient β α s t y :=
    funext (parisiCDFGradient_odd β ha hm s t ht)
  rw [he] at hc
  have H := hc.unique (((parisiCDFValue_spatial_derivatives β α ha hm s t ht).2.1 x).neg)
  linarith

theorem finiteTemperatureCDFDrift_odd (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) (v : ℝ) :
    Function.Odd ((ParisiFullSupport.finiteTemperatureCDFDrift β α ha h1).f v) := by
  intro x
  have ht : Real.toNNReal (1-ParisiFullSupport.cdfTimeClamp (v/β^2)) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith [(ParisiFullSupport.cdfTimeClamp_mem (v/β^2)).1]
  change α (ParisiFullSupport.cdfTimeClamp (v/β^2)) *
      scalarCDFGradient β α (ParisiFullSupport.cdfTimeClamp (v/β^2))
        (Real.toNNReal (1-ParisiFullSupport.cdfTimeClamp (v/β^2))) (-x) = _
  rw [parisiCDFGradient_odd β ha α.mono _ _ ht]
  exact mul_neg _ _

end SKConstants
