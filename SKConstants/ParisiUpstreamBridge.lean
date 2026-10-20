module
public import SKConstants.ParisiRegularity
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Scalar.ScalarTimeChain
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Scalar.ScalarSpinRecursion
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Scalar.ScalarCDFLimit

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

theorem parisiIntegralStep_eq_upstream_scalarStep (m v : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) :
    parisiIntegralStep (gaussianReal 0 (⟨v^2, sq_nonneg v⟩ : ℝ≥0)) m f =
      SKConstantsOAI.SK.Analytic.scalarStep m v f := by
  funext x
  have hmap : (gaussianReal 0 1).map (fun y => v * y) =
      gaussianReal 0 (⟨v^2, sq_nonneg v⟩ : ℝ≥0) := by
    convert gaussianReal_map_const_mul (μ := 0) (v := 1) v using 1; norm_num
    congr 1
  have hI : (∫ z, f (x + z) ∂gaussianReal 0 (⟨v^2, sq_nonneg v⟩ : ℝ≥0)) =
      ∫ y, f (x + v*y) ∂gaussianReal 0 1 := by
    rw [← hmap]
    exact integral_map (by fun_prop) (by fun_prop)
  have hE : (∫ z, Real.exp (m*f (x + z)) ∂gaussianReal 0 (⟨v^2, sq_nonneg v⟩ : ℝ≥0)) =
      ∫ y, Real.exp (m*f (x + v*y)) ∂gaussianReal 0 1 := by
    rw [← hmap]
    exact integral_map (by fun_prop) (by fun_prop)
  simp only [parisiIntegralStep, parisiIntegralPartition,
    SKConstantsOAI.SK.Analytic.scalarStep, SKConstantsOAI.SK.Analytic.gaussianStep,
    SKConstantsOAI.SK.Analytic.positiveGaussianLogStep]
  split_ifs <;> simp only [hI, hE]

def parisiUpstreamVariance (β : ℝ) (t : ℝ≥0) : ℝ≥0 :=
  ⟨β^2 * (t : ℝ), mul_nonneg (sq_nonneg β) t.coe_nonneg⟩

theorem parisiGaussianIterate_eq_upstream_timeChain (β : ℝ)
    (l : List (ℝ × ℝ≥0)) :
    parisiGaussianIterate (l.map (fun p => (0, parisiUpstreamVariance β p.2, p.1))) =
      SKConstantsOAI.SK.Analytic.scalarTimeChain β l SKConstantsOAI.SK.Analytic.scalarSpinTerminal := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, parisiGaussianIterate,
      SKConstantsOAI.SK.Analytic.scalarTimeChain]
    change parisiIntegralStep (gaussianReal 0 (parisiUpstreamVariance β p.2)) p.1
      (parisiGaussianIterate (l.map (fun p => (0, parisiUpstreamVariance β p.2, p.1)))) = _
    rw [ih]
    have hv : (⟨(β * Real.sqrt (p.2 : ℝ))^2, sq_nonneg _⟩ : ℝ≥0) =
        parisiUpstreamVariance β p.2 := by
      apply NNReal.coe_injective
      simp only [parisiUpstreamVariance, mul_pow,
        Real.sq_sqrt p.2.coe_nonneg]
    rw [← hv]
    exact parisiIntegralStep_eq_upstream_scalarStep p.1 _ _
      (SKConstantsOAI.SK.Analytic.scalarTimeChain_regular
        SKConstantsOAI.SK.Analytic.scalarSpinTerminal_regular β l).1.continuous

end SKConstants
