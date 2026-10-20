module
public import SKConstants.ParisiCDFCoercivity
public import SKConstants.Upstream.OAI.Probability.SKSupport.Density.FiniteDensity

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat
set_option maxHeartbeats 1000000

def finiteTanhDualWeight (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) : ℝ → ℝ :=
  gaussianLogDensity (1/(2*(i:ℝ)*(h:ℝ))) (forwardBoundary c h (softAbs 1) N i)

theorem gaussianLogDensity_antitoneOn_of_even_concave {L : ℝ → ℝ}
    (hL : RegularDatum L) (he : Function.Even L)
    (hL2 : ∀ x, iteratedDeriv 2 L x ≤ 0) {d : ℝ} (hd : 0 ≤ d) :
    AntitoneOn (gaussianLogDensity d L) (Ici (0:ℝ)) := by
  have hL0 : deriv L 0 = 0 := by
    have H := even_deriv_odd (hL.smooth.differentiable (by simp)) he 0
    simp only [neg_zero] at H
    linarith
  have hLa : Antitone (deriv L) := antitone_of_hasDerivAt_nonpos
    (fun x => by simpa only [iteratedDeriv_one] using hasDerivAt_spatialJet hL.smooth 1 x)
    (fun x => hL2 x)
  have hderiv (x : ℝ) : HasDerivAt (gaussianLogDensity d L)
      ((deriv L x-2*d*x)*gaussianLogDensity d L x) x :=
    gaussianLogDensity_derivative ((hL.smooth.differentiable (by simp)) x).hasDerivAt
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (gaussianLogDensity_continuous hL.smooth.continuous d).continuousOn
    (fun x hx => (hderiv x).hasDerivWithinAt)
  intro x hx
  apply mul_nonpos_of_nonpos_of_nonneg
  · have hx0 : 0 ≤ x := interior_subset hx
    have H := hLa hx0
    rw [hL0] at H
    nlinarith [mul_nonneg hd hx0]
  · exact (gaussianLogDensity_pos d L x).le

theorem finiteTanhDualWeight_shape (c : ℕ → ℝ≥0)
    (hc : ∀ i, 0 < (c i:ℝ)) (hmono : Monotone c) (hcap : ∀ i, (c i:ℝ) ≤ 1)
    {h : ℝ≥0} (hh : 0 < (h:ℝ)) (N i : ℕ) (hi : 0 < i) :
    (∀ x, 0 < finiteTanhDualWeight c h N i x) ∧
      Function.Even (finiteTanhDualWeight c h N i) ∧
      Continuous (finiteTanhDualWeight c h N i) ∧
      Integrable (finiteTanhDualWeight c h N i) ∧
      AntitoneOn (finiteTanhDualWeight c h N i) (Ici (0:ℝ)) := by
  let L := forwardBoundary c h (softAbs 1) N i
  have hL := forwardBoundary_regular (regularDatum_softAbs (by norm_num : (1:ℝ) ≠ 0))
    (softAbs_lipschitz (by norm_num : (1:ℝ) ≠ 0)) c hh N i
  have hshape := forwardBoundary_shape c hc hmono hcap hh N i
  have hd : 0 < 1/(2*(i:ℝ)*(h:ℝ)) := by positivity
  obtain ⟨K,hK⟩ := hL.exists_lipschitz
  refine ⟨gaussianLogDensity_pos _ _,gaussianLogDensity_even hshape.even _,
    gaussianLogDensity_continuous hL.smooth.continuous _,?_,
    gaussianLogDensity_antitoneOn_of_even_concave hL hshape.even hshape.second hd.le⟩
  change Integrable (gaussianLogDensity (1/(2*(i:ℝ)*(h:ℝ))) L)
  simpa only [mul_one] using gaussianLogDensity_integrable_mul hK
    (measurable_const : Measurable (fun _ : ℝ => (1:ℝ))) (ExponentialBound.const 1) hd

end SKConstants.ParisiFullSupport
