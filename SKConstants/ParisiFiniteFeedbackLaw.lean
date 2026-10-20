module
public import SKConstants.ParisiFiniteCDFBridge
public import SKConstants.Upstream.OAI.Probability.SKSupport.Diffusion.FiniteTransition
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.CDFChainAverage
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Gaussian.GaussianCovarianceStep

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

theorem scalarStepAverage_eq_varianceTilted (m : ℝ) (h : ℝ≥0) (f g : ℝ → ℝ) :
    scalarStepAverage m (Real.sqrt h) f g = varianceTilted m h f g := by
  funext x
  unfold scalarStepAverage gaussianAverage
  rw [gaussianStepLaw_integral_inv_smul]
  unfold varianceTilted varianceHeat scaled
  simp only [smul_eq_mul]
  rw [div_eq_mul_inv, mul_comm]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => mul_comm _ _)

theorem backwardBoundary_eq_scalarStep {f : ℝ → ℝ} (hf : RegularDatum f)
    (hLip : LipschitzWith 1 f) (c : ℕ → ℝ≥0) (h : ℝ≥0)
    {N i : ℕ} (hi : i < N) :
    backwardBoundary c h f N i = scalarStep (c i) (Real.sqrt h)
      (backwardBoundary c h f N (i+1)) := by
  have hm : Measurable (backwardBoundary c h f N (i+1)) :=
    (cascade_regular hf hLip c h (N-(i+1)) (i+1)).smooth.continuous.measurable
  rw [← backwardBoundary_step hf hLip c h hi, scalarStep_eq_logSemigroup hm]
  rw [show Real.toNNReal ((Real.sqrt (h : ℝ))^2) = h by
    rw [Real.sq_sqrt h.coe_nonneg, Real.toNNReal_coe]]
  funext x
  simpa only [Real.toNNReal_coe] using
    varianceLogHeat_eq_logSemigroup_toNNReal hm (c i) (h : ℝ) x

theorem finiteFeedback_expectation_eq_scalarHierarchyAverage
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    {f g : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (hg : BoundedSmooth g) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (hi : i ≤ N) :
    (∫ w, g ((finiteFeedback hf hLip c h N 0).solution W.driver ((i : ℝ≥0)*h) w) ∂W.law) =
      scalarHierarchyAverage i (fun j => (c j : ℝ)) (fun _ => Real.sqrt h)
        (backwardBoundary c h f N i) g 0 := by
  let := W.isProbability
  induction i generalizing g with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, BoundedLipschitzDrift.solution_zero,
      scalarHierarchyAverage, integral_const, probReal_univ, one_smul]
  | succ i ih =>
    rw [finite_transition_tilted W hf hLip hg c h (by omega : i < N)]
    have hφ : RegularDatum (backwardBoundary c h f N (i+1)) :=
      cascade_regular hf hLip c h (N-(i+1)) (i+1)
    have hφLip : LipschitzWith 1 (backwardBoundary c h f N (i+1)) :=
      cascade_lipschitz hLip c h (N-(i+1)) (i+1)
    have hgt : BoundedSmooth
        (varianceTilted (c i) h (backwardBoundary c h f N (i+1)) g) :=
      (varianceTilted_family hφ hφLip hg (c i).coe_nonneg).regular h
    rw [ih hgt (by omega)]
    rw [backwardBoundary_eq_scalarStep hf hLip c h (by omega : i < N),
      ← scalarStepAverage_eq_varianceTilted]
    rfl

theorem finiteFeedback_endpoint_expectation_eq_scalarHierarchyAverage
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    {f g : ℝ → ℝ} (hf : RegularDatum f) (hLip : LipschitzWith 1 f)
    (hg : BoundedSmooth g) (c : ℕ → ℝ≥0) (h : ℝ≥0) (N : ℕ) :
    (∫ w, g ((finiteFeedback hf hLip c h N 0).solution W.driver ((N : ℝ≥0)*h) w) ∂W.law) =
      scalarHierarchyAverage N (fun j => (c j : ℝ)) (fun _ => Real.sqrt h) f g 0 := by
  have H := finiteFeedback_expectation_eq_scalarHierarchyAverage W hf hLip hg c h N N le_rfl
  simpa only [backwardBoundary, Nat.sub_self, cascade] using H

end SKConstants.ParisiFullSupport
