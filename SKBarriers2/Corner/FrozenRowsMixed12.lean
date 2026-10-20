module

public import SKBarriers2.Corner.FrozenRowsNoise2
public import SKBarriers2.Corner.FrozenRowsMixed9
public import SKBarriers2.Corner.FrozenRowsMixed10

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic
namespace SKBarriers2.Corner

section UniversalLift
variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

def affineCoordinateEndpoint (c : AffineGaussianCoordinate P X) (z : P × (X × ℝ)) : X :=
  c.mean z.1 z.2.1 + c.shift z.1 + z.2.2 • c.noise z.1

def affineCoordinateDensityPotential (c : AffineGaussianCoordinate P X)
    (F : P × X → ℝ) (z : P × (X × ℝ)) : ℝ :=
  Real.exp (c.logMass z.1) * F (z.1,affineCoordinateEndpoint c z)

def affineCoordinateObservable (c : AffineGaussianCoordinate P X)
    (G : P × X → ℝ) (z : P × (X × ℝ)) : ℝ :=
  G (z.1,affineCoordinateEndpoint c z)

private def affineCoordinateNoiseBilinear (c : AffineGaussianCoordinate P X) :
    P →L[ℝ] (X × ℝ) →L[ℝ] X :=
  ((ContinuousLinearMap.compL ℝ (X × ℝ) X X).flip
    (ContinuousLinearMap.fst ℝ X ℝ)).comp c.mean +
  (((ContinuousLinearMap.compL ℝ (X × ℝ) ℝ X).flip
    (ContinuousLinearMap.snd ℝ X ℝ)).comp (ContinuousLinearMap.lsmul ℝ ℝ).flip).comp c.noise

private theorem affineCoordinateNoiseBilinear_apply (c : AffineGaussianCoordinate P X)
    (p : P) (y : X × ℝ) :
    affineCoordinateNoiseBilinear c p y = c.mean p y.1 + y.2 • c.noise p := rfl

theorem regular_affineCoordinateDensityPotential (c : AffineGaussianCoordinate P X)
    {F : P × X → ℝ} (hF : ParamRegular F) :
    ParamRegular (affineCoordinateDensityPotential c F) := by
  have H := ParamChain.regular_mul_exp_parameter
    (ParamChain.regular_affineBilinear
      (ParamChain.regular_parameterTranslation hF c.shift)
      (0 : (X × ℝ) →L[ℝ] X) (affineCoordinateNoiseBilinear c)) c.logMass
  convert H using 1
  funext z
  simp only [affineCoordinateDensityPotential,affineCoordinateEndpoint,
    zero_apply,zero_add,affineCoordinateNoiseBilinear_apply]
  congr 2
  abel

theorem smooth_affineCoordinateObservable (c : AffineGaussianCoordinate P X)
    {G : P × X → ℝ} (hG : ParamSmooth G) :
    ParamSmooth (affineCoordinateObservable c G) := by
  have H := ParamChain.smooth_affineBilinear
    (ParamChain.smooth_parameterTranslation hG c.shift)
    (0 : (X × ℝ) →L[ℝ] X) (affineCoordinateNoiseBilinear c)
  convert H using 1
  funext z
  simp only [affineCoordinateObservable,affineCoordinateEndpoint,
    zero_apply,zero_add,affineCoordinateNoiseBilinear_apply]
  congr 2
  abel

theorem affineCoordinateAverage_as_gaussianAverage
    (c : AffineGaussianCoordinate P X) (F G : P × X → ℝ) (z : P × X) :
    affineCoordinateAverage c F G z = OAI.SK.Analytic.gaussianAverage 1
      (fun w : (P × X) × ℝ => affineCoordinateDensityPotential c F (w.1.1,(w.1.2,w.2)))
      (fun w : (P × X) × ℝ => affineCoordinateObservable c G (w.1.1,(w.1.2,w.2))) z := by
  simp only [affineCoordinateAverage,vectorStepAverage,OAI.SK.Analytic.gaussianAverage,gaussianStepLaw,
    affineCoordinateDensityPotential,affineCoordinateObservable,affineCoordinateEndpoint,one_mul]

theorem paramSmooth_moving_endpoint_first {G : P × X → ℝ} (hG : ParamSmooth G)
    {p : ℝ → P} {x : ℝ → X} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (hx : ContDiffAt ℝ 2 x k) :
    deriv (fun t => G (p t,x t)) k =
      deriv (fun t => G (p t,x k)) k +
        fderiv ℝ (fun y => G (p k,y)) (x k) (deriv x k) := by
  have hpd := (hp.differentiableAt (by norm_num)).hasDerivAt
  have hxd := (hx.differentiableAt (by norm_num)).hasDerivAt
  have hd := (hG.1.differentiable (by norm_num) (p k,x k)).hasFDerivAt
  have ht := (hd.comp_hasDerivAt k (hpd.prodMk hxd)).deriv
  have hi := (hd.comp_hasDerivAt k (hpd.prodMk (hasDerivAt_const k (x k)))).deriv
  have hs := (hd.comp (x k)
    ((hasFDerivAt_const (p k) (x k)).prodMk (hasFDerivAt_id (x k)))).fderiv
  have hse := congrArg (fun L : X →L[ℝ] ℝ => L (deriv x k)) hs
  change fderiv ℝ (fun y => G (p k,y)) (x k) (deriv x k) =
    fderiv ℝ G (p k,x k) (0,deriv x k) at hse
  dsimp only [Function.comp_def] at ht hi
  rw [ht,hi,hse,← map_add]
  congr 1
  ext <;> simp

theorem affineCoordinateEndpoint_contDiffAt (c : AffineGaussianCoordinate P X)
    {p : ℝ → P} {k : ℝ} (hp : ContDiffAt ℝ 2 p k) (x : X) (t : ℝ) :
    ContDiffAt ℝ 2 (fun z => affineCoordinateEndpoint c (p z,(x,t))) k := by
  exact (((c.mean.contDiff.contDiffAt.comp k hp).clm_apply contDiffAt_const).add
    (c.shift.contDiff.contDiffAt.comp k hp)).add ((c.noise.contDiff.contDiffAt.comp k hp).const_smul t)

theorem affineCoordinateObservable_scaled_first (c : AffineGaussianCoordinate P X)
    {G : P × X → ℝ} (hG : ParamSmooth G) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (ρ : ℝ) (x : X) (t : ℝ) :
    ρ * deriv (fun z => affineCoordinateObservable c G (p z,(x,t))) k =
      ρ * deriv (fun z => G (p z,affineCoordinateEndpoint c (p k,(x,t)))) k +
        fderiv ℝ (fun y => G (p k,y)) (affineCoordinateEndpoint c (p k,(x,t)))
          (ρ • deriv (fun z => affineCoordinateEndpoint c (p z,(x,t))) k) := by
  rw [map_smul,smul_eq_mul]
  have H := paramSmooth_moving_endpoint_first hG hp
    (affineCoordinateEndpoint_contDiffAt c hp x t)
  change ρ * deriv (fun z => G (p z,affineCoordinateEndpoint c (p z,(x,t)))) k = _
  rw [H]
  ring

theorem affineCoordinateAverage_scaled_first_centered
    (c : AffineGaussianCoordinate P X) {F G : P × X → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (x : X) (center ρ : ℝ) :
    let H := affineCoordinateDensityPotential c F
    let J := affineCoordinateObservable c G
    let μ := gaussianStepLaw 1
      (fun w : (P × X) × ℝ => H (w.1.1,(w.1.2,w.2))) (p k,x)
    ρ * deriv (fun t => affineCoordinateAverage c F G (p t,x)) k =
      (∫ t, ρ * deriv (fun z => J (p z,(x,t))) k ∂μ) +
      (∫ t, (J (p k,(x,t))-center) * (ρ * deriv (fun z => H (p z,(x,t))) k) ∂μ) -
      (∫ t, J (p k,(x,t))-center ∂μ) *
        (∫ t, ρ * deriv (fun z => H (p z,(x,t))) k ∂μ) := by
  have H := gaussianAverage_curve_scaled_first_centered
    (regular_affineCoordinateDensityPotential c hF) (smooth_affineCoordinateObservable c hG)
    hp x center ρ
  dsimp only at H
  have he : (fun t => affineCoordinateAverage c F G (p t,x)) =
      fun t => OAI.SK.Analytic.gaussianAverage 1
        (fun w : (P × X) × ℝ => affineCoordinateDensityPotential c F (w.1.1,(w.1.2,w.2)))
        (fun w : (P × X) × ℝ => affineCoordinateObservable c G (w.1.1,(w.1.2,w.2))) (p t,x) :=
    funext (fun t => affineCoordinateAverage_as_gaussianAverage c F G (p t,x))
  rw [← he] at H
  exact H

end UniversalLift

section ThreeDimensional
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "X" => (Fin 3 → ℝ)

theorem affineCoordinateAverage_scaled_first_eq_transport
    (c : AffineGaussianCoordinate P X) {F G : P × X → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (center : X → ℝ) (ρ : ℝ) (x : X) :
    ρ * deriv (fun t => affineCoordinateAverage c F G (p t,x)) k =
      StepCalculus.centeredFirstNoiseTransport (Real.exp (c.logMass (p k))) (c.noise (p k))
        (fun y => F (p k,y)) (c.mean (p k)) (c.shift (p k))
        (fun t x => ρ * deriv (fun z => affineCoordinateObservable c G (p z,(x,t))) k)
        (fun t x => affineCoordinateObservable c G (p k,(x,t)) - center x)
        (fun t x => ρ * deriv (fun z => affineCoordinateDensityPotential c F (p z,(x,t))) k) x := by
  have H := affineCoordinateAverage_scaled_first_centered c hF hG hp x (center x) ρ
  dsimp only at H
  have hμ : gaussianStepLaw 1
      (fun w : (P × X) × ℝ => affineCoordinateDensityPotential c F (w.1.1,(w.1.2,w.2))) (p k,x) =
      StepCalculus.stepLaw (Real.exp (c.logMass (p k))) (c.noise (p k))
        (fun y => F (p k,y)) (c.mean (p k) x + c.shift (p k)) := by
    simp only [gaussianStepLaw,StepCalculus.stepLaw,affineCoordinateDensityPotential,
      affineCoordinateEndpoint,one_mul,Function.comp_def,vectorTranslation,
      add_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.smulRight_apply]
  rw [hμ] at H
  exact H

end ThreeDimensional
end SKBarriers2.Corner
