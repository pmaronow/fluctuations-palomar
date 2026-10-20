module

public import SKBarriers2.Corner.FrozenRowsMixed15
public import SKBarriers2.Corner.FrozenRowsMixed12
public import SKBarriers2.Corner.FrozenRowsInductionK
public import SKBarriers2.Corner.PathEnergyProof3
public import SKBarriers2.Analysis.ParamStep4

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic
namespace SKBarriers2.StepCalculus
local notation "X" => (Fin 3 → ℝ)

theorem memLp_noise_weightedFamily {r p q : ℕ} {B C m : ℝ} {f : X → ℝ}
    {G : ℝ → X → ℝ} (hf : QPotential 3 B f) (hC : 0 ≤ C)
    (hG : ContDiff ℝ r (Function.uncurry G))
    (hGj : ∀ t, WJets r (C*(1+|t|)^q) p (G t)) (v a x : X) :
    MemLp (fun t => G t x) 2 (stepLaw m v f a) := by
  apply memLp_noise_of_growth hf m v a
    (hG.continuous.comp (continuous_id.prodMk continuous_const))
  refine ⟨C*(1+‖x‖)^p,q,by positivity,by positivity,?_⟩
  intro t
  have hpow : (1+|t|)^q ≤ Real.exp ((q:ℝ)*|t|) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity)
      (by simpa only [add_comm] using Real.add_one_le_exp |t|) q
  calc
    _ ≤ C*(1+|t|)^q*(1+‖x‖)^p := (hGj t).norm_le x
    _ ≤ C*Real.exp ((q:ℝ)*|t|)*(1+‖x‖)^p := by gcongr
    _ = _ := by rw [Real.norm_eq_abs]; ring

theorem affineNoiseCovariance_eq_covariance {B m : ℝ} {f : X → ℝ}
    (hf : QPotential 2 B f) (v : X) (A : X →L[ℝ] X) (b x : X)
    {G H : ℝ → X → ℝ}
    (hG : MemLp (fun t => G t x) 2 (stepLaw m v f (A x+b)))
    (hH : MemLp (fun t => H t x) 2 (stepLaw m v f (A x+b))) :
    affineNoiseCovariance m v f A b G H x =
      covariance (fun t => G t x) (fun t => H t x) (stepLaw m v f (A x+b)) := by
  let _ := stepLaw_probability hf le_rfl m v (A x+b)
  rw [covariance_eq_sub hG hH]
  rfl

set_option maxHeartbeats 800000 in
theorem secondAffineNoiseTransport_eq_secondAverageTransport {B m : ℝ} {f : X → ℝ}
    (hf : QPotential 2 B f) (v : X) (A : X →L[ℝ] X) (b x : X)
    {B₂ A₁ C₀ S T : ℝ → X → ℝ}
    (hA : MemLp (fun t => A₁ t x) 2 (stepLaw m v f (A x+b)))
    (hC : MemLp (fun t => C₀ t x) 2 (stepLaw m v f (A x+b)))
    (hS : MemLp (fun t => S t x) 2 (stepLaw m v f (A x+b)))
    (hT : MemLp (fun t => T t x) 2 (stepLaw m v f (A x+b)))
    (hSq : MemLp (fun t => S t x^2) 2 (stepLaw m v f (A x+b))) :
    secondAffineNoiseTransport m v f A b B₂ A₁ C₀ S T x =
      secondAverageTransport (stepLaw m v f (A x+b))
        (fun t => C₀ t x) (fun t => A₁ t x) (fun t => B₂ t x)
        (fun t => S t x) (fun t => T t x) := by
  let _ := stepLaw_probability hf le_rfl m v (A x+b)
  unfold secondAffineNoiseTransport secondAverageTransport
  rw [affineNoiseCovariance_eq_covariance (G := A₁) (H := S) hf v A b x hA hS,
    affineNoiseCovariance_eq_covariance (G := C₀) (H := T) hf v A b x hC hT,
    affineNoiseCovariance_eq_covariance (G := C₀) (H := fun t y => S t y^2) hf v A b x hC hSq,
    affineNoiseCovariance_eq_covariance (G := C₀) (H := S) hf v A b x hC hS]
  simp only [noiseMean]
  ring

set_option maxHeartbeats 800000 in
theorem secondAverageTransport_eq_secondAffineNoiseTransport_centered
    {B m : ℝ} {f : X → ℝ}
    (hf : QPotential 2 B f) (v : X) (A : X →L[ℝ] X) (b x : X)
    {B₂ A₁ C₀ S T : ℝ → X → ℝ}
    (hA : MemLp (fun t => A₁ t x) 2 (stepLaw m v f (A x+b)))
    (hC : MemLp (fun t => C₀ t x) 2 (stepLaw m v f (A x+b)))
    (hS : MemLp (fun t => S t x) 2 (stepLaw m v f (A x+b)))
    (hT : MemLp (fun t => T t x) 2 (stepLaw m v f (A x+b)))
    (hSq : MemLp (fun t => S t x^2) 2 (stepLaw m v f (A x+b)))
    (a₀ c₀ : X → ℝ) :
    secondAverageTransport (stepLaw m v f (A x+b))
      (fun t => C₀ t x) (fun t => A₁ t x) (fun t => B₂ t x)
      (fun t => S t x) (fun t => T t x) =
      secondAffineNoiseTransport m v f A b B₂
        (fun t y => A₁ t y-a₀ y) (fun t y => C₀ t y-c₀ y) S T x := by
  let _ := stepLaw_probability hf le_rfl m v (A x+b)
  rw [secondAffineNoiseTransport_eq_secondAverageTransport
    (B₂ := B₂) (A₁ := fun t y => A₁ t y-a₀ y) (C₀ := fun t y => C₀ t y-c₀ y)
    (S := S) (T := T) hf v A b x
    (hA.sub (memLp_const (a₀ x))) (hC.sub (memLp_const (c₀ x))) hS hT hSq]
  unfold secondAverageTransport
  rw [covariance_sub_const_left (hA.integrable (by norm_num)),
    covariance_sub_const_left (hC.integrable (by norm_num)),
    covariance_sub_const_left (hC.integrable (by norm_num)),
    covariance_sub_const_left (hC.integrable (by norm_num))]

end SKBarriers2.StepCalculus

namespace SKBarriers2.Corner
local notation "X" => (Fin 3 → ℝ)
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

set_option maxHeartbeats 800000 in
theorem affineCoordinateAverage_scaled_second_eq_transport
    (c : AffineGaussianCoordinate P X) {F G : P × X → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G) {p : ℝ → P} {k B : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (hf : QPotential 2 B (fun y => F (p k,y)))
    (centerFirst centerValue : X → ℝ) (ρ : ℝ) (x : X) :
    ρ^2 * deriv (deriv (fun t => affineCoordinateAverage c F G (p t,x))) k =
      StepCalculus.secondAffineNoiseTransport (Real.exp (c.logMass (p k))) (c.noise (p k))
        (fun y => F (p k,y)) (c.mean (p k)) (c.shift (p k))
        (fun t y => ρ^2 * deriv (deriv (fun z => affineCoordinateObservable c G (p z,(y,t)))) k)
        (fun t y => ρ * deriv (fun z => affineCoordinateObservable c G (p z,(y,t))) k-centerFirst y)
        (fun t y => affineCoordinateObservable c G (p k,(y,t))-centerValue y)
        (fun t y => ρ * deriv (fun z => affineCoordinateDensityPotential c F (p z,(y,t))) k)
        (fun t y => ρ^2 * deriv (deriv (fun z => affineCoordinateDensityPotential c F (p z,(y,t)))) k) x := by
  let H := affineCoordinateDensityPotential c F
  let J := affineCoordinateObservable c G
  have hH := regular_affineCoordinateDensityPotential c hF
  have hJ := smooth_affineCoordinateObservable c hG
  have hGm := gaussian_curve_jets_memLp hH hJ hp x
  have hHm := gaussian_curve_jets_memLp hH hH.toSmooth hp x
  have hjet := gaussianAverage_curve_transportKJet hH hJ hp x
  dsimp only at hGm hHm hjet
  have HR := congrArg (fun K : MomentKJet => (MomentKJet.rescale ρ K).second) hjet
  rw [averageTransportKJet_rescale] at HR
  change ρ^2 * deriv (deriv (fun t => OAI.SK.Analytic.gaussianAverage 1
      (fun w : (P × X) × ℝ => H (w.1.1,(w.1.2,w.2)))
      (fun w : (P × X) × ℝ => J (w.1.1,(w.1.2,w.2))) (p t,x))) k =
    StepCalculus.secondAverageTransport
      (gaussianStepLaw 1 (fun w : (P × X) × ℝ => H (w.1.1,(w.1.2,w.2))) (p k,x))
      (fun t => J (p k,(x,t)))
      (fun t => ρ * deriv (fun z => J (p z,(x,t))) k)
      (fun t => ρ^2 * deriv (deriv (fun z => J (p z,(x,t)))) k)
      (fun t => ρ * deriv (fun z => H (p z,(x,t))) k)
      (fun t => ρ^2 * deriv (deriv (fun z => H (p z,(x,t)))) k) at HR
  have he : (fun t => affineCoordinateAverage c F G (p t,x)) =
      fun t => OAI.SK.Analytic.gaussianAverage 1
        (fun w : (P × X) × ℝ => H (w.1.1,(w.1.2,w.2)))
        (fun w : (P × X) × ℝ => J (w.1.1,(w.1.2,w.2))) (p t,x) :=
    funext (fun t => affineCoordinateAverage_as_gaussianAverage c F G (p t,x))
  rw [← he] at HR
  have hμ : gaussianStepLaw 1
      (fun w : (P × X) × ℝ => H (w.1.1,(w.1.2,w.2))) (p k,x) =
      StepCalculus.stepLaw (Real.exp (c.logMass (p k))) (c.noise (p k))
        (fun y => F (p k,y)) (c.mean (p k) x+c.shift (p k)) := by
    simp only [H,gaussianStepLaw,StepCalculus.stepLaw,affineCoordinateDensityPotential,
      affineCoordinateEndpoint,one_mul,Function.comp_def,vectorTranslation,
      add_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.smulRight_apply]
  rw [hμ] at HR hGm hHm
  have hsq : MemLp (fun t => (ρ * deriv (fun z => H (p z,(x,t))) k)^2) 2
      (StepCalculus.stepLaw (Real.exp (c.logMass (p k))) (c.noise (p k))
        (fun y => F (p k,y)) (c.mean (p k) x+c.shift (p k))) := by
    convert hHm.2.2.2.const_mul (ρ^2) using 1
    funext t
    ring
  exact HR.trans (StepCalculus.secondAverageTransport_eq_secondAffineNoiseTransport_centered
    (B₂ := fun t y => ρ^2 * deriv (deriv (fun z => J (p z,(y,t)))) k)
    (A₁ := fun t y => ρ * deriv (fun z => J (p z,(y,t))) k)
    (C₀ := fun t y => J (p k,(y,t)))
    (S := fun t y => ρ * deriv (fun z => H (p z,(y,t))) k)
    (T := fun t y => ρ^2 * deriv (deriv (fun z => H (p z,(y,t)))) k)
    hf (c.noise (p k)) (c.mean (p k)) (c.shift (p k)) x
    (hGm.2.1.const_mul ρ) hGm.1 (hHm.2.1.const_mul ρ)
    (hHm.2.2.1.const_mul (ρ^2)) hsq centerFirst centerValue)

end SKBarriers2.Corner
