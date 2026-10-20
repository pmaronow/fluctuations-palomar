module

public import SKBarriers2.Corner.FrozenRowsMixedAverageTransport
public import SKBarriers2.Corner.FrozenRowsMixed30

@[expose] public section

noncomputable section
open scoped Topology ContDiff
open Set OAI.SK.Analytic SKOptimized.Overshoot
namespace SKBarriers2.Corner
open StepCalculus
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem spatialBound_parameterCurveKJet_affineAverage
    (c : AffineGaussianCoordinate P Vec3) {F G : P × Vec3 → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G) {p : ℝ → P} {k : ℝ}
    {r n q : ℕ} {B C L σ δ K D : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (hn : 2 ≤ n)
    (hf : QPotential (r+2) B (fun y => F (p k,y)))
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hδ : |δ| ≤ 1)
    (hK : 1 ≤ K) (hv : ‖c.noise (p k)‖ ≤ K)
    (hm : Real.exp (c.logMass (p k)) ∈ Icc (0 : ℝ) 1)
    (Htest : MovingNoiseTestPacket r C n q δ
      (fun t y => affineCoordinateObservable c G (p k,(y,t)))
      (fun t y => σ*deriv (fun κ => affineCoordinateObservable c G (p κ,(y,t))) k)
      (fun t y => affineCoordinateObservable c G (p k,(y,t))-
        affineCoordinateObservable c G (p k,(y,0)))
      (fun t y => σ*deriv (fun κ => affineCoordinateObservable c G (p κ,(y,t))) k-
        σ*deriv (fun κ => affineCoordinateObservable c G (p κ,(y,0))) k)
      (fun t y => σ^2*deriv (deriv (fun κ => affineCoordinateObservable c G (p κ,(y,t)))) k))
    (s₀ s₁ t₀ t₁ t₂ : ℝ → Vec3 → ℝ)
    (hs₀ : ContDiff ℝ r (Function.uncurry s₀))
    (hs₁ : ContDiff ℝ r (Function.uncurry s₁))
    (ht₀ : ContDiff ℝ r (Function.uncurry t₀))
    (ht₁ : ContDiff ℝ r (Function.uncurry t₁))
    (ht₂ : ContDiff ℝ r (Function.uncurry t₂))
    (hs₀j : ∀ t, WJets r (L*(1+|t|)^q) 0 (s₀ t))
    (hs₁j : ∀ t, WJets r (L*(1+|t|)^q) 1 (s₁ t))
    (ht₀j : ∀ t, WJets r (L*(1+|t|)^q) 0 (t₀ t))
    (ht₁j : ∀ t, WJets r (L*(1+|t|)^q) 1 (t₁ t))
    (ht₂j : ∀ t, WJets r (L*(1+|t|)^q) 2 (t₂ t))
    (hscore : ∀ t y, σ*deriv (fun κ => affineCoordinateDensityPotential c F (p κ,(y,t))) k =
      s₀ t y+δ*s₁ t y)
    (hsecond : ∀ t y, σ^2*deriv (deriv (fun κ => affineCoordinateDensityPotential c F (p κ,(y,t)))) k =
      t₀ t y+δ*t₁ t y+δ^2*t₂ t y)
    (hD : affineNoiseAverageCoefficient r q (B*K^(r+2)) (K⁻¹ • c.mean (p k)) ≤ D ∧
      spatialFirstNoiseTransportBudget r q (B*K^(r+2)) L (K⁻¹ • c.mean (p k)) ≤ D ∧
      spatialSecondNoiseTransportBudget r q (B*K^(r+2)) L (K⁻¹ • c.mean (p k)) ≤ D) :
    MomentKJet.SpatialBound r (D*C) n
      (fun y => MomentKJet.rescale σ (parameterCurveKJet (affineCoordinateAverage c F G) p k y)) := by
  have H := spatialBound_affineNoiseKJet hn hf hC hL hδ
    Htest.value_smooth Htest.first_smooth Htest.centered_value_smooth
    Htest.second_smooth Htest.centered_first_smooth hs₀ hs₁ ht₀ ht₁ ht₂
    Htest.value Htest.first (fun t => (Htest.centered t).value)
    (fun t => (Htest.centered t).coarse_value) (fun t => (Htest.centered t).second)
    (fun t => (Htest.centered t).first) (fun t => (Htest.centered t).coarse_first)
    hs₀j hs₁j ht₀j ht₁j ht₂j hm hK (c.noise (p k)) hv (c.mean (p k)) (c.shift (p k)) hD
  have hS : (fun t y => σ*deriv (fun κ => affineCoordinateDensityPotential c F (p κ,(y,t))) k) =
      fun t y => s₀ t y+δ*s₁ t y := funext (fun t => funext (hscore t))
  have hT : (fun t y => σ^2*deriv (deriv (fun κ => affineCoordinateDensityPotential c F (p κ,(y,t)))) k) =
      fun t y => t₀ t y+δ*t₁ t y+δ^2*t₂ t y := funext (fun t => funext (hsecond t))
  have he : (fun y => MomentKJet.rescale σ
      (parameterCurveKJet (affineCoordinateAverage c F G) p k y)) =
      affineNoiseKJet (Real.exp (c.logMass (p k))) (c.noise (p k))
        (fun y => F (p k,y)) (c.mean (p k)) (c.shift (p k))
        (fun t y => affineCoordinateObservable c G (p k,(y,t)))
        (fun t y => σ*deriv (fun κ => affineCoordinateObservable c G (p κ,(y,t))) k)
        (fun t y => affineCoordinateObservable c G (p k,(y,t))-affineCoordinateObservable c G (p k,(y,0)))
        (fun t y => σ^2*deriv (deriv (fun κ => affineCoordinateObservable c G (p κ,(y,t)))) k)
        (fun t y => σ*deriv (fun κ => affineCoordinateObservable c G (p κ,(y,t))) k-
          σ*deriv (fun κ => affineCoordinateObservable c G (p κ,(y,0))) k)
        (fun t y => s₀ t y+δ*s₁ t y) (fun t y => t₀ t y+δ*t₁ t y+δ^2*t₂ t y) := by
    funext y
    have HE := parameterCurveKJet_affineAverage_eq_transport c hF hG hp
      (hf.of_le (by omega : 2 ≤ r+2))
      (fun y => σ*deriv (fun κ => affineCoordinateObservable c G (p κ,(y,0))) k)
      (fun y => affineCoordinateObservable c G (p k,(y,0))) σ y
    rwa [hS,hT] at HE
  rw [he]
  exact H

end SKBarriers2.Corner
