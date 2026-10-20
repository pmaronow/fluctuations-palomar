module

public import SKBarriers2.Corner.FrozenRowsMixed29
public import SKBarriers2.Corner.FrozenRowsMixed17
public import SKBarriers2.Corner.FrozenRowsMixedCurveJet

@[expose] public section

noncomputable section
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic SKOptimized.Overshoot
namespace SKBarriers2.Corner

theorem parameterCurveKJet_affineAverage_eq_transport
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (c : AffineGaussianCoordinate P Vec3) {F G : P × Vec3 → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G) {p : ℝ → P} {k B : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (hf : QPotential 2 B (fun y => F (p k,y)))
    (centerFirst centerValue : Vec3 → ℝ) (σ : ℝ) (x : Vec3) :
    MomentKJet.rescale σ (parameterCurveKJet (affineCoordinateAverage c F G) p k x) =
      affineNoiseKJet (Real.exp (c.logMass (p k))) (c.noise (p k))
        (fun y => F (p k,y)) (c.mean (p k)) (c.shift (p k))
        (fun t y => affineCoordinateObservable c G (p k,(y,t)))
        (fun t y => σ * deriv (fun κ => affineCoordinateObservable c G (p κ,(y,t))) k)
        (fun t y => affineCoordinateObservable c G (p k,(y,t))-centerValue y)
        (fun t y => σ^2 * deriv (deriv (fun κ => affineCoordinateObservable c G (p κ,(y,t)))) k)
        (fun t y => σ * deriv (fun κ => affineCoordinateObservable c G (p κ,(y,t))) k-centerFirst y)
        (fun t y => σ * deriv (fun κ => affineCoordinateDensityPotential c F (p κ,(y,t))) k)
        (fun t y => σ^2 * deriv (deriv (fun κ => affineCoordinateDensityPotential c F (p κ,(y,t)))) k) x := by
  have hfirst := affineCoordinateAverage_scaled_first_eq_transport c hF hG hp centerValue σ x
  have hsecond := affineCoordinateAverage_scaled_second_eq_transport c hF hG hp hf centerFirst centerValue σ x
  change MomentKJet.mk (affineCoordinateAverage c F G (p k,x))
    (σ * deriv (fun t => affineCoordinateAverage c F G (p t,x)) k)
    (σ^2 * deriv (deriv (fun t => affineCoordinateAverage c F G (p t,x))) k) = _
  rw [hfirst,hsecond]
  rfl

end SKBarriers2.Corner
