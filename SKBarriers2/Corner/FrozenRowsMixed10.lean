module

public import SKBarriers2.Corner.FrozenRowsInductionK

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic

namespace SKBarriers2.Corner

variable {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem gaussianAverage_curve_first_centered {H G : P × (X × ℝ) → ℝ}
    (hH : ParamRegular H) (hG : ParamSmooth G) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (x : X) (c : ℝ) :
    let U := fun z : (P × X) × ℝ => H (z.1.1,(z.1.2,z.2))
    let J := fun z : (P × X) × ℝ => G (z.1.1,(z.1.2,z.2))
    let μ := gaussianStepLaw 1 U (p k,x)
    deriv (fun t => OAI.SK.Analytic.gaussianAverage 1 U J (p t,x)) k =
      (∫ t, deriv (fun q => G (p q,(x,t))) k ∂μ) +
        (∫ t, (G (p k,(x,t)) - c) * deriv (fun q => H (p q,(x,t))) k ∂μ) -
        (∫ t, G (p k,(x,t)) - c ∂μ) *
          (∫ t, deriv (fun q => H (p q,(x,t))) k ∂μ) := by
  dsimp only
  have hGm := gaussian_curve_jets_memLp hH hG hp x
  have hHm := gaussian_curve_jets_memLp hH hH.toSmooth hp x
  dsimp only at hGm hHm
  have hexp := (hH.2.1.exp_mul 1).weakLocallyDominated.integrable_section
    (Real.continuous_exp.comp (continuous_const.mul (hH.1.continuous.comp
      (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))))) (p k,x)
  let : IsProbabilityMeasure
      (gaussianStepLaw 1 (fun z : (P × X) × ℝ => H (z.1.1,(z.1.2,z.2))) (p k,x)) :=
    isProbabilityMeasure_tilted hexp
  have hfirst := ParamChain.gaussianAverage_curve_first hH hG hp x
  dsimp only at hfirst
  have hprod : Integrable (fun t => G (p k,(x,t)) *
      deriv (fun q => H (p q,(x,t))) k)
      (gaussianStepLaw 1 (fun z : (P × X) × ℝ => H (z.1.1,(z.1.2,z.2))) (p k,x)) :=
    (hGm.1.integrable_mul hHm.2.1).congr (ae_of_all _ (fun _ => by simp only [Pi.mul_apply]))
  rw [integral_add (hGm.2.1.integrable (by norm_num)) hprod] at hfirst
  have hj : deriv (fun t => OAI.SK.Analytic.gaussianAverage 1
      (fun z : (P × X) × ℝ => H (z.1.1,(z.1.2,z.2)))
      (fun z : (P × X) × ℝ => G (z.1.1,(z.1.2,z.2))) (p t,x)) k =
    (∫ t, deriv (fun q => G (p q,(x,t))) k
      ∂gaussianStepLaw 1 (fun z : (P × X) × ℝ => H (z.1.1,(z.1.2,z.2))) (p k,x)) +
      covariance (fun t => G (p k,(x,t)))
        (fun t => deriv (fun q => H (p q,(x,t))) k)
          (gaussianStepLaw 1 (fun z : (P × X) × ℝ => H (z.1.1,(z.1.2,z.2))) (p k,x)) := by
    rw [hfirst, covariance_eq_sub hGm.1 hHm.2.1]
    simp only [Pi.mul_apply]
    ring
  rw [← covariance_sub_const_left (hGm.1.integrable (by norm_num)) c] at hj
  have hcenter : MemLp (fun t => G (p k,(x,t)) - c) 2
      (gaussianStepLaw 1 (fun z : (P × X) × ℝ => H (z.1.1,(z.1.2,z.2))) (p k,x)) := by
    exact MemLp.ae_eq (ae_of_all _ (fun _ => by simp only [Pi.sub_apply]))
      (hGm.1.sub (memLp_const c))
  rw [covariance_eq_sub hcenter hHm.2.1] at hj
  simpa only [Pi.mul_apply, add_sub_assoc] using hj

theorem gaussianAverage_curve_scaled_first_centered {H G : P × (X × ℝ) → ℝ}
    (hH : ParamRegular H) (hG : ParamSmooth G) {p : ℝ → P} {k : ℝ}
    (hp : ContDiffAt ℝ 2 p k) (x : X) (c ρ : ℝ) :
    let U := fun z : (P × X) × ℝ => H (z.1.1,(z.1.2,z.2))
    let J := fun z : (P × X) × ℝ => G (z.1.1,(z.1.2,z.2))
    let μ := gaussianStepLaw 1 U (p k,x)
    ρ * deriv (fun t => OAI.SK.Analytic.gaussianAverage 1 U J (p t,x)) k =
      (∫ t, ρ * deriv (fun q => G (p q,(x,t))) k ∂μ) +
        (∫ t, (G (p k,(x,t)) - c) * (ρ * deriv (fun q => H (p q,(x,t))) k) ∂μ) -
        (∫ t, G (p k,(x,t)) - c ∂μ) *
          (∫ t, ρ * deriv (fun q => H (p q,(x,t))) k ∂μ) := by
  dsimp only
  rw [gaussianAverage_curve_first_centered hH hG hp x c]
  have he : (fun t => (G (p k,(x,t)) - c) *
      (ρ * deriv (fun q => H (p q,(x,t))) k)) =
      fun t => ρ * ((G (p k,(x,t)) - c) * deriv (fun q => H (p q,(x,t))) k) := by
    funext t
    ring
  rw [he, integral_const_mul, integral_const_mul, integral_const_mul]
  ring

end SKBarriers2.Corner
