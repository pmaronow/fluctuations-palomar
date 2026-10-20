module

public import SKBarriers2.Analysis.TiltedAffineStep
public import SKBarriers2.Corner.FrozenRowsMoments6
public import SKBarriers2.Corner.FrozenCoef6
public import OAI.Probability.SKBarriers.Scalar.ScalarSuffixSusceptibility

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def quadraticMeanLinear (Q : QuadraticTerminal) (m : ℝ) (v : Vec3) : Vec3 →L[ℝ] Vec3 :=
  (quadraticNoiseCLM Q m v).comp (ContinuousLinearMap.inl ℝ Vec3 ℝ)

theorem quadraticMeanTransition_eq_affine (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3) :
    quadraticMeanTransition Q m v x = quadraticMeanLinear Q m v x + quadraticNoiseConstant Q m v := by
  simpa only [quadraticMeanLinear, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, mul_zero, add_zero, zero_add, zero_smul, add_comm,
    quadraticMeanTransition] using (quadraticNoise_affine Q m v x 0).symm

theorem vectorStep_eq_quadratic_add_tiltedAffineStep
    (Q : QuadraticTerminal) (m : ℝ) (v x : Vec3) {R : Vec3 → ℝ}
    (hR : Continuous R) (hm : m ≠ 0) (hD : 0 < Q.precision m v)
    (hpos : 0 < quadraticAverage Q m v (fun y => Real.exp (m * R y)) x) :
    vectorStep m v (fun y => Q.value y + R y) x = (Q.update m v).value x +
      StepCalculus.tiltedAffineStep m (quadraticMeanLinear Q m v)
        (quadraticNoiseConstant Q m v) ((Real.sqrt (Q.precision m v)⁻¹) • v) R x := by
  rw [Q.vectorStep_add_correction m v x R hm hD hpos,
    quadraticAverage_eq_standard Q m v x hD (by fun_prop),
    quadraticMeanTransition_eq_affine]
  simp only [StepCalculus.tiltedAffineStep, vectorStep, gaussianStep,
    ite_eq_right hm, positiveGaussianLogStep]

theorem quadraticTaylorTailFirst_unbounded {f : ℝ → ℝ} {A z : ℝ}
    (hf : ∀ y, |deriv f y| ≤ A) (hχ : deriv (deriv f) z ≠ 0) (B : ℝ) :
    ∃ y, B < |quadraticTaylorTailFirst f z y| := by
  simpa only [quadraticTaylorTailFirst, scalarTaylorPolynomial,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, iteratedDeriv_zero,
    iteratedDeriv_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
    pow_zero, pow_one, mul_one, div_one] using
    unbounded_sub_linear_of_bounded (u := deriv f z) (z := z) hf hχ B

theorem terminalResidual_not_qPotential {β s h z A : ℝ} {α : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ (Phi β α (s + 4 * h)))
    (hb : ∀ y, |deriv (Phi β α (s + 4 * h)) y| ≤ A)
    (hχ : jet β α 2 (s + 4 * h) z ≠ 0) {r : ℕ} (hr : 1 ≤ r) (B : ℝ) :
    ¬ QPotential r B (terminalResidual β α s h z) := by
  intro hR
  let c : Vec3 := fun _ => z
  let e : Vec3 := Pi.single 2 1
  have he : ‖e‖ = 1 := by
    dsimp only [e]
    rw [Pi.norm_single, norm_one]
  have hcurve : LipschitzWith 1 (fun y : ℝ => c + (y - z) • e) := by
    apply LipschitzWith.of_dist_le_mul
    intro y w
    rw [dist_eq_norm, Real.dist_eq]
    have heq : c + (y - z) • e - (c + (w - z) • e) = (y - w) • e := by module
    rw [heq, norm_smul, Real.norm_eq_abs, he]
    simp
  have hEq : (fun y => terminalResidual β α s h z (c + (y - z) • e)) =
      quadraticTaylorTail (Phi β α (s + 4 * h)) z := by
    funext y
    simpa only [c, e, one_smul, one_mul, add_sub_cancel] using
      terminalResidual_scalar_axis β α s h z 1 (y - z)
  have hLip := (hR.lipschitzWith hr).comp hcurve
  simp only [Function.comp_def] at hLip
  rw [hEq] at hLip
  have hbounded (y : ℝ) : |quadraticTaylorTailFirst (Phi β α (s + 4 * h)) z y| ≤ B := by
    have H := (quadraticTaylorTail_derivatives hf z y).1.le_of_lipschitz hLip
    change ‖quadraticTaylorTailFirst (Phi β α (s + 4 * h)) z y‖ ≤ B * 1 at H
    simpa only [Real.norm_eq_abs, mul_one] using H
  have hχ' : deriv (deriv (Phi β α (s + 4 * h))) z ≠ 0 := by
    simpa only [jet, iteratedDeriv_succ, iteratedDeriv_zero] using hχ
  obtain ⟨y, hy⟩ := quadraticTaylorTailFirst_unbounded hb hχ' B
  exact (not_lt_of_ge (hbounded y)) hy

theorem scalarData_terminalResidual_not_qPotential {β s h z : ℝ} (D : ScalarData β)
    (ht : s + 4 * h ∈ Icc (0 : ℝ) 1)
    (hχ : jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z ≠ 0)
    {r : ℕ} (hr : 1 ≤ r) (B : ℝ) :
    ¬ QPotential r B (terminalResidual β (cdf (D.μ : Measure ℝ)) s h z) := by
  apply terminalResidual_not_qPotential (A := scalarTerminalJetBound D 1)
    (scalarData_phi_contDiff D ht) _ hχ hr B
  intro y
  simpa only [jet, iteratedDeriv_one] using
    scalarData_jet_le D (by norm_num : 1 ≤ 1) le_rfl ht y

theorem scalarData_exists_nonzero_second_jet {β t : ℝ} (D : ScalarData β)
    (ht : t ∈ Ioo (0 : ℝ) D.q) :
    ∃ z, jet β (cdf (D.μ : Measure ℝ)) 2 t z ≠ 0 := by
  by_contra! H
  have ht' : t ∈ Icc (0 : ℝ) 1 :=
    ⟨ht.1.le, ht.2.le.trans D.q_mem.2.le⟩
  have hf := scalarData_phi_regular D ht'
  have hzero : scalarLaw β (cdf (D.μ : Measure ℝ)) t (fun _ => (0 : ℝ)) = 0 := by
    simp only [scalarLaw, scalarCDFAverage, dyadicScalarAverage,
      scalarHierarchyAverage_const hf]
    exact tendsto_const_nhds.limUnder_eq
  have hfun : (fun x => jet β (cdf (D.μ : Measure ℝ)) 2 t x ^ 2) =
      fun _ => (0 : ℝ) := by
    funext x
    rw [H x, zero_pow (by norm_num : 2 ≠ 0)]
  have hc := D.contact₁ t ht
  rw [hfun, hzero, mul_zero] at hc
  norm_num at hc

theorem scalarData_terminalRiccatiResidual_obstruction {β s h : ℝ} (D : ScalarData β)
    (ht : s + 4 * h ∈ Ioo (0 : ℝ) D.q) :
    ∃ z, ∀ r : ℕ, 1 ≤ r → ∀ B : ℝ,
      ¬ QPotential r B
        (epsilonSuffixRemainder []
          (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) s h z)
          (terminalResidual β (cdf (D.μ : Measure ℝ)) s h z) 1) := by
  obtain ⟨z, hz⟩ := scalarData_exists_nonzero_second_jet D ht
  refine ⟨z, fun r hr B => ?_⟩
  have ht' : s + 4 * h ∈ Icc (0 : ℝ) 1 :=
    ⟨ht.1.le, ht.2.le.trans D.q_mem.2.le⟩
  have heq : epsilonSuffixRemainder []
      (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) s h z)
      (terminalResidual β (cdf (D.μ : Measure ℝ)) s h z) 1 =
        terminalResidual β (cdf (D.μ : Measure ℝ)) s h z := by
    funext x
    simpa only [one_mul] using epsilonSuffixRemainder_nil
      (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) s h z)
      (terminalResidual β (cdf (D.μ : Measure ℝ)) s h z) 1 x
  rw [heq]
  exact scalarData_terminalResidual_not_qPotential D ht' hz hr B

end SKBarriers2.Corner
