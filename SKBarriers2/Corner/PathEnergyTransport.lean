module

public import SKBarriers2.Corner.PathEnergyBias

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open Set Filter MeasureTheory ProbabilityTheory OAI.SK.Analytic
namespace SKBarriers2.Corner
open StepCalculus ParamChain
local notation "E" => (Fin 3 → ℝ)
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

set_option maxHeartbeats 800000 in
theorem chartAverage_energy_jets {F G : P × E → ℝ}
    (hF : ParamRegular F) (hG : ParamSmooth G)
    (q : (P →L[ℝ] ℝ) × (P →L[ℝ] E))
    {p : ℝ → P} {k B R K e a b c : ℝ} (hp : ContDiffAt ℝ 2 p k)
    (hK : 0 ≤ K)
    (hK₄ : |tiltedStabilityCoefficient 4 B| ≤ K)
    (hK₂ : |tiltedStabilityCoefficient 2 B| ≤ K)
    (hK₁ : firstTiltedTransportCoefficient B R ≤ K)
    (hKS : secondAverageTransportCoefficient (secondMovingAverageScale B R R)
      (defectNoiseMomentBound 1 B) (defectNoiseMomentBound 2 B) (defectNoiseMomentBound 3 B) ≤ K)
    (hf : QPotential 5 B (fun x => F (p k,x)))
    (hF₁ : QBoundedJets 3 R (fun x => deriv (fun t => F (p t,x)) k))
    (hF₂ : QBoundedJets 1 R (fun x => deriv (deriv (fun t => F (p t,x))) k))
    (hm : Real.exp (q.1 (p k)) ≤ 1)
    (hdm : |deriv (fun t => Real.exp (q.1 (p t))) k| ≤ 1)
    (hddm : |deriv (deriv (fun t => Real.exp (q.1 (p t)))) k| ≤ 1)
    (hv : ‖q.2 (p k)‖ ≤ 1)
    (hsmall : Real.exp (q.1 (p k))*(B*‖q.2 (p k)‖^2) ≤ 1/2)
    (henergy : ‖q.2 (p k)‖^2+‖deriv (fun t => q.2 (p t)) k‖^2+
      ‖deriv (deriv (fun t => q.2 (p t))) k‖^2 ≤ e) (he1 : e ≤ 1)
    (hg : QBoundedJets 4 a (fun x => G (p k,x)))
    (ha : QBoundedJets 2 b (fun x => deriv (fun t => G (p t,x)) k))
    (hq : QBoundedJets 0 c (fun x => deriv (deriv (fun t => G (p t,x))) k)) :
    let T := fun t x => tiltedAverage (Real.exp (q.1 (p t))) (q.2 (p t))
      (fun y => F (p t,y)) (fun y => G (p t,y)) x
    (∀ x, ContDiffAt ℝ 2 (fun t => T t x) k) ∧
    QBoundedJets 4 ((1+K*e)*a) (T k) ∧
    QBoundedJets 2 ((1+K*e)*b+K*e*a) (fun x => deriv (fun t => T t x) k) ∧
    QBoundedJets 0 ((1+K*e)*c+K*e*(a+b)) (fun x => deriv (deriv (fun t => T t x)) k) := by
  dsimp only
  let T := fun t x => tiltedAverage (Real.exp (q.1 (p t))) (q.2 (p t))
    (fun y => F (p t,y)) (fun y => G (p t,y)) x
  have hT := smooth_movingAverage hF hG q.1 q.2
  have hjet (x : E) := chartAverage_twoJet hF hG q.1 q.2 hp
    (hf.of_le (by norm_num : 4 ≤ 5)) hF₁
    (hg.of_le (by norm_num : 3 ≤ 4)) (ha.of_le (by norm_num : 1 ≤ 2)) hm x
  dsimp only at hjet
  have hm' : Real.exp (q.1 (p k)) ∈ Icc (0:ℝ) 1 := ⟨(Real.exp_pos _).le,hm⟩
  have he : 0 ≤ e := by
    nlinarith only [henergy,sq_nonneg ‖q.2 (p k)‖,
      sq_nonneg ‖deriv (fun t => q.2 (p t)) k‖,sq_nonneg ‖deriv (deriv (fun t => q.2 (p t))) k‖]
  have hvE : ‖q.2 (p k)‖^2 ≤ e := by
    nlinarith only [henergy,
      sq_nonneg ‖deriv (fun t => q.2 (p t)) k‖,sq_nonneg ‖deriv (deriv (fun t => q.2 (p t))) k‖]
  have hval : QBoundedJets 4 ((1+K*e)*a) (T k) := by
    apply (qBoundedJets_tiltedAverage 4 hf (by norm_num) le_rfl hg hm' _ hsmall).mono
    have H₁ := mul_le_mul_of_nonneg_right (le_abs_self (tiltedStabilityCoefficient 4 B))
      (mul_nonneg hg.nonneg (sq_nonneg ‖q.2 (p k)‖))
    have H₂ := mul_le_mul_of_nonneg_right hK₄ (mul_nonneg hg.nonneg (sq_nonneg ‖q.2 (p k)‖))
    have H₃ := mul_le_mul_of_nonneg_left hvE (mul_nonneg hK hg.nonneg)
    nlinarith only [H₁,H₂,H₃]
  have hfirst : QBoundedJets 2 ((1+K*e)*b+K*e*a) (fun x => deriv (fun t => T t x) k) := by
    have H₁ := qBoundedJets_firstTiltedAverageSource_energy hf hF₁ hg ha
      hF₁.nonneg le_rfl hm' hdm (q.2 (p k)) (deriv (fun t => q.2 (p t)) k) hv hsmall
      (show ‖q.2 (p k)‖^2+‖deriv (fun t => q.2 (p t)) k‖^2 ≤ e by
        nlinarith only [henergy,sq_nonneg ‖deriv (deriv (fun t => q.2 (p t))) k‖])
    have heq : (fun x => deriv (fun t => T t x) k) = _ := funext (fun x => (hjet x).2.1)
    rw [heq]
    apply H₁.mono
    have H₂ := mul_le_mul_of_nonneg_right hK₂ (mul_nonneg he ha.nonneg)
    have H₃ := mul_le_mul_of_nonneg_right hK₁ (mul_nonneg hg.nonneg he)
    nlinarith only [H₂,H₃]
  have ha0 := hg.nonneg
  have hb0 := ha.nonneg
  have hc0 := hq.nonneg
  have hsecond : QBoundedJets 0 ((1+K*e)*c+K*e*(a+b))
      (fun x => deriv (deriv (fun t => T t x)) k) := by
    refine ⟨by positivity,contDiff_zero.mpr (continuous_second_parameter_curve hT.1 hp),?_⟩
    intro n hn x
    have hn0 : n = 0 := by omega
    subst n
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs]
    rw [(hjet x).2.2]
    have H₁ := abs_secondMovingAverageSource_energy
      (hf.of_le (by norm_num : 3 ≤ 5)) (hF₁.of_le (by norm_num : 1 ≤ 3)) hF₂
      (hg.of_le (by norm_num : 2 ≤ 4)) ha hq hm' hdm hddm _ _ _ henergy he1 x
    have H₂ := mul_le_mul_of_nonneg_right hKS (mul_nonneg (add_nonneg hg.nonneg ha.nonneg) he)
    have H₃ := mul_nonneg (mul_nonneg hK he) hq.nonneg
    exact H₁.trans (by nlinarith only [H₂,H₃])
  exact ⟨fun x => (hT.1.contDiffAt (x := (p k,x))).comp (f := fun t : ℝ => (p t,x)) k (hp.prodMk (contDiffAt_const (c := x))),
    hval,hfirst,hsecond⟩

end SKBarriers2.Corner
