module
public import SKConstants.ParisiIntegralStep
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

public section
noncomputable section
namespace SKConstants
open MeasureTheory Filter Set
open scoped NNReal

theorem parisiGaussian_weighted_continuous (center : ℝ) (variance : ℝ≥0)
    (ell : ℝ) (f p a g : ℝ → ℝ) (M : ℝ)
    (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (hf : ∀ y, HasDerivAt f (p y) y)
    (ha : ∀ y, 0 ≤ a y ∧ a y ≤ 1 - p y ^ 2)
    (hgc : Continuous g) (hM : 0 ≤ M) (hg : ∀ y, |g y| ≤ M) :
    Continuous (fun x => ∫ z, Real.exp (ell * f (x + z)) * g (x + z)
      ∂ProbabilityTheory.gaussianReal center variance) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun y => (hf y).continuousAt
  obtain ⟨hpb, _⟩ := parisi_profile_bounds p a ha
  have hLip (x y : ℝ) : |f x - f y| ≤ |x - y| := by
    have hh := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (hf t).hasDerivWithinAt)
      (fun t _ => by simpa only [Real.norm_eq_abs] using hpb t)
      (mem_univ y) (mem_univ x)
    simpa only [Real.norm_eq_abs, one_mul] using hh
  apply continuous_iff_continuousAt.mpr
  intro x₀
  let μ := ProbabilityTheory.gaussianReal center variance
  let F : ℝ → ℝ → ℝ := fun x z => Real.exp (ell * f (x + z)) * g (x + z)
  let b : ℝ → ℝ := fun z => M * Real.exp 1 * Real.exp (ell * f (x₀ + z))
  have hb : Integrable b μ :=
    (parisiGaussian_exp_integrable center variance ell f p a x₀ hell hell1 hf ha).const_mul
      (M * Real.exp 1)
  have hFm (x : ℝ) : AEStronglyMeasurable (F x) μ := by
    apply Continuous.aestronglyMeasurable
    dsimp [F]
    fun_prop
  have hbound (x z : ℝ) (hx : x ∈ Metric.ball x₀ 1) : ‖F x z‖ ≤ b z := by
    have hdist : |x - x₀| < 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using hx
    have hh := hLip (x + z) (x₀ + z)
    have hsub : (x + z) - (x₀ + z) = x - x₀ := by ring
    rw [hsub] at hh
    have hfd : f (x + z) - f (x₀ + z) ≤ 1 := by
      linarith [le_abs_self (f (x + z) - f (x₀ + z))]
    have hm := mul_le_mul_of_nonneg_left hfd hell
    have harg : ell * f (x + z) ≤ 1 + ell * f (x₀ + z) := by nlinarith
    have hexp : Real.exp (ell * f (x + z)) ≤ Real.exp 1 * Real.exp (ell * f (x₀ + z)) := by
      simpa only [Real.exp_add] using Real.exp_le_exp.mpr harg
    dsimp [F, b]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (ell * f (x + z)) * M :=
        mul_le_mul_of_nonneg_left (hg _) (Real.exp_pos _).le
      _ ≤ (Real.exp 1 * Real.exp (ell * f (x₀ + z))) * M :=
        mul_le_mul_of_nonneg_right hexp hM
      _ = _ := by ring
  apply continuousAt_of_dominated (μ := μ) (F := F) (bound := b)
    (Eventually.of_forall hFm) ?_ hb ?_
  · filter_upwards [Metric.ball_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1)] with x hx
    exact Eventually.of_forall fun z => hbound x z hx
  · apply Eventually.of_forall
    intro z
    apply Continuous.continuousAt
    dsimp [F]
    fun_prop

theorem parisiGaussianStep_continuous_second_derivative (center : ℝ) (variance : ℝ≥0)
    (ell : ℝ) (f p a : ℝ → ℝ)
    (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (hf : ∀ y, HasDerivAt f (p y) y)
    (hp : ∀ y, HasDerivAt p (a y) y) (hac : Continuous a)
    (ha : ∀ y, 0 ≤ a y ∧ a y ≤ 1 - p y ^ 2) :
    Continuous (deriv (deriv (parisiIntegralStep
      (ProbabilityTheory.gaussianReal center variance) ell f))) := by
  let μ := ProbabilityTheory.gaussianReal center variance
  have hpc : Continuous p := continuous_iff_continuousAt.mpr fun y => (hp y).continuousAt
  have hZc : Continuous (parisiIntegralPartition μ ell f) :=
    continuous_iff_continuousAt.mpr fun x =>
      ((parisiIntegral_partition_derivatives μ ell f p a x hell hell1 hf hp hac ha
        (parisiGaussian_exp_integrable center variance ell f p a x hell hell1 hf ha)).1).continuousAt
  have hAc : Continuous (parisiIntegralNumerator μ ell f p) :=
    continuous_iff_continuousAt.mpr fun x =>
      ((parisiIntegral_partition_derivatives μ ell f p a x hell hell1 hf hp hac ha
        (parisiGaussian_exp_integrable center variance ell f p a x hell hell1 hf ha)).2).continuousAt
  have hZ (x : ℝ) : parisiIntegralPartition μ ell f x ≠ 0 :=
    (integral_exp_pos (parisiGaussian_exp_integrable center variance ell f p a x
      hell hell1 hf ha)).ne'
  have hBc : Continuous (parisiIntegralSecondNumerator μ ell f p a) := by
    apply parisiGaussian_weighted_continuous center variance ell f p a
      (fun y => a y + ell * p y ^ 2) 2 hell hell1 hf ha
      (hac.add (continuous_const.mul (hpc.pow 2))) (by norm_num)
    intro y
    have hnon : 0 ≤ a y + ell * p y ^ 2 := add_nonneg (ha y).1 (mul_nonneg hell (sq_nonneg _))
    rw [abs_of_nonneg hnon]
    have hp2 : p y ^ 2 ≤ 1 := by nlinarith [(ha y).1, (ha y).2]
    have hm := mul_le_mul_of_nonneg_left hp2 hell
    nlinarith [(ha y).2, sq_nonneg (p y)]
  have hcurvc : Continuous (parisiIntegralCurvature μ ell f p a) := by
    by_cases hzero : ell = 0
    · change Continuous (fun x => parisiIntegralCurvature μ ell f p a x)
      simp only [parisiIntegralCurvature, hzero, ite_true]
      obtain ⟨_, hab⟩ := parisi_profile_bounds p a ha
      have hh := parisiGaussian_weighted_continuous center variance 0 f p a a 1
        (by norm_num) (by norm_num) hf ha hac (by norm_num) hab
      simpa only [zero_mul, Real.exp_zero, one_mul] using hh
    · change Continuous (fun x => if ell = 0 then _ else _)
      simp only [hzero, ite_false]
      exact (hBc.div hZc hZ).sub (continuous_const.mul ((hAc.div hZc hZ).pow 2))
  have hfirst : deriv (parisiIntegralStep μ ell f) = parisiIntegralSlope μ ell f p := by
    funext x
    exact (parisiGaussianStep_derivatives center variance ell f p a x hell hell1 hf hp hac ha).1.deriv
  have hsecond : deriv (parisiIntegralSlope μ ell f p) = parisiIntegralCurvature μ ell f p a := by
    funext x
    exact (parisiGaussianStep_derivatives center variance ell f p a x hell hell1 hf hp hac ha).2.deriv
  rw [hfirst, hsecond]
  exact hcurvc

theorem parisi_logCosh_profile :
    (∀ x, HasDerivAt (fun y => Real.log (Real.cosh y)) (Real.tanh x) x) ∧
    (∀ x, HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x) ∧
    Continuous (fun x => 1 / Real.cosh x ^ 2) ∧
    (∀ x, 0 ≤ 1 / Real.cosh x ^ 2 ∧ 1 / Real.cosh x ^ 2 ≤ 1 - Real.tanh x ^ 2) := by
  have hid (x : ℝ) : 1 / Real.cosh x ^ 2 = 1 - Real.tanh x ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos x).ne']
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    simpa only [Real.tanh_eq_sinh_div_cosh] using
      (Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne'
  · intro x
    have hh := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
    convert hh using 1
    · funext y
      exact Real.tanh_eq_sinh_div_cosh y
    · field_simp [(Real.cosh_pos x).ne']
      nlinarith [Real.cosh_sq_sub_sinh_sq x]
  · exact continuous_const.div (Real.continuous_cosh.pow 2)
      (fun x => pow_ne_zero 2 (Real.cosh_pos x).ne')
  · intro x
    exact ⟨by positivity, (hid x).le⟩

theorem parisi_logTwoCosh_profile :
    (∀ x, HasDerivAt (fun y => Real.log (((2 : ℕ) : ℝ) * Real.cosh y)) (Real.tanh x) x) ∧
    (∀ x, HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x) ∧
    Continuous (fun x => 1 / Real.cosh x ^ 2) ∧
    (∀ x, 0 ≤ 1 / Real.cosh x ^ 2 ∧ 1 / Real.cosh x ^ 2 ≤ 1 - Real.tanh x ^ 2) := by
  obtain ⟨hf, hp, hc, ha⟩ := parisi_logCosh_profile
  refine ⟨?_, hp, hc, ha⟩
  intro x
  have hh := (hf x).const_add (Real.log ((2 : ℕ) : ℝ))
  convert hh using 1
  funext y
  rw [Real.log_mul (by norm_num : ((2 : ℕ) : ℝ) ≠ 0) (Real.cosh_pos y).ne']

@[expose] def parisiGaussianIterate (steps : List (ℝ × ℝ≥0 × ℝ)) : ℝ → ℝ :=
  List.rec (fun x => Real.log (((2 : ℕ) : ℝ) * Real.cosh x))
    (fun t _ T => parisiIntegralStep
      (ProbabilityTheory.gaussianReal t.1 t.2.1) t.2.2 T) steps

theorem parisiGaussianIterate_second_derivative_bound (steps : List (ℝ × ℝ≥0 × ℝ))
    (hsteps : ∀ t ∈ steps, 0 ≤ t.2.2 ∧ t.2.2 ≤ 1) :
    (∀ x, DifferentiableAt ℝ (parisiGaussianIterate steps) x ∧
      DifferentiableAt ℝ (deriv (parisiGaussianIterate steps)) x ∧
      0 ≤ deriv (deriv (parisiGaussianIterate steps)) x ∧
      deriv (deriv (parisiGaussianIterate steps)) x ≤
        1 - (deriv (parisiGaussianIterate steps) x) ^ 2) ∧
    Continuous (deriv (deriv (parisiGaussianIterate steps))) := by
  induction steps with
  | nil =>
      obtain ⟨hf, hp, hac, ha⟩ := parisi_logTwoCosh_profile
      have hfirst : deriv (fun x => Real.log (((2 : ℕ) : ℝ) * Real.cosh x)) = Real.tanh := by
        funext x
        exact (hf x).deriv
      have hsecond : deriv Real.tanh = fun x => 1 / Real.cosh x ^ 2 := by
        funext x
        exact (hp x).deriv
      dsimp only [parisiGaussianIterate]
      constructor
      · intro x
        refine ⟨(hf x).differentiableAt, ?_, ?_, ?_⟩
        · rw [hfirst]
          exact (hp x).differentiableAt
        · rw [hfirst, hsecond]
          exact (ha x).1
        · rw [hfirst, hsecond]
          exact (ha x).2
      · rw [hfirst, hsecond]
        exact hac
  | cons t ts ih =>
      have ht := hsteps t (by simp)
      obtain ⟨hprev, hcprev⟩ := ih (fun u hu => hsteps u (by simp [hu]))
      have hf : ∀ x, HasDerivAt (parisiGaussianIterate ts)
          (deriv (parisiGaussianIterate ts) x) x := fun x => (hprev x).1.hasDerivAt
      have hp : ∀ x, HasDerivAt (deriv (parisiGaussianIterate ts))
          (deriv (deriv (parisiGaussianIterate ts)) x) x := fun x => (hprev x).2.1.hasDerivAt
      have ha : ∀ x, 0 ≤ deriv (deriv (parisiGaussianIterate ts)) x ∧
          deriv (deriv (parisiGaussianIterate ts)) x ≤
            1 - (deriv (parisiGaussianIterate ts) x) ^ 2 := fun x => (hprev x).2.2
      exact ⟨parisiGaussianStep_second_derivative_bound t.1 t.2.1 t.2.2
          (parisiGaussianIterate ts) (deriv (parisiGaussianIterate ts))
          (deriv (deriv (parisiGaussianIterate ts))) ht.1 ht.2 hf hp hcprev ha,
        parisiGaussianStep_continuous_second_derivative t.1 t.2.1 t.2.2
          (parisiGaussianIterate ts) (deriv (parisiGaussianIterate ts))
          (deriv (deriv (parisiGaussianIterate ts))) ht.1 ht.2 hf hp hcprev ha⟩

end SKConstants
#print axioms SKConstants.parisiGaussianStep_continuous_second_derivative
#print axioms SKConstants.parisi_logCosh_profile
#print axioms SKConstants.parisiGaussianIterate_second_derivative_bound
