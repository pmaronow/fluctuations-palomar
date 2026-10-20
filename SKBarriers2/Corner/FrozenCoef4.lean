module

public import SKBarriers2.Corner.FrozenCoef3

@[expose] public section

noncomputable section
open scoped BigOperators Matrix ContDiff Topology NNReal
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def gaussianPolynomialWeight (n : ℕ) (x : ℝ) : ℝ := (1 + |x|) ^ n

theorem gaussianPolynomialWeight_integrable (n : ℕ) :
    Integrable (gaussianPolynomialWeight n) (gaussianReal 0 1) := by
  have hid : HasExpGrowth (fun x : ℝ => x) := HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)
  have ha : HasExpGrowth (fun x : ℝ => |x|) := by
    simpa only [Real.norm_eq_abs] using hid.norm (fun x => norm_nonneg x)
  exact (((HasExpGrowth.const 1).add ha).pow n).integrable_gaussianMeasure (by
    fun_prop)

theorem integrable_of_gaussianPolynomialWeight_bound {f : ℝ → ℝ} {B : ℝ} {n : ℕ}
    (hf : AEStronglyMeasurable f (gaussianReal 0 1))
    (hb : ∀ x, |f x| ≤ B * gaussianPolynomialWeight n x) :
    Integrable f (gaussianReal 0 1) :=
  ((gaussianPolynomialWeight_integrable n).const_mul B).mono' hf
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x))

theorem gaussian_integral_two_derivatives
    {F F₁ F₂ : ℝ → ℝ → ℝ} {U : Set ℝ} {k B : ℝ} {n : ℕ}
    (hU : U ∈ 𝓝 k)
    (hm : ∀ x ∈ U, AEStronglyMeasurable (F x) (gaussianReal 0 1) ∧
      AEStronglyMeasurable (F₁ x) (gaussianReal 0 1) ∧
      AEStronglyMeasurable (F₂ x) (gaussianReal 0 1))
    (hd : ∀ g : ℝ, ∀ x ∈ U, HasDerivAt (fun y => F y g) (F₁ x g) x ∧
      HasDerivAt (fun y => F₁ y g) (F₂ x g) x)
    (hb : ∀ x ∈ U, ∀ g : ℝ, |F x g| ≤ B * gaussianPolynomialWeight n g ∧
      |F₁ x g| ≤ B * gaussianPolynomialWeight n g ∧
      |F₂ x g| ≤ B * gaussianPolynomialWeight n g) :
    HasDerivAt (fun x => ∫ g, F x g ∂gaussianReal 0 1) (∫ g, F₁ k g ∂gaussianReal 0 1) k ∧
    HasDerivAt (fun x => ∫ g, F₁ x g ∂gaussianReal 0 1) (∫ g, F₂ k g ∂gaussianReal 0 1) k := by
  have hk : k ∈ U := mem_of_mem_nhds hU
  have hi₀ := integrable_of_gaussianPolynomialWeight_bound (hm k hk).1 (fun g => (hb k hk g).1)
  have hi₁ := integrable_of_gaussianPolynomialWeight_bound (hm k hk).2.1 (fun g => (hb k hk g).2.1)
  have hdom := (gaussianPolynomialWeight_integrable n).const_mul B
  have h₀ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hU
    (Filter.mem_of_superset hU (fun x hx => (hm x hx).1)) hi₀ (hm k hk).2.1
    (ae_of_all _ (fun g x hx => by simpa only [Real.norm_eq_abs] using (hb x hx g).2.1))
    hdom (ae_of_all _ (fun g x hx => (hd g x hx).1))
  have h₁ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hU
    (Filter.mem_of_superset hU (fun x hx => (hm x hx).2.1)) hi₁ (hm k hk).2.2
    (ae_of_all _ (fun g x hx => by simpa only [Real.norm_eq_abs] using (hb x hx g).2.2))
    hdom (ae_of_all _ (fun g x hx => (hd g x hx).2))
  exact ⟨h₀.2, h₁.2⟩

theorem iteratedDeriv_iteratedDeriv_eq (f : ℝ → ℝ) (n j : ℕ) :
    iteratedDeriv n (iteratedDeriv j f) = iteratedDeriv (n + j) f := by
  simp only [iteratedDeriv_eq_iterate, Function.iterate_add_apply]

theorem contDiff_deriv_infty {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (deriv f) := by
  change ContDiff ℝ ∞ (fun x => fderiv ℝ f x 1)
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

theorem scalarTaylorPolynomial_succ (f : ℝ → ℝ) (n : ℕ) (z y : ℝ) :
    scalarTaylorPolynomial f (n + 1) z y = scalarTaylorPolynomial f n z y +
      iteratedDeriv (n + 1) f z * (y - z) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  exact Finset.sum_range_succ _ (n + 1)

theorem scalarTaylorPolynomial_hasDerivAt (f : ℝ → ℝ) (n : ℕ) (z y : ℝ) :
    HasDerivAt (scalarTaylorPolynomial f (n + 1) z)
      (scalarTaylorPolynomial (deriv f) n z y) y := by
  induction n with
  | zero =>
    have H := (((hasDerivAt_id y).sub_const z).const_mul (deriv f z)).const_add (f z)
    convert H using 1
    · funext x
      simp [scalarTaylorPolynomial, Finset.sum_range_succ]
    · simp [scalarTaylorPolynomial]
  | succ n ih =>
    have hterm := ((((hasDerivAt_id y).sub_const z).pow (n + 2)).const_mul
      (iteratedDeriv (n + 2) f z)).div_const ((n + 2).factorial : ℝ)
    have H := ih.add hterm
    convert H using 1
    · funext x
      exact scalarTaylorPolynomial_succ f (n + 1) z x
    · have hn : n + 2 - 1 = n + 1 := by omega
      simp only [id_eq, hn, mul_one]
      rw [scalarTaylorPolynomial_succ, ← iteratedDeriv_succ']
      congr 1
      simp only [Nat.factorial_succ, Nat.cast_mul]
      field_simp

def scalarSixthTail (f : ℝ → ℝ) (z y : ℝ) : ℝ :=
  f y - scalarTaylorPolynomial f 6 z y

def scalarSixthTailFirst (f : ℝ → ℝ) (z y : ℝ) : ℝ :=
  deriv f y - scalarTaylorPolynomial (deriv f) 5 z y

def scalarSixthTailSecond (f : ℝ → ℝ) (z y : ℝ) : ℝ :=
  iteratedDeriv 2 f y - scalarTaylorPolynomial (iteratedDeriv 2 f) 4 z y

theorem scalarSixthTail_derivatives {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (z y : ℝ) :
    HasDerivAt (scalarSixthTail f z) (scalarSixthTailFirst f z y) y ∧
    HasDerivAt (scalarSixthTailFirst f z) (scalarSixthTailSecond f z y) y := by
  have hf₁ : ContDiff ℝ ∞ (deriv f) := contDiff_deriv_infty hf
  refine ⟨(hf.differentiable (by simp) y).hasDerivAt.sub (scalarTaylorPolynomial_hasDerivAt f 5 z y), ?_⟩
  have H := (hf₁.differentiable (by simp) y).hasDerivAt.sub
    (scalarTaylorPolynomial_hasDerivAt (deriv f) 4 z y)
  change HasDerivAt (fun x => deriv f x - scalarTaylorPolynomial (deriv f) 5 z x)
    (iteratedDeriv 2 f y - scalarTaylorPolynomial (iteratedDeriv 2 f) 4 z y) y
  have he : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [he]
  exact H

theorem scalarSixthTail_bounds {f : ℝ → ℝ} {B : ℝ}
    (hf : ContDiff ℝ ∞ f) (hb : ∀ y, |iteratedDeriv 7 f y| ≤ B) (z y : ℝ) :
    |scalarSixthTail f z y| ≤ B * |y - z| ^ 7 / 5040 ∧
    |scalarSixthTailFirst f z y| ≤ B * |y - z| ^ 6 / 720 ∧
    |scalarSixthTailSecond f z y| ≤ B * |y - z| ^ 5 / 120 := by
  have h₀ := scalarTaylorPolynomial_remainder_le (n := 6) (hf.of_le (by simp)) hb z y
  have hf₁ : ContDiff ℝ ∞ (deriv f) := contDiff_deriv_infty hf
  have hf₂ : ContDiff ℝ ∞ (iteratedDeriv 2 f) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using contDiff_deriv_infty hf₁
  have h₁ := scalarTaylorPolynomial_remainder_le (n := 5) (hf₁.of_le (by simp))
    (fun y => by simpa only [← iteratedDeriv_succ'] using hb y) z y
  have h₂ := scalarTaylorPolynomial_remainder_le (n := 4) (hf₂.of_le (by simp))
    (fun y => by simpa only [iteratedDeriv_iteratedDeriv_eq] using hb y) z y
  norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at h₀ h₁ h₂
  exact ⟨h₀, h₁, h₂⟩

def gaussianAffineExpectation (R : ℝ → ℝ) (m σ : ℝ → ℝ) (k : ℝ) : ℝ :=
  ∫ g, R (m k + σ k * g) ∂gaussianReal 0 1

def gaussianAffineFirst (R₁ : ℝ → ℝ) (m σ m₁ σ₁ : ℝ → ℝ) (k : ℝ) : ℝ :=
  ∫ g, R₁ (m k + σ k * g) * (m₁ k + σ₁ k * g) ∂gaussianReal 0 1

def gaussianAffineSecond (R₁ R₂ : ℝ → ℝ) (m σ m₁ σ₁ m₂ σ₂ : ℝ → ℝ) (k : ℝ) : ℝ :=
  ∫ g, R₂ (m k + σ k * g) * (m₁ k + σ₁ k * g) ^ 2 +
    R₁ (m k + σ k * g) * (m₂ k + σ₂ k * g) ∂gaussianReal 0 1

private theorem affine_abs_bound {M ρ a b : ℝ} (ha : |a| ≤ M * ρ) (hb : |b| ≤ M * ρ) (g : ℝ) :
    |a + b * g| ≤ M * ρ * (1 + |g|) := by
  calc
    _ ≤ |a| + |b * g| := abs_add_le _ _
    _ = |a| + |b| * |g| := by rw [abs_mul]
    _ ≤ M * ρ + (M * ρ) * |g| := add_le_add ha (mul_le_mul_of_nonneg_right hb (abs_nonneg g))
    _ = _ := by ring

theorem affine_remainder_integrand_bounds {R R₁ R₂ : ℝ → ℝ} {n : ℕ} {B M ρ z : ℝ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hR : ∀ y, |R y| ≤ B * |y - z| ^ (n + 2) ∧
      |R₁ y| ≤ B * |y - z| ^ (n + 1) ∧ |R₂ y| ≤ B * |y - z| ^ n)
    {m σ m₁ σ₁ m₂ σ₂ : ℝ}
    (hm : |m - z| ≤ M * ρ) (hσ : |σ| ≤ M * ρ)
    (hm₁ : |m₁| ≤ M * ρ) (hσ₁ : |σ₁| ≤ M * ρ)
    (hm₂ : |m₂| ≤ M * ρ) (hσ₂ : |σ₂| ≤ M * ρ) (g : ℝ) :
    |R (m + σ * g)| ≤ (2 * B * M ^ (n + 2) * ρ ^ (n + 2)) * gaussianPolynomialWeight (n + 2) g ∧
    |R₁ (m + σ * g) * (m₁ + σ₁ * g)| ≤
      (2 * B * M ^ (n + 2) * ρ ^ (n + 2)) * gaussianPolynomialWeight (n + 2) g ∧
    |R₂ (m + σ * g) * (m₁ + σ₁ * g) ^ 2 + R₁ (m + σ * g) * (m₂ + σ₂ * g)| ≤
      (2 * B * M ^ (n + 2) * ρ ^ (n + 2)) * gaussianPolynomialWeight (n + 2) g := by
  let T := M * ρ * (1 + |g|)
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hx : |m + σ * g - z| ≤ T := by
    simpa only [T, sub_add_eq_add_sub, add_sub_assoc] using affine_abs_bound hm hσ g
  have hx₁ : |m₁ + σ₁ * g| ≤ T := affine_abs_bound hm₁ hσ₁ g
  have hx₂ : |m₂ + σ₂ * g| ≤ T := affine_abs_bound hm₂ hσ₂ g
  have hr₀ : |R (m + σ * g)| ≤ B * T ^ (n + 2) :=
    (hR _).1.trans (by gcongr)
  have hr₁ : |R₁ (m + σ * g)| ≤ B * T ^ (n + 1) :=
    (hR _).2.1.trans (by gcongr)
  have hr₂ : |R₂ (m + σ * g)| ≤ B * T ^ n :=
    (hR _).2.2.trans (by gcongr)
  have hs : 2 * B * T ^ (n + 2) =
      (2 * B * M ^ (n + 2) * ρ ^ (n + 2)) * gaussianPolynomialWeight (n + 2) g := by
    dsimp only [T, gaussianPolynomialWeight]
    rw [mul_pow, mul_pow]
    ring
  rw [← hs]
  refine ⟨hr₀.trans (by nlinarith [mul_nonneg hB (pow_nonneg hT (n + 2))]), ?_, ?_⟩
  · rw [abs_mul]
    calc
      _ ≤ (B * T ^ (n + 1)) * T := mul_le_mul hr₁ hx₁ (abs_nonneg _) (by positivity)
      _ = B * T ^ (n + 2) := by simp only [pow_succ]; ring
      _ ≤ 2 * B * T ^ (n + 2) := by nlinarith [mul_nonneg hB (pow_nonneg hT (n + 2))]
  · calc
      _ ≤ |R₂ (m + σ * g)| * |m₁ + σ₁ * g| ^ 2 +
          |R₁ (m + σ * g)| * |m₂ + σ₂ * g| := by
        exact (abs_add_le _ _).trans_eq (by rw [abs_mul, abs_mul, abs_pow])
      _ ≤ (B * T ^ n) * T ^ 2 + (B * T ^ (n + 1)) * T := by gcongr
      _ = 2 * B * T ^ (n + 2) := by simp only [pow_succ]; ring

theorem gaussian_integral_abs_le_polynomial {F : ℝ → ℝ} {B : ℝ} {n : ℕ}
    (hb : ∀ g, |F g| ≤ B * gaussianPolynomialWeight n g) :
    |∫ g, F g ∂gaussianReal 0 1| ≤ B * ∫ g, gaussianPolynomialWeight n g ∂gaussianReal 0 1 := by
  have H := norm_integral_le_of_norm_le (f := F) ((gaussianPolynomialWeight_integrable n).const_mul B)
    (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hb g))
  simpa only [Real.norm_eq_abs, integral_const_mul] using H

theorem gaussian_affine_remainder_control {R R₁ R₂ : ℝ → ℝ} {n : ℕ} {B M ρ z : ℝ}
    (hc : Continuous R ∧ Continuous R₁ ∧ Continuous R₂)
    (hdR : ∀ y, HasDerivAt R (R₁ y) y ∧ HasDerivAt R₁ (R₂ y) y)
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hR : ∀ y, |R y| ≤ B * |y - z| ^ (n + 2) ∧
      |R₁ y| ≤ B * |y - z| ^ (n + 1) ∧ |R₂ y| ≤ B * |y - z| ^ n)
    {m σ m₁ σ₁ m₂ σ₂ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ k ∈ U, HasDerivAt m (m₁ k) k ∧ HasDerivAt m₁ (m₂ k) k ∧
      HasDerivAt σ (σ₁ k) k ∧ HasDerivAt σ₁ (σ₂ k) k)
    (hp : ∀ k ∈ U, |m k - z| ≤ M * ρ ∧ |σ k| ≤ M * ρ ∧
      |m₁ k| ≤ M * ρ ∧ |σ₁ k| ≤ M * ρ ∧ |m₂ k| ≤ M * ρ ∧ |σ₂ k| ≤ M * ρ) :
    ∀ k ∈ U,
      HasDerivAt (gaussianAffineExpectation R m σ) (gaussianAffineFirst R₁ m σ m₁ σ₁ k) k ∧
      HasDerivAt (gaussianAffineFirst R₁ m σ m₁ σ₁) (gaussianAffineSecond R₁ R₂ m σ m₁ σ₁ m₂ σ₂ k) k ∧
      |gaussianAffineExpectation R m σ k| ≤
        (2 * B * M ^ (n + 2) * ρ ^ (n + 2)) * ∫ g, gaussianPolynomialWeight (n + 2) g ∂gaussianReal 0 1 ∧
      |gaussianAffineFirst R₁ m σ m₁ σ₁ k| ≤
        (2 * B * M ^ (n + 2) * ρ ^ (n + 2)) * ∫ g, gaussianPolynomialWeight (n + 2) g ∂gaussianReal 0 1 ∧
      |gaussianAffineSecond R₁ R₂ m σ m₁ σ₁ m₂ σ₂ k| ≤
        (2 * B * M ^ (n + 2) * ρ ^ (n + 2)) * ∫ g, gaussianPolynomialWeight (n + 2) g ∂gaussianReal 0 1 := by
  let F := fun k g => R (m k + σ k * g)
  let F₁ := fun k g => R₁ (m k + σ k * g) * (m₁ k + σ₁ k * g)
  let F₂ := fun k g => R₂ (m k + σ k * g) * (m₁ k + σ₁ k * g) ^ 2 + R₁ (m k + σ k * g) * (m₂ k + σ₂ k * g)
  have hb (k : ℝ) (hk : k ∈ U) : ∀ g : ℝ,
      |F k g| ≤ (2 * B * M ^ (n + 2) * ρ ^ (n + 2)) * gaussianPolynomialWeight (n + 2) g ∧
      |F₁ k g| ≤ (2 * B * M ^ (n + 2) * ρ ^ (n + 2)) * gaussianPolynomialWeight (n + 2) g ∧
      |F₂ k g| ≤ (2 * B * M ^ (n + 2) * ρ ^ (n + 2)) * gaussianPolynomialWeight (n + 2) g := by
    rcases hp k hk with ⟨hm, hσ, hm₁, hσ₁, hm₂, hσ₂⟩
    exact affine_remainder_integrand_bounds hB hM hρ hR hm hσ hm₁ hσ₁ hm₂ hσ₂
  have hc₀ := hc.1
  have hc₁ := hc.2.1
  have hc₂ := hc.2.2
  intro k hk
  have H := gaussian_integral_two_derivatives (hU.mem_nhds hk)
    (F := F) (F₁ := F₁) (F₂ := F₂)
    (fun x _ => by
      have hc₀ : Continuous (F x) := by dsimp only [F]; fun_prop
      have hc₁ : Continuous (F₁ x) := by dsimp only [F₁]; fun_prop
      have hc₂ : Continuous (F₂ x) := by dsimp only [F₂]; fun_prop
      exact ⟨hc₀.aestronglyMeasurable, hc₁.aestronglyMeasurable, hc₂.aestronglyMeasurable⟩)
    (fun g x hx => by
      rcases hd x hx with ⟨hm, hm₁, hσ, hσ₁⟩
      have hdX := hm.add (hσ.mul_const g)
      have hdX₁ := hm₁.add (hσ₁.mul_const g)
      refine ⟨(hdR _).1.comp x hdX, ?_⟩
      convert ((hdR _).2.comp x hdX).mul hdX₁ using 1
      · rfl
      · dsimp only [F₂, Function.comp_def, Pi.add_apply]
        ring)
    hb
  exact ⟨H.1, H.2, gaussian_integral_abs_le_polynomial (fun g => (hb k hk g).1),
    gaussian_integral_abs_le_polynomial (fun g => (hb k hk g).2.1),
    gaussian_integral_abs_le_polynomial (fun g => (hb k hk g).2.2)⟩

theorem scalarTaylorPolynomial_contDiff (f : ℝ → ℝ) (n : ℕ) (z : ℝ) :
    ContDiff ℝ ∞ (scalarTaylorPolynomial f n z) := by
  unfold scalarTaylorPolynomial
  fun_prop

theorem scalarSixthTail_gaussian_control {f : ℝ → ℝ} {B M ρ z : ℝ}
    (hf : ContDiff ℝ ∞ f) (hB : 0 ≤ B) (hb : ∀ y, |iteratedDeriv 7 f y| ≤ B)
    (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    {m σ m₁ σ₁ m₂ σ₂ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ k ∈ U, HasDerivAt m (m₁ k) k ∧ HasDerivAt m₁ (m₂ k) k ∧
      HasDerivAt σ (σ₁ k) k ∧ HasDerivAt σ₁ (σ₂ k) k)
    (hp : ∀ k ∈ U, |m k - z| ≤ M * ρ ∧ |σ k| ≤ M * ρ ∧
      |m₁ k| ≤ M * ρ ∧ |σ₁ k| ≤ M * ρ ∧ |m₂ k| ≤ M * ρ ∧ |σ₂ k| ≤ M * ρ) :
    ∀ k ∈ U,
      HasDerivAt (gaussianAffineExpectation (scalarSixthTail f z) m σ)
        (gaussianAffineFirst (scalarSixthTailFirst f z) m σ m₁ σ₁ k) k ∧
      HasDerivAt (gaussianAffineFirst (scalarSixthTailFirst f z) m σ m₁ σ₁)
        (gaussianAffineSecond (scalarSixthTailFirst f z) (scalarSixthTailSecond f z) m σ m₁ σ₁ m₂ σ₂ k) k ∧
      |gaussianAffineExpectation (scalarSixthTail f z) m σ k| ≤
        (2 * B * M ^ 7 * ρ ^ 7) * ∫ g, gaussianPolynomialWeight 7 g ∂gaussianReal 0 1 ∧
      |gaussianAffineFirst (scalarSixthTailFirst f z) m σ m₁ σ₁ k| ≤
        (2 * B * M ^ 7 * ρ ^ 7) * ∫ g, gaussianPolynomialWeight 7 g ∂gaussianReal 0 1 ∧
      |gaussianAffineSecond (scalarSixthTailFirst f z) (scalarSixthTailSecond f z) m σ m₁ σ₁ m₂ σ₂ k| ≤
        (2 * B * M ^ 7 * ρ ^ 7) * ∫ g, gaussianPolynomialWeight 7 g ∂gaussianReal 0 1 := by
  have hf₁ := contDiff_deriv_infty hf
  have hf₂ : ContDiff ℝ ∞ (iteratedDeriv 2 f) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using contDiff_deriv_infty hf₁
  have hc₀ : Continuous (scalarSixthTail f z) := (hf.sub (scalarTaylorPolynomial_contDiff f 6 z)).continuous
  have hc₁ : Continuous (scalarSixthTailFirst f z) := (hf₁.sub (scalarTaylorPolynomial_contDiff (deriv f) 5 z)).continuous
  have hc₂ : Continuous (scalarSixthTailSecond f z) := (hf₂.sub (scalarTaylorPolynomial_contDiff (iteratedDeriv 2 f) 4 z)).continuous
  have hR (y : ℝ) : |scalarSixthTail f z y| ≤ B * |y - z| ^ (5 + 2) ∧
      |scalarSixthTailFirst f z y| ≤ B * |y - z| ^ (5 + 1) ∧
      |scalarSixthTailSecond f z y| ≤ B * |y - z| ^ 5 := by
    rcases scalarSixthTail_bounds hf hb z y with ⟨H₀, H₁, H₂⟩
    refine ⟨H₀.trans ?_, H₁.trans ?_, H₂.trans ?_⟩
    · nlinarith [mul_nonneg hB (pow_nonneg (abs_nonneg (y - z)) 7)]
    · nlinarith [mul_nonneg hB (pow_nonneg (abs_nonneg (y - z)) 6)]
    · nlinarith [mul_nonneg hB (pow_nonneg (abs_nonneg (y - z)) 5)]
  exact gaussian_affine_remainder_control ⟨hc₀, hc₁, hc₂⟩ (scalarSixthTail_derivatives hf z)
    hB hM hρ hR hU hd hp

def frozenNormalizedVariance (i : Fin 3) (x : ℝ × ℝ) : ℝ :=
  4 + x.1 * frozenCovarianceQuadratic x.2 i i + x.1 ^ 2 * frozenCovarianceRemainder x.1 x.2 i i

def frozenNormalizedScale (i : Fin 3) (x : ℝ × ℝ) : ℝ := Real.sqrt (frozenNormalizedVariance i x)

theorem frozenCovarianceQuadratic_entry_contDiff (i j : Fin 3) :
    ContDiff ℝ ∞ (fun x : ℝ × ℝ => frozenCovarianceQuadratic x.2 i j) := by
  have hC := frozenRiccatiCovariance_entry_contDiff
  change ContDiff ℝ ∞ (fun x : ℝ × ℝ =>
    3 * (∑ m, frozenRiccatiCovariance 0 x.2 i m * frozenRiccatiCovariance 0 x.2 m j) -
      (∑ m, frozenRiccatiCovariance 1 x.2 i m * frozenRiccatiCovariance 1 x.2 m j) -
      (∑ m, frozenRiccatiCovariance 2 x.2 i m * frozenRiccatiCovariance 2 x.2 m j))
  fun_prop

theorem frozenNormalizedVariance_contDiffOn (i : Fin 3) :
    ContDiffOn ℝ ∞ (frozenNormalizedVariance i) frozenResolventDomain := by
  exact (contDiffOn_const.add (contDiff_fst.mul (frozenCovarianceQuadratic_entry_contDiff i i)).contDiffOn).add
    ((contDiff_fst.pow 2).contDiffOn.mul (frozenCovarianceRemainder_entry_contDiffOn i i))

def frozenScaleDomain : Set (ℝ × ℝ) :=
  {x | x ∈ frozenResolventDomain ∧ ∀ i : Fin 3, 0 < frozenNormalizedVariance i x}

theorem frozenScaleDomain_isOpen : IsOpen frozenScaleDomain := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hdom := frozenResolventDomain_isOpen.mem_nhds hx.1
  have hpos (i : Fin 3) : ∀ᶠ y in 𝓝 x, 0 < frozenNormalizedVariance i y :=
    ((frozenNormalizedVariance_contDiffOn i).contDiffAt hdom).continuousAt.eventually (Ioi_mem_nhds (hx.2 i))
  filter_upwards [hdom, eventually_all.mpr hpos] with y hy hp
  exact ⟨hy, hp⟩

theorem frozenNormalizedScale_contDiffOn (i : Fin 3) :
    ContDiffOn ℝ ∞ (frozenNormalizedScale i) frozenScaleDomain :=
  ((frozenNormalizedVariance_contDiffOn i).mono (fun _ hx => hx.1)).sqrt
    (fun _ hx => ne_of_gt (hx.2 i))

theorem frozenScaleDomain_contains_rectangle :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      (Icc (-δ) δ ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2)) ⊆ frozenScaleDomain := by
  obtain ⟨R, δR, hR, hδR, _, hbR⟩ := frozenCovarianceRemainder_uniform_bounds
  obtain ⟨δD, hδD, _, hD⟩ := frozenResolventDomain_contains_rectangle
  choose Q hQ hbQ using fun i : Fin 3 => smooth_uniform_vertical_bounds (frozenCovarianceQuadratic_entry_contDiff i i)
  let B : ℝ := 1 + R + ∑ i : Fin 3, Q i
  have hsum : 0 ≤ ∑ i : Fin 3, Q i := Finset.sum_nonneg (fun i _ => (hQ i).le)
  have hB : 0 < B := by dsimp only [B]; linarith
  have hRB : R ≤ B := by dsimp only [B]; linarith
  have hQB (i : Fin 3) : Q i ≤ B := by
    have H := Finset.single_le_sum (f := Q) (fun j _ => (hQ j).le) (Finset.mem_univ i)
    dsimp only [B]
    linarith
  let δ := min δR (min δD (min 1 (1 / (4 * B))))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδR' : δ ≤ δR := min_le_left _ _
  have hδD' : δ ≤ δD := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₁ : δ ≤ 1 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδB : δ ≤ 1 / (4 * B) := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  refine ⟨δ, hδ, hδ₁, ?_⟩
  rintro ⟨t, k⟩ ⟨ht, hk⟩
  have htδ : |t| ≤ δ := abs_le.mpr ht
  have ht₁ : t ∈ Icc (-1 : ℝ) 1 := abs_le.mp (htδ.trans hδ₁)
  have htB : |t| * B ≤ 1 / 4 := by
    have H := (le_div_iff₀ (by positivity : 0 < 4 * B)).mp (htδ.trans hδB)
    nlinarith
  refine ⟨hD ⟨abs_le.mp (htδ.trans hδD'), hk⟩, ?_⟩
  intro i
  have hq : |frozenCovarianceQuadratic k i i| ≤ B := ((hbQ i t ht₁ k hk).1).trans (hQB i)
  have hr : |frozenCovarianceRemainder t k i i| ≤ B :=
    ((hbR i i t (htδ.trans hδR') k (abs_le.mpr hk)).1).trans hRB
  have h₁ : |t * frozenCovarianceQuadratic k i i| ≤ 1 / 4 := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hq (abs_nonneg t)).trans htB
  have h₂ : |t ^ 2 * frozenCovarianceRemainder t k i i| ≤ 1 / 4 := by
    rw [abs_mul, abs_pow]
    calc
      _ ≤ |t| ^ 2 * B := mul_le_mul_of_nonneg_left hr (sq_nonneg _)
      _ ≤ |t| * B := by nlinarith [mul_nonneg hB.le (mul_nonneg (abs_nonneg t) (sub_nonneg.mpr (htδ.trans hδ₁)))]
      _ ≤ 1 / 4 := htB
  dsimp only [frozenNormalizedVariance]
  linarith [(abs_le.mp h₁).1, (abs_le.mp h₂).1]

theorem frozenNormalizedScale_uniform_bounds :
    ∃ S δ : ℝ, 0 < S ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ i : Fin 3, ∀ t : ℝ, |t| ≤ δ → ∀ k : ℝ, |k| ≤ 1 / 2 →
        (t, k) ∈ frozenScaleDomain ∧
        |frozenNormalizedScale i (t, k)| ≤ S ∧
        |verticalDerivative (frozenNormalizedScale i) (t, k)| ≤ S ∧
        |verticalDerivative (verticalDerivative (frozenNormalizedScale i)) (t, k)| ≤ S ∧
        HasDerivAt (fun k => frozenNormalizedScale i (t, k))
          (verticalDerivative (frozenNormalizedScale i) (t, k)) k ∧
        HasDerivAt (fun k => verticalDerivative (frozenNormalizedScale i) (t, k))
          (verticalDerivative (verticalDerivative (frozenNormalizedScale i)) (t, k)) k := by
  obtain ⟨δ, hδ, hδ₁, hK⟩ := frozenScaleDomain_contains_rectangle
  choose S hS hb using fun i : Fin 3 => smoothOn_uniform_vertical_bounds
    frozenScaleDomain_isOpen (frozenNormalizedScale_contDiffOn i) δ hK
  let M : ℝ := 1 + ∑ i : Fin 3, S i
  have hsum : 0 ≤ ∑ i : Fin 3, S i := Finset.sum_nonneg (fun i _ => (hS i).le)
  have hM : 0 < M := by dsimp only [M]; linarith
  have hSM (i : Fin 3) : S i ≤ M := by
    have H := Finset.single_le_sum (f := S) (fun j _ => (hS j).le) (Finset.mem_univ i)
    dsimp only [M]
    linarith
  refine ⟨M, δ, hM, hδ, hδ₁, ?_⟩
  intro i t ht k hk
  have hx := hK (show (t, k) ∈ Icc (-δ) δ ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2) from ⟨abs_le.mp ht, abs_le.mp hk⟩)
  have H := hb i t (abs_le.mp ht) k (abs_le.mp hk)
  have hF := frozenNormalizedScale_contDiffOn i
  have hF₁ : ContDiffOn ℝ ∞ (verticalDerivative (frozenNormalizedScale i)) frozenScaleDomain :=
    (hF.fderiv_of_isOpen frozenScaleDomain_isOpen (by simp)).clm_apply contDiffOn_const
  exact ⟨hx, H.1.trans (hSM i), H.2.1.trans (hSM i), H.2.2.trans (hSM i),
    verticalDerivative_hasDerivAt_on frozenScaleDomain_isOpen hF t k hx,
    verticalDerivative_hasDerivAt_on frozenScaleDomain_isOpen hF₁ t k hx⟩

def frozenGaussianMean (β a u χ h z : ℝ) : ℝ :=
  z + 4 * a * β ^ 2 * h * u / (1 - 4 * a * β ^ 2 * χ * h)

def frozenGaussianScale (β a χ h : ℝ) (i : Fin 3) (k : ℝ) : ℝ :=
  β * Real.sqrt h * frozenNormalizedScale i (a * β ^ 2 * χ * h, k)

def frozenGaussianScaleFirst (β a χ h : ℝ) (i : Fin 3) (k : ℝ) : ℝ :=
  β * Real.sqrt h * verticalDerivative (frozenNormalizedScale i) (a * β ^ 2 * χ * h, k)

def frozenGaussianScaleSecond (β a χ h : ℝ) (i : Fin 3) (k : ℝ) : ℝ :=
  β * Real.sqrt h * verticalDerivative (verticalDerivative (frozenNormalizedScale i)) (a * β ^ 2 * χ * h, k)

theorem frozenGaussianParameter_uniform_control (β B : ℝ) (hB : 0 < B) :
    ∃ M h₀ : ℝ, 0 < M ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ a u χ h z : ℝ,
      a ∈ Ioc (0 : ℝ) 1 → |u| ≤ B → |χ| ≤ B → 0 ≤ h → h ≤ h₀ →
      ∀ i : Fin 3, ∀ k : ℝ, |k| ≤ 1 / 2 →
        (a * β ^ 2 * χ * h, k) ∈ frozenScaleDomain ∧
        |frozenGaussianMean β a u χ h z - z| ≤ M * Real.sqrt h ∧
        |frozenGaussianScale β a χ h i k| ≤ M * Real.sqrt h ∧
        |frozenGaussianScaleFirst β a χ h i k| ≤ M * Real.sqrt h ∧
        |frozenGaussianScaleSecond β a χ h i k| ≤ M * Real.sqrt h ∧
        HasDerivAt (frozenGaussianScale β a χ h i) (frozenGaussianScaleFirst β a χ h i k) k ∧
        HasDerivAt (frozenGaussianScaleFirst β a χ h i) (frozenGaussianScaleSecond β a χ h i k) k := by
  obtain ⟨S, δ, hS, hδ, _, hScale⟩ := frozenNormalizedScale_uniform_bounds
  let T := (β ^ 2 + 1) * (B + 1)
  have hT : 0 < T := by dsimp only [T]; positivity
  let η := min 1 (min (δ / T) (1 / (8 * T)))
  have hη : 0 < η := by dsimp only [η]; positivity
  let M := 1 + 8 * β ^ 2 * B + |β| * S
  have hM : 0 < M := by dsimp only [M]; positivity
  refine ⟨M, η, hM, hη, min_le_left _ _, ?_⟩
  intro a u χ h z ha hu hχ hh hhη i k hk
  have hha : |a| ≤ 1 := by rw [abs_of_pos ha.1]; exact ha.2
  have hh₁ : h ≤ 1 := hhη.trans (min_le_left _ _)
  have ht : |a * β ^ 2 * χ * h| ≤ T * h := by
    dsimp only [T]
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg β), abs_of_nonneg hh]
    calc
      _ ≤ 1 * (β ^ 2 + 1) * (B + 1) * h := by gcongr <;> linarith [hha, hχ]
      _ = _ := by ring
  have htδ : |a * β ^ 2 * χ * h| ≤ δ := ht.trans (by
    have H := (le_div_iff₀ hT).mp ((hhη.trans (min_le_right _ _)).trans (min_le_left _ _))
    nlinarith)
  have ht₈ : |a * β ^ 2 * χ * h| ≤ 1 / 8 := ht.trans (by
    have H := (le_div_iff₀ (by positivity : 0 < 8 * T)).mp
      ((hhη.trans (min_le_right _ _)).trans (min_le_right _ _))
    nlinarith)
  have hden : 1 / 2 ≤ 1 - 4 * a * β ^ 2 * χ * h := by
    have H := (abs_le.mp ht₈).2
    nlinarith
  have hdenpos : 0 < 1 - 4 * a * β ^ 2 * χ * h := lt_of_lt_of_le (by norm_num) hden
  have hnum : |4 * a * β ^ 2 * h * u| ≤ 4 * β ^ 2 * B * h := by
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg β), abs_of_nonneg hh]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    calc
      _ ≤ 4 * 1 * β ^ 2 * h * B := by gcongr
      _ = _ := by ring
  have hsqrt : h ≤ Real.sqrt h := by
    nlinarith [Real.sq_sqrt hh, Real.sqrt_nonneg h, mul_nonneg hh (sub_nonneg.mpr hh₁)]
  have hmean : |frozenGaussianMean β a u χ h z - z| ≤ M * Real.sqrt h := by
    simp only [frozenGaussianMean, add_sub_cancel_left, abs_div, abs_of_pos hdenpos]
    apply (div_le_iff₀ hdenpos).mpr
    have H := mul_le_mul_of_nonneg_left hden (mul_nonneg hM.le (Real.sqrt_nonneg h))
    have H' := mul_le_mul_of_nonneg_left hsqrt (by positivity : 0 ≤ 4 * β ^ 2 * B)
    have HM : 4 * β ^ 2 * B ≤ M / 2 := by dsimp only [M]; nlinarith [mul_nonneg (abs_nonneg β) hS.le]
    have HM' := mul_le_mul_of_nonneg_right HM (Real.sqrt_nonneg h)
    nlinarith
  have H := hScale i (a * β ^ 2 * χ * h) htδ k hk
  have hb (x : ℝ) (hx : |x| ≤ S) : |β * Real.sqrt h * x| ≤ M * Real.sqrt h := by
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg h)]
    calc
      _ ≤ |β| * Real.sqrt h * S := mul_le_mul_of_nonneg_left hx (by positivity)
      _ ≤ M * Real.sqrt h := by
        have HM : |β| * S ≤ M := by dsimp only [M]; nlinarith [mul_nonneg (sq_nonneg β) hB.le]
        nlinarith [mul_le_mul_of_nonneg_right HM (Real.sqrt_nonneg h)]
  exact ⟨H.1, hmean, hb _ H.2.1, hb _ H.2.2.1, hb _ H.2.2.2.1,
    H.2.2.2.2.1.const_mul (β * Real.sqrt h), H.2.2.2.2.2.const_mul (β * Real.sqrt h)⟩

theorem gaussian_integral_eq_standard_affine (φ : ℝ → ℝ) (hφ : Measurable φ) (m σ : ℝ) :
    (∫ y, φ y ∂gaussianReal m (Real.toNNReal (σ ^ 2))) =
      ∫ g, φ (m + σ * g) ∂gaussianReal 0 1 := by
  have hv : NNReal.mk (σ ^ 2) (sq_nonneg σ) * 1 = Real.toNNReal (σ ^ 2) := by
    apply NNReal.eq
    simp only [NNReal.coe_mk, mul_one, Real.toNNReal_of_nonneg (sq_nonneg σ)]
  have hZ : HasLaw (fun x : ℝ => m + σ * x) (gaussianReal m (Real.toNNReal (σ ^ 2))) (gaussianReal 0 1) := by
    simpa only [id_eq, mul_zero, zero_add, hv] using
      gaussianReal_const_add (gaussianReal_const_mul (HasLaw.id (μ := gaussianReal 0 1)) σ) m
  exact (hZ.integral_comp hφ.aestronglyMeasurable).symm

theorem frozenGaussianScale_sq (β a h k c u χ z : ℝ)
    (ha : a ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z))
    (hdom : (a * β ^ 2 * χ * h, k) ∈ frozenScaleDomain) (i : Fin 3) :
    frozenGaussianScale β a χ h i k ^ 2 =
      gaussianPathCovariance (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z) i i := by
  have hs : frozenNormalizedScale i (a * β ^ 2 * χ * h, k) ^ 2 =
      frozenNormalizedVariance i (a * β ^ 2 * χ * h, k) := Real.sq_sqrt (hdom.2 i).le
  simp only [frozenGaussianScale, mul_pow, Real.sq_sqrt hh, hs]
  rw [frozenSchedule_pathVariance_expansion β a h k c u χ z ha hh hk hl i]
  dsimp only [frozenNormalizedVariance]
  ring

theorem frozenSchedule_separable_standardGaussians (β a h k c u χ z : ℝ)
    (ha : a ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z))
    (hdom : (a * β ^ 2 * χ * h, k) ∈ frozenScaleDomain)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hi : ∀ m : ℝ, ∀ v : ℝ≥0, Integrable φ (gaussianReal m v)) :
    quadraticFirst (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z)
      (fun x => ∑ i : Fin 3, φ (x i)) (fun _ => z) =
      ∑ i : Fin 3, ∫ g, φ (frozenGaussianMean β a u χ h z + frozenGaussianScale β a χ h i k * g) ∂gaussianReal 0 1 := by
  rw [quadraticFirst_separable _ _ hl φ hφ hi]
  apply Finset.sum_congr rfl
  intro i _
  rw [frozenSchedule_pathMean β a h k c u χ z hh hk hl i,
    ← frozenGaussianScale_sq β a h k c u χ z ha hh hk hl hdom i]
  exact gaussian_integral_eq_standard_affine φ hφ _ _

theorem scalarSixthTail_integrable {f : ℝ → ℝ} {B : ℝ} (hf : ContDiff ℝ ∞ f)
    (hB : 0 ≤ B) (hb : ∀ y, |iteratedDeriv 7 f y| ≤ B) (z m : ℝ) (v : ℝ≥0) :
    Integrable (scalarSixthTail f z) (gaussianReal m v) := by
  have hid : HasExpGrowth (fun y : ℝ => y) := HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)
  have hshift := hid.sub_real (HasExpGrowth.const z)
  have habs : HasExpGrowth (fun y : ℝ => |y - z|) := by
    simpa only [Real.norm_eq_abs] using hshift.norm (fun y => norm_nonneg (y - z))
  have hpoly := ((HasExpGrowth.const B).mul (habs.pow 7)).integrable_gaussianMeasure
    (μ := gaussianReal m v) (by fun_prop)
  have hc : Continuous (scalarSixthTail f z) := (hf.sub (scalarTaylorPolynomial_contDiff f 6 z)).continuous
  exact hpoly.mono' hc.aestronglyMeasurable (ae_of_all _ (fun y => by
    rw [Real.norm_eq_abs]
    have H := (scalarSixthTail_bounds hf hb z y).1
    exact H.trans (by nlinarith [mul_nonneg hB (pow_nonneg (abs_nonneg (y - z)) 7)])))

def frozenSixthTailMoment (β : ℝ) (α : ℝ → ℝ) (a s h z k : ℝ) : ℝ :=
  quadraticFirst (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z)
    (fun x => ∑ i : Fin 3, scalarSixthTail (Phi β α (s + 4 * h)) z (x i)) (fun _ => z)

def frozenSixthTailGaussian (β : ℝ) (α : ℝ → ℝ) (a s h z k : ℝ) : ℝ :=
  ∑ i : Fin 3, gaussianAffineExpectation (scalarSixthTail (Phi β α (s + 4 * h)) z)
    (fun _ => frozenGaussianMean β a (jet β α 1 (s + 4 * h) z) (jet β α 2 (s + 4 * h) z) h z)
    (frozenGaussianScale β a (jet β α 2 (s + 4 * h) z) h i) k

theorem frozenSixthTailMoment_eq_gaussian (β : ℝ) (α : ℝ → ℝ) (a s h z k B : ℝ)
    (ha : a ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z))
    (hdom : (a * β ^ 2 * jet β α 2 (s + 4 * h) z * h, k) ∈ frozenScaleDomain)
    (hf : ContDiff ℝ ∞ (Phi β α (s + 4 * h))) (hB : 0 ≤ B)
    (hb : ∀ y, |jet β α 7 (s + 4 * h) y| ≤ B) :
    frozenSixthTailMoment β α a s h z k = frozenSixthTailGaussian β α a s h z k :=
  frozenSchedule_separable_standardGaussians β a h k _ _ _ z ha hh hk hl hdom _
    ((hf.sub (scalarTaylorPolynomial_contDiff _ 6 z)).continuous.measurable)
    (scalarSixthTail_integrable hf hB hb z)

theorem frozenSixthTailGaussian_uniform_control (β B : ℝ) (hB : 0 < B) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ (α : ℝ → ℝ) (a s h z : ℝ),
      a ∈ Ioc (0 : ℝ) 1 → 0 ≤ h → h ≤ h₀ →
      ContDiff ℝ ∞ (Phi β α (s + 4 * h)) →
      |jet β α 1 (s + 4 * h) z| ≤ B → |jet β α 2 (s + 4 * h) z| ≤ B →
      (∀ y, |jet β α 7 (s + 4 * h) y| ≤ B) →
      ∃ g₁ g₂ : ℝ → ℝ, ∀ k ∈ Ioo (-(1 / 2) : ℝ) (1 / 2),
        HasDerivAt (frozenSixthTailGaussian β α a s h z) (g₁ k) k ∧ HasDerivAt g₁ (g₂ k) k ∧
        |frozenSixthTailGaussian β α a s h z k| ≤ C * Real.sqrt h * h ^ 3 ∧
        |g₁ k| ≤ C * Real.sqrt h * h ^ 3 ∧ |g₂ k| ≤ C * Real.sqrt h * h ^ 3 := by
  obtain ⟨M, η, hM, hη, _, hP⟩ := frozenGaussianParameter_uniform_control β B hB
  let J : ℝ := ∫ g, gaussianPolynomialWeight 7 g ∂gaussianReal 0 1
  have hJ : 0 ≤ J := integral_nonneg (fun _ => by unfold gaussianPolynomialWeight; positivity)
  let C := 6 * B * M ^ 7 * (J + 1)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, η, hC, hη, ?_⟩
  intro α a s h z ha hh hhη hf hu hχ h7
  let f := Phi β α (s + 4 * h)
  let m : ℝ → ℝ := fun _ => frozenGaussianMean β a (jet β α 1 (s + 4 * h) z) (jet β α 2 (s + 4 * h) z) h z
  let σ := frozenGaussianScale β a (jet β α 2 (s + 4 * h) z) h
  let σ₁ := frozenGaussianScaleFirst β a (jet β α 2 (s + 4 * h) z) h
  let σ₂ := frozenGaussianScaleSecond β a (jet β α 2 (s + 4 * h) z) h
  let F₁ := fun i => gaussianAffineFirst (scalarSixthTailFirst f z) m (σ i) (fun _ => 0) (σ₁ i)
  let F₂ := fun i => gaussianAffineSecond (scalarSixthTailFirst f z) (scalarSixthTailSecond f z)
    m (σ i) (fun _ => 0) (σ₁ i) (fun _ => 0) (σ₂ i)
  have H (i : Fin 3) := scalarSixthTail_gaussian_control (z := z) hf hB.le h7 hM.le (Real.sqrt_nonneg h)
    (m := m) (σ := σ i) (m₁ := fun _ => 0) (σ₁ := σ₁ i) (m₂ := fun _ => 0) (σ₂ := σ₂ i)
    isOpen_Ioo
    (fun k hk => by
      have HP := hP a _ _ h z ha hu hχ hh hhη i k (abs_le.mpr ⟨hk.1.le, hk.2.le⟩)
      exact ⟨hasDerivAt_const k _, hasDerivAt_const k 0, HP.2.2.2.2.2.1, HP.2.2.2.2.2.2⟩)
    (fun k hk => by
      have HP := hP a _ _ h z ha hu hχ hh hhη i k (abs_le.mpr ⟨hk.1.le, hk.2.le⟩)
      exact ⟨HP.2.1, HP.2.2.1, by simpa only [abs_zero] using mul_nonneg hM.le (Real.sqrt_nonneg h),
        HP.2.2.2.1, by simpa only [abs_zero] using mul_nonneg hM.le (Real.sqrt_nonneg h), HP.2.2.2.2.1⟩)
  have hs : Real.sqrt h ^ 7 = Real.sqrt h * h ^ 3 := by
    calc
      _ = Real.sqrt h * (Real.sqrt h ^ 2) ^ 3 := by ring
      _ = _ := by rw [Real.sq_sqrt hh]
  have hcoef : 6 * B * M ^ 7 * J ≤ C := by
    dsimp only [C]
    nlinarith [mul_nonneg hB.le (pow_nonneg hM.le 7)]
  have hbound (v : Fin 3 → ℝ)
      (hv : ∀ i, |v i| ≤ (2 * B * M ^ 7 * Real.sqrt h ^ 7) * J) :
      |∑ i : Fin 3, v i| ≤ C * Real.sqrt h * h ^ 3 := by
    calc
      _ ≤ ∑ i : Fin 3, |v i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, (2 * B * M ^ 7 * Real.sqrt h ^ 7) * J := Finset.sum_le_sum (fun i _ => hv i)
      _ = (6 * B * M ^ 7 * J) * (Real.sqrt h * h ^ 3) := by simp only [Fin.sum_univ_succ, hs]; ring
      _ ≤ C * (Real.sqrt h * h ^ 3) := mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ = _ := by ring
  refine ⟨fun k => ∑ i : Fin 3, F₁ i k, fun k => ∑ i : Fin 3, F₂ i k, ?_⟩
  intro k hk
  refine ⟨HasDerivAt.fun_sum (fun i _ => (H i k hk).1),
    HasDerivAt.fun_sum (fun i _ => (H i k hk).2.1), ?_, ?_, ?_⟩
  · exact hbound _ (fun i => (H i k hk).2.2.1)
  · exact hbound _ (fun i => (H i k hk).2.2.2.1)
  · exact hbound _ (fun i => (H i k hk).2.2.2.2)

theorem frozenSixthTailMoment_uniform_control (β B : ℝ) (hB : 0 < B) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ (α : ℝ → ℝ) (a s h z : ℝ),
      a ∈ Ioc (0 : ℝ) 1 → 0 ≤ h → h ≤ h₀ →
      ContDiff ℝ ∞ (Phi β α (s + 4 * h)) →
      |jet β α 1 (s + 4 * h) z| ≤ B → |jet β α 2 (s + 4 * h) z| ≤ B →
      (∀ y, |jet β α 7 (s + 4 * h) y| ≤ B) →
      ∃ g₁ g₂ : ℝ → ℝ, ∀ k ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
        HasDerivAt (frozenSixthTailMoment β α a s h z) (g₁ k) k ∧ HasDerivAt g₁ (g₂ k) k ∧
        |frozenSixthTailMoment β α a s h z k| ≤ C * Real.sqrt h * h ^ 3 ∧
        |g₁ k| ≤ C * Real.sqrt h * h ^ 3 ∧ |g₂ k| ≤ C * Real.sqrt h * h ^ 3 := by
  obtain ⟨C, η, hC, hη, H⟩ := frozenSixthTailGaussian_uniform_control β B hB
  obtain ⟨M, ζ, _, hζ, _, hP⟩ := frozenGaussianParameter_uniform_control β B hB
  obtain ⟨ξ, hξ, hA⟩ := terminalTaylorQuadratic_uniform_admissible β B hB
  refine ⟨C, min η (min ζ ξ), hC, by positivity, ?_⟩
  intro α a s h z ha hh hh₀ hf hu hχ h7
  obtain ⟨g₁, g₂, hg⟩ := H α a s h z ha hh (hh₀.trans (min_le_left _ _)) hf hu hχ h7
  have he (k : ℝ) (hk : |k| ≤ 1 / 2) :
      frozenSixthTailMoment β α a s h z k = frozenSixthTailGaussian β α a s h z k := by
    exact frozenSixthTailMoment_eq_gaussian β α a s h z k B (ne_of_gt ha.1) hh hk
      (hA α a s h k z ha hh ((hh₀.trans (min_le_right _ _)).trans (min_le_right _ _)) hk hχ)
      (hP a _ _ h z ha hu hχ hh ((hh₀.trans (min_le_right _ _)).trans (min_le_left _ _)) 0 k hk).1 hf hB.le h7
  refine ⟨g₁, g₂, ?_⟩
  intro k hk
  have hk' : k ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := ⟨by linarith [hk.1], by linarith [hk.2]⟩
  have hnear : frozenSixthTailMoment β α a s h z =ᶠ[𝓝 k] frozenSixthTailGaussian β α a s h z := by
    filter_upwards [isOpen_Ioo.mem_nhds hk'] with x hx
    exact he x (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
  have HG := hg k hk'
  exact ⟨HG.1.congr_of_eventuallyEq hnear, HG.2.1,
    by rw [he k (abs_le.mpr ⟨hk'.1.le, hk'.2.le⟩)]; exact HG.2.2.1,
    HG.2.2.2.1, HG.2.2.2.2⟩

theorem scalarData_sixthTailMoment_control {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      ∃ g₁ g₂ : ℝ → ℝ, ∀ k ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
        HasDerivAt (frozenSixthTailMoment β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z) (g₁ k) k ∧ HasDerivAt g₁ (g₂ k) k ∧
        |frozenSixthTailMoment β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z k| ≤ C * Real.sqrt h * h ^ 3 ∧
        |g₁ k| ≤ C * Real.sqrt h * h ^ 3 ∧ |g₂ k| ≤ C * Real.sqrt h * h ^ 3 := by
  let B := scalarTerminalJetBound D 7 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 7]
  obtain ⟨C, η, hC, hη, H⟩ := frozenSixthTailMoment_uniform_control β B hB
  obtain ⟨c, T, hc, hT, hlin⟩ := D.lin_lower
  let v := min (l / 2) T
  have hv : 0 < v := lt_min (by positivity) hT
  refine ⟨C, min η (min (l / 2) ((D.q - u) / 3)), hC, by positivity, ?_⟩
  intro r hr h hh hh₀ z
  have hhη : h ≤ η := hh₀.trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := (hh₀.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 3 := (hh₀.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : v ≤ r - h := (min_le_left _ _).trans (by linarith [hr.1])
  have ha : cdf (D.μ : Measure ℝ) (r - h) ∈ Ioc (0 : ℝ) 1 := by
    refine ⟨?_, cdf_le_one _ _⟩
    exact (mul_pos hc hv).trans_le ((hlin v ⟨hv.le, min_le_right _ _⟩).trans
      ((cdf (D.μ : Measure ℝ)).mono hs))
  have ht : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith [hr.1]
    · linarith [hr.2, D.q_mem.2]
  have hj (j : ℕ) (hj₁ : 1 ≤ j) (hj₇ : j ≤ 7) (y : ℝ) :
      |jet β (cdf (D.μ : Measure ℝ)) j ((r - h) + 4 * h) y| ≤ B :=
    (scalarData_jet_le D hj₁ hj₇ ht y).trans (by dsimp only [B]; linarith)
  exact H _ _ (r - h) h z ha hh.le hhη (scalarData_phi_contDiff D ht)
    (hj 1 le_rfl (by norm_num) z) (hj 2 (by norm_num) (by norm_num) z) (hj 7 (by norm_num) le_rfl)

theorem frozenFirstMoment_eq_Taylor_add_sixthTail (β : ℝ) (α : ℝ → ℝ) (a s h k z B : ℝ)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z))
    (hφ : BoundedDerivs (Phi β α (s + 4 * h)))
    (hf : ContDiff ℝ ∞ (Phi β α (s + 4 * h))) (hB : 0 ≤ B)
    (hb : ∀ y, |jet β α 7 (s + 4 * h) y| ≤ B) :
    frozenFirstMoment β α a s h k z =
      quadraticFirst (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z)
        (terminalTaylorResidual β α s h z 6) (fun _ => z) + frozenSixthTailMoment β α a s h z k := by
  let K := scalarTerminalResidual β α s h z
  let R := scalarSixthTail (Phi β α (s + 4 * h)) z
  have hK (m : ℝ) (v : ℝ≥0) : Integrable K (gaussianReal m v) := scalarTerminalResidual_integrable β α s h z m v hφ
  have hR (m : ℝ) (v : ℝ≥0) : Integrable R (gaussianReal m v) := scalarSixthTail_integrable hf hB hb z m v
  have hcK : Continuous K := by
    have hΦ := hφ.1.continuous
    unfold K scalarTerminalResidual
    fun_prop
  have hcR : Continuous R := (hf.sub (scalarTaylorPolynomial_contDiff _ 6 z)).continuous
  have hT : terminalTaylorResidual β α s h z 6 = fun x => ∑ i : Fin 3, (K (x i) - R (x i)) := by
    funext x
    unfold terminalTaylorResidual
    rw [terminalTaylorQuadratic_value, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [K, R, scalarTerminalResidual, scalarSixthTail]
    ring
  rw [frozenFirstMoment_eq_scalar_gaussians β α a s h k z hl hφ, hT,
    quadraticFirst_separable _ _ hl (fun y => K y - R y) (hcK.measurable.sub hcR.measurable)
      (fun m v => (hK m v).sub (hR m v))]
  unfold frozenSixthTailMoment
  rw [quadraticFirst_separable _ _ hl _ hcR.measurable hR]
  simp_rw [integral_sub (hK _ _) (hR _ _)]
  rw [Finset.sum_sub_distrib]
  ring

def frozenTiltSwap : Equiv.Perm (Fin 3) := Equiv.swap 1 2

theorem frozenRiccatiCovariance_neg (j : Fin 3) (k : ℝ) :
    frozenRiccatiCovariance j (-k) = (frozenRiccatiCovariance j k).submatrix frozenTiltSwap frozenTiltSwap := by
  ext i l
  fin_cases j <;> fin_cases i <;> fin_cases l <;>
    simp [frozenTiltSwap, Equiv.swap_apply_def, frozenRiccatiCovariance,
      frozenRiccatiCovariance₀, frozenRiccatiCovariance₁, frozenRiccatiCovariance₂,
      physicalInner, q0, q1, q2, outer, commonVector, sharedVector, tentWeight, rampWeight] <;> ring_nf
  all_goals simp only [true_or]

theorem frozenCovarianceResolvent_neg (j : Fin 3) (t k : ℝ) :
    frozenCovarianceResolvent j t (-k) = (frozenCovarianceResolvent j t k).submatrix frozenTiltSwap frozenTiltSwap := by
  unfold frozenCovarianceResolvent
  rw [frozenRiccatiCovariance_neg]
  have H : (1 : Mat3) - t • (frozenRiccatiCovariance j k).submatrix frozenTiltSwap frozenTiltSwap =
      (1 - t • frozenRiccatiCovariance j k).submatrix frozenTiltSwap frozenTiltSwap := by
    ext i l
    simp [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply]
  rw [H, Matrix.inv_submatrix_equiv]

theorem frozenCovarianceQuadratic_neg (k : ℝ) :
    frozenCovarianceQuadratic (-k) = (frozenCovarianceQuadratic k).submatrix frozenTiltSwap frozenTiltSwap := by
  change (3 : ℝ) • (frozenRiccatiCovariance 0 (-k) * frozenRiccatiCovariance 0 (-k)) -
    frozenRiccatiCovariance 1 (-k) * frozenRiccatiCovariance 1 (-k) -
    frozenRiccatiCovariance 2 (-k) * frozenRiccatiCovariance 2 (-k) =
      ((3 : ℝ) • (frozenRiccatiCovariance 0 k * frozenRiccatiCovariance 0 k) -
        frozenRiccatiCovariance 1 k * frozenRiccatiCovariance 1 k -
        frozenRiccatiCovariance 2 k * frozenRiccatiCovariance 2 k).submatrix frozenTiltSwap frozenTiltSwap
  rw [frozenRiccatiCovariance_neg, frozenRiccatiCovariance_neg, frozenRiccatiCovariance_neg]
  simp only [Matrix.submatrix_mul_equiv]
  rfl

theorem frozenCovarianceRemainder_neg (t k : ℝ) :
    frozenCovarianceRemainder t (-k) = (frozenCovarianceRemainder t k).submatrix frozenTiltSwap frozenTiltSwap := by
  change (3 : ℝ) • (frozenRiccatiCovariance 0 (-k) * frozenRiccatiCovariance 0 (-k) * frozenRiccatiCovariance 0 (-k) * frozenCovarianceResolvent 0 t (-k)) -
    frozenRiccatiCovariance 1 (-k) * frozenRiccatiCovariance 1 (-k) * frozenRiccatiCovariance 1 (-k) * frozenCovarianceResolvent 1 t (-k) -
    frozenRiccatiCovariance 2 (-k) * frozenRiccatiCovariance 2 (-k) * frozenRiccatiCovariance 2 (-k) * frozenCovarianceResolvent 2 t (-k) =
      ((3 : ℝ) • (frozenRiccatiCovariance 0 k * frozenRiccatiCovariance 0 k * frozenRiccatiCovariance 0 k * frozenCovarianceResolvent 0 t k) -
        frozenRiccatiCovariance 1 k * frozenRiccatiCovariance 1 k * frozenRiccatiCovariance 1 k * frozenCovarianceResolvent 1 t k -
        frozenRiccatiCovariance 2 k * frozenRiccatiCovariance 2 k * frozenRiccatiCovariance 2 k * frozenCovarianceResolvent 2 t k).submatrix frozenTiltSwap frozenTiltSwap
  simp_rw [frozenRiccatiCovariance_neg, frozenCovarianceResolvent_neg]
  simp only [Matrix.submatrix_mul_equiv]
  rfl

theorem frozenGaussianScale_neg (β a χ h k : ℝ) (i : Fin 3) :
    frozenGaussianScale β a χ h i (-k) = frozenGaussianScale β a χ h (frozenTiltSwap i) k := by
  have hQ := congrArg (fun A : Mat3 => A i i) (frozenCovarianceQuadratic_neg k)
  have hR := congrArg (fun A : Mat3 => A i i) (frozenCovarianceRemainder_neg (a * β ^ 2 * χ * h) k)
  simp only [Matrix.submatrix_apply] at hQ hR
  simp only [frozenGaussianScale, frozenNormalizedScale, frozenNormalizedVariance, hQ, hR]

theorem frozenSixthTailGaussian_even (β : ℝ) (α : ℝ → ℝ) (a s h z k : ℝ) :
    frozenSixthTailGaussian β α a s h z (-k) = frozenSixthTailGaussian β α a s h z k := by
  unfold frozenSixthTailGaussian gaussianAffineExpectation
  simp_rw [frozenGaussianScale_neg]
  exact Equiv.sum_comp frozenTiltSwap (fun i : Fin 3 =>
    ∫ g, scalarSixthTail (Phi β α (s + 4 * h)) z
      (frozenGaussianMean β a (jet β α 1 (s + 4 * h) z) (jet β α 2 (s + 4 * h) z) h z +
        frozenGaussianScale β a (jet β α 2 (s + 4 * h) z) h i k * g) ∂gaussianReal 0 1)

theorem frozenSixthTailGaussian_evenSecondControl (β B : ℝ) (hB : 0 < B) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ (α : ℝ → ℝ) (a s h z : ℝ),
      a ∈ Ioc (0 : ℝ) 1 → 0 ≤ h → h ≤ h₀ →
      ContDiff ℝ ∞ (Phi β α (s + 4 * h)) →
      |jet β α 1 (s + 4 * h) z| ≤ B → |jet β α 2 (s + 4 * h) z| ≤ B →
      (∀ y, |jet β α 7 (s + 4 * h) y| ≤ B) →
      EvenSecondControl (frozenSixthTailGaussian β α a s h z) (1 / 3)
        (C * Real.sqrt h * h ^ 3) 0 := by
  obtain ⟨C, η, hC, hη, H⟩ := frozenSixthTailGaussian_uniform_control β B hB
  refine ⟨C, η, hC, hη, ?_⟩
  intro α a s h z ha hh hhη hf hu hχ h7
  obtain ⟨g₁, g₂, hg⟩ := H α a s h z ha hh hhη hf hu hχ h7
  refine ⟨g₁, g₂, ?_, ?_, fun k _ => frozenSixthTailGaussian_even β α a s h z k⟩
  · intro k hk
    have hk' : k ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := ⟨by linarith [hk.1], by linarith [hk.2]⟩
    exact ⟨(hg k hk').1, (hg k hk').2.1⟩
  · intro k hk
    have hk' : k ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := ⟨by linarith [hk.1], by linarith [hk.2]⟩
    simpa only [zero_mul, add_zero] using (hg k hk').2.2.2.2

theorem frozenSixthTailDifference_uniform_control (β B : ℝ) (hB : 0 < B) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ (α : ℝ → ℝ) (a s h z : ℝ),
      a ∈ Ioc (0 : ℝ) 1 → 0 ≤ h → h ≤ h₀ →
      ContDiff ℝ ∞ (Phi β α (s + 4 * h)) →
      |jet β α 1 (s + 4 * h) z| ≤ B → |jet β α 2 (s + 4 * h) z| ≤ B →
      (∀ y, |jet β α 7 (s + 4 * h) y| ≤ B) →
      EvenSecondControl (fun k => frozenSixthTailMoment β α a s h z k - frozenSixthTailMoment β α a s h z 0)
        (1 / 4) (C * Real.sqrt h * h ^ 3) 0 := by
  obtain ⟨C, η, hC, hη, H⟩ := frozenSixthTailGaussian_evenSecondControl β B hB
  obtain ⟨M, ζ, _, hζ, _, hP⟩ := frozenGaussianParameter_uniform_control β B hB
  obtain ⟨ξ, hξ, hA⟩ := terminalTaylorQuadratic_uniform_admissible β B hB
  refine ⟨C, min η (min ζ ξ), hC, by positivity, ?_⟩
  intro α a s h z ha hh hh₀ hf hu hχ h7
  have HG := H α a s h z ha hh (hh₀.trans (min_le_left _ _)) hf hu hχ h7
  have HE : EvenSecondControl (frozenSixthTailMoment β α a s h z) (1 / 4) (C * Real.sqrt h * h ^ 3) 0 :=
    HG.transfer (by norm_num) (fun k hk => by
      have hk' : |k| ≤ 1 / 2 := (abs_le.mpr hk).trans (by norm_num)
      exact frozenSixthTailMoment_eq_gaussian β α a s h z k B (ne_of_gt ha.1) hh hk'
        (hA α a s h k z ha hh ((hh₀.trans (min_le_right _ _)).trans (min_le_right _ _)) hk' hχ)
        (hP a _ _ h z ha hu hχ hh ((hh₀.trans (min_le_right _ _)).trans (min_le_left _ _)) 0 k hk').1 hf hB.le h7)
  exact HE.sub_const _

theorem scalarData_sixthTailDifference_control {β : ℝ} (D : ScalarData β) {l u : ℝ}
    (hl : 0 < l) (hu : u < D.q) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ,
      EvenSecondControl
        (fun k => frozenSixthTailMoment β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z k -
          frozenSixthTailMoment β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z 0)
        (1 / 4) (C * Real.sqrt h * h ^ 3) 0 := by
  let B := scalarTerminalJetBound D 7 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 7]
  obtain ⟨C, η, hC, hη, H⟩ := frozenSixthTailDifference_uniform_control β B hB
  obtain ⟨c, T, hc, hT, hlin⟩ := D.lin_lower
  let v := min (l / 2) T
  have hv : 0 < v := lt_min (by positivity) hT
  refine ⟨C, min η (min (l / 2) ((D.q - u) / 3)), hC, by positivity, ?_⟩
  intro r hr h hh hh₀ z
  have hhη : h ≤ η := hh₀.trans (min_le_left _ _)
  have hhl : h ≤ l / 2 := (hh₀.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hhq : h ≤ (D.q - u) / 3 := (hh₀.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hs : v ≤ r - h := (min_le_left _ _).trans (by linarith [hr.1])
  have ha : cdf (D.μ : Measure ℝ) (r - h) ∈ Ioc (0 : ℝ) 1 := by
    refine ⟨?_, cdf_le_one _ _⟩
    exact (mul_pos hc hv).trans_le ((hlin v ⟨hv.le, min_le_right _ _⟩).trans ((cdf (D.μ : Measure ℝ)).mono hs))
  have ht : (r - h) + 4 * h ∈ Icc (0 : ℝ) 1 := by
    constructor
    · linarith [hr.1]
    · linarith [hr.2, D.q_mem.2]
  have hj (j : ℕ) (hj₁ : 1 ≤ j) (hj₇ : j ≤ 7) (y : ℝ) :
      |jet β (cdf (D.μ : Measure ℝ)) j ((r - h) + 4 * h) y| ≤ B :=
    (scalarData_jet_le D hj₁ hj₇ ht y).trans (by dsimp only [B]; linarith)
  exact H _ _ (r - h) h z ha hh.le hhη (scalarData_phi_contDiff D ht)
    (hj 1 le_rfl (by norm_num) z) (hj 2 (by norm_num) (by norm_num) z) (hj 7 (by norm_num) le_rfl)

def scalarFourthTail (f : ℝ → ℝ) (z y : ℝ) : ℝ := f y - scalarTaylorPolynomial f 3 z y

def scalarFourthTailFirst (f : ℝ → ℝ) (z y : ℝ) : ℝ := deriv f y - scalarTaylorPolynomial (deriv f) 2 z y

def scalarFourthTailSecond (f : ℝ → ℝ) (z y : ℝ) : ℝ :=
  iteratedDeriv 2 f y - scalarTaylorPolynomial (iteratedDeriv 2 f) 1 z y

theorem scalarFourthTail_derivatives {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (z y : ℝ) :
    HasDerivAt (scalarFourthTail f z) (scalarFourthTailFirst f z y) y ∧
    HasDerivAt (scalarFourthTailFirst f z) (scalarFourthTailSecond f z y) y := by
  have hf₁ := contDiff_deriv_infty hf
  refine ⟨(hf.differentiable (by simp) y).hasDerivAt.sub (scalarTaylorPolynomial_hasDerivAt f 2 z y), ?_⟩
  have H := (hf₁.differentiable (by simp) y).hasDerivAt.sub (scalarTaylorPolynomial_hasDerivAt (deriv f) 1 z y)
  change HasDerivAt (fun x => deriv f x - scalarTaylorPolynomial (deriv f) 2 z x)
    (iteratedDeriv 2 f y - scalarTaylorPolynomial (iteratedDeriv 2 f) 1 z y) y
  have he : iteratedDeriv 2 f = deriv (deriv f) := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [he]
  exact H

theorem scalarFourthTail_jet_bounds {f : ℝ → ℝ} {B : ℝ}
    (hf : ContDiff ℝ ∞ f) (hB : 0 ≤ B) (hb : ∀ y, |iteratedDeriv 4 f y| ≤ B) (z y : ℝ) :
    |scalarFourthTail f z y| ≤ B * |y - z| ^ 4 ∧
    |scalarFourthTailFirst f z y| ≤ B * |y - z| ^ 3 ∧
    |scalarFourthTailSecond f z y| ≤ B * |y - z| ^ 2 := by
  have hf₁ := contDiff_deriv_infty hf
  have hf₂ : ContDiff ℝ ∞ (iteratedDeriv 2 f) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using contDiff_deriv_infty hf₁
  have H₀ := scalarTaylorPolynomial_remainder_le (n := 3) (hf.of_le (by simp)) hb z y
  have H₁ := scalarTaylorPolynomial_remainder_le (n := 2) (hf₁.of_le (by simp))
    (fun y => by simpa only [← iteratedDeriv_succ'] using hb y) z y
  have H₂ := scalarTaylorPolynomial_remainder_le (n := 1) (hf₂.of_le (by simp))
    (fun y => by simpa only [iteratedDeriv_iteratedDeriv_eq] using hb y) z y
  norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at H₀ H₁ H₂
  refine ⟨H₀.trans ?_, H₁.trans ?_, H₂.trans ?_⟩
  · nlinarith [mul_nonneg hB (pow_nonneg (abs_nonneg (y - z)) 4)]
  · nlinarith [mul_nonneg hB (pow_nonneg (abs_nonneg (y - z)) 3)]
  · nlinarith [mul_nonneg hB (pow_nonneg (abs_nonneg (y - z)) 2)]

def scalarFourthTailSquareFirst (f : ℝ → ℝ) (z y : ℝ) : ℝ :=
  2 * scalarFourthTail f z y * scalarFourthTailFirst f z y

def scalarFourthTailSquareSecond (f : ℝ → ℝ) (z y : ℝ) : ℝ :=
  2 * scalarFourthTailFirst f z y ^ 2 + 2 * scalarFourthTail f z y * scalarFourthTailSecond f z y

theorem scalarFourthTailSquare_derivatives {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (z y : ℝ) :
    HasDerivAt (fun y => scalarFourthTail f z y ^ 2) (scalarFourthTailSquareFirst f z y) y ∧
    HasDerivAt (scalarFourthTailSquareFirst f z) (scalarFourthTailSquareSecond f z y) y := by
  have H := scalarFourthTail_derivatives hf z y
  refine ⟨?_, ?_⟩
  · convert H.1.pow 2 using 1
    dsimp only [scalarFourthTailSquareFirst]
    ring
  · convert (H.1.const_mul 2).mul H.2 using 1
    · rfl
    · dsimp only [scalarFourthTailSquareSecond]
      ring

theorem scalarFourthTailSquare_jet_bounds {f : ℝ → ℝ} {B : ℝ}
    (hf : ContDiff ℝ ∞ f) (hB : 0 ≤ B) (hb : ∀ y, |iteratedDeriv 4 f y| ≤ B) (z y : ℝ) :
    |scalarFourthTail f z y ^ 2| ≤ (4 * B ^ 2) * |y - z| ^ 8 ∧
    |scalarFourthTailSquareFirst f z y| ≤ (4 * B ^ 2) * |y - z| ^ 7 ∧
    |scalarFourthTailSquareSecond f z y| ≤ (4 * B ^ 2) * |y - z| ^ 6 := by
  rcases scalarFourthTail_jet_bounds hf hB hb z y with ⟨H₀, H₁, H₂⟩
  have hR : 0 ≤ |y - z| := abs_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_pow]
    have H := pow_le_pow_left₀ (abs_nonneg _) H₀ 2
    calc
      _ ≤ (B * |y - z| ^ 4) ^ 2 := H
      _ ≤ 4 * B ^ 2 * |y - z| ^ 8 := by nlinarith [sq_nonneg (B * |y - z| ^ 4)]
  · dsimp only [scalarFourthTailSquareFirst]
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ 2 * (B * |y - z| ^ 4) * (B * |y - z| ^ 3) := by gcongr
      _ ≤ 4 * B ^ 2 * |y - z| ^ 7 := by nlinarith [mul_nonneg (sq_nonneg B) (pow_nonneg hR 7)]
  · dsimp only [scalarFourthTailSquareSecond]
    calc
      _ ≤ |2 * scalarFourthTailFirst f z y ^ 2| + |2 * scalarFourthTail f z y * scalarFourthTailSecond f z y| := abs_add_le _ _
      _ = 2 * |scalarFourthTailFirst f z y| ^ 2 + 2 * |scalarFourthTail f z y| * |scalarFourthTailSecond f z y| := by
        rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 2 * (B * |y - z| ^ 3) ^ 2 + 2 * (B * |y - z| ^ 4) * (B * |y - z| ^ 2) := by gcongr
      _ = 4 * B ^ 2 * |y - z| ^ 6 := by ring

theorem scalarFourthTailSquare_gaussian_control {f : ℝ → ℝ} {B M ρ z : ℝ}
    (hf : ContDiff ℝ ∞ f) (hB : 0 ≤ B) (hb : ∀ y, |iteratedDeriv 4 f y| ≤ B)
    (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    {m σ m₁ σ₁ m₂ σ₂ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hd : ∀ k ∈ U, HasDerivAt m (m₁ k) k ∧ HasDerivAt m₁ (m₂ k) k ∧
      HasDerivAt σ (σ₁ k) k ∧ HasDerivAt σ₁ (σ₂ k) k)
    (hp : ∀ k ∈ U, |m k - z| ≤ M * ρ ∧ |σ k| ≤ M * ρ ∧
      |m₁ k| ≤ M * ρ ∧ |σ₁ k| ≤ M * ρ ∧ |m₂ k| ≤ M * ρ ∧ |σ₂ k| ≤ M * ρ) :
    ∀ k ∈ U,
      HasDerivAt (gaussianAffineExpectation (fun y => scalarFourthTail f z y ^ 2) m σ)
        (gaussianAffineFirst (scalarFourthTailSquareFirst f z) m σ m₁ σ₁ k) k ∧
      HasDerivAt (gaussianAffineFirst (scalarFourthTailSquareFirst f z) m σ m₁ σ₁)
        (gaussianAffineSecond (scalarFourthTailSquareFirst f z) (scalarFourthTailSquareSecond f z) m σ m₁ σ₁ m₂ σ₂ k) k ∧
      |gaussianAffineExpectation (fun y => scalarFourthTail f z y ^ 2) m σ k| ≤
        (8 * B ^ 2 * M ^ 8 * ρ ^ 8) * ∫ g, gaussianPolynomialWeight 8 g ∂gaussianReal 0 1 ∧
      |gaussianAffineFirst (scalarFourthTailSquareFirst f z) m σ m₁ σ₁ k| ≤
        (8 * B ^ 2 * M ^ 8 * ρ ^ 8) * ∫ g, gaussianPolynomialWeight 8 g ∂gaussianReal 0 1 ∧
      |gaussianAffineSecond (scalarFourthTailSquareFirst f z) (scalarFourthTailSquareSecond f z) m σ m₁ σ₁ m₂ σ₂ k| ≤
        (8 * B ^ 2 * M ^ 8 * ρ ^ 8) * ∫ g, gaussianPolynomialWeight 8 g ∂gaussianReal 0 1 := by
  have hf₁ := contDiff_deriv_infty hf
  have hf₂ : ContDiff ℝ ∞ (iteratedDeriv 2 f) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using contDiff_deriv_infty hf₁
  have hc₀ : Continuous (scalarFourthTail f z) := (hf.sub (scalarTaylorPolynomial_contDiff f 3 z)).continuous
  have hc₁ : Continuous (scalarFourthTailFirst f z) := (hf₁.sub (scalarTaylorPolynomial_contDiff (deriv f) 2 z)).continuous
  have hc₂ : Continuous (scalarFourthTailSecond f z) := (hf₂.sub (scalarTaylorPolynomial_contDiff (iteratedDeriv 2 f) 1 z)).continuous
  have hcF₁ : Continuous (scalarFourthTailSquareFirst f z) := by unfold scalarFourthTailSquareFirst; fun_prop
  have hcF₂ : Continuous (scalarFourthTailSquareSecond f z) := by unfold scalarFourthTailSquareSecond; fun_prop
  have H := gaussian_affine_remainder_control (n := 6) (R := fun y => scalarFourthTail f z y ^ 2) ⟨hc₀.pow 2, hcF₁, hcF₂⟩
    (scalarFourthTailSquare_derivatives hf z) (by positivity : 0 ≤ 4 * B ^ 2) hM hρ
    (scalarFourthTailSquare_jet_bounds hf hB hb z) hU hd hp
  simpa only [show (2 : ℝ) * (4 * B ^ 2) = 8 * B ^ 2 by ring] using H

theorem scalarFourthTail_Phi_eq (β : ℝ) (α : ℝ → ℝ) (s h z y : ℝ) :
    scalarFourthTail (Phi β α (s + 4 * h)) z y = scalarCubicTail β α s h z y := by
  rw [scalarCubicTail_eq]
  rfl

theorem scalarFourthTailSquare_integrable {f : ℝ → ℝ} {B : ℝ} (hf : ContDiff ℝ ∞ f)
    (hB : 0 ≤ B) (hb : ∀ y, |iteratedDeriv 4 f y| ≤ B) (z m : ℝ) (v : ℝ≥0) :
    Integrable (fun y => scalarFourthTail f z y ^ 2) (gaussianReal m v) := by
  have hid : HasExpGrowth (fun y : ℝ => y) := HasExpGrowth.linear (ContinuousLinearMap.id ℝ ℝ)
  have hshift := hid.sub_real (HasExpGrowth.const z)
  have habs : HasExpGrowth (fun y : ℝ => |y - z|) := by
    simpa only [Real.norm_eq_abs] using hshift.norm (fun y => norm_nonneg (y - z))
  have hpoly := ((HasExpGrowth.const (4 * B ^ 2)).mul (habs.pow 8)).integrable_gaussianMeasure
    (μ := gaussianReal m v) (by fun_prop)
  have hc : Continuous (scalarFourthTail f z) := (hf.sub (scalarTaylorPolynomial_contDiff f 3 z)).continuous
  exact hpoly.mono' (hc.pow 2).aestronglyMeasurable (ae_of_all _ (fun y => by
    simpa only [Real.norm_eq_abs] using (scalarFourthTailSquare_jet_bounds hf hB hb z y).1))

theorem frozenSchedule_coordinate_standardGaussian (β a h k c u χ z : ℝ)
    (ha : a ≠ 0) (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hl : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z))
    (hdom : (a * β ^ 2 * χ * h, k) ∈ frozenScaleDomain)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hi : ∀ m : ℝ, ∀ v : ℝ≥0, Integrable φ (gaussianReal m v)) (i : Fin 3) :
    quadraticFirst (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z)
      (fun x => φ (x i)) (fun _ => z) =
      ∫ g, φ (frozenGaussianMean β a u χ h z + frozenGaussianScale β a χ h i k * g) ∂gaussianReal 0 1 := by
  rw [quadraticFirst_coordinate _ _ hl φ hφ hi i, frozenSchedule_pathMean β a h k c u χ z hh hk hl i,
    ← frozenGaussianScale_sq β a h k c u χ z ha hh hk hl hdom i]
  exact gaussian_integral_eq_standard_affine φ hφ _ _

def frozenFourthTailSquareCoordinate (β : ℝ) (α : ℝ → ℝ) (a s h z : ℝ) (i : Fin 3) (k : ℝ) : ℝ :=
  quadraticFirst (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z)
    (fun x => scalarFourthTail (Phi β α (s + 4 * h)) z (x i) ^ 2) (fun _ => z)

theorem scalarData_fourthTailSquareCoordinate_control {β : ℝ} (D : ScalarData β) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ ∀ a s h z : ℝ,
      a ∈ Ioc (0 : ℝ) 1 → 0 ≤ h → h ≤ h₀ → s + 4 * h ∈ Icc (0 : ℝ) 1 →
      ∀ i : Fin 3, ∃ g₁ g₂ : ℝ → ℝ, ∀ k ∈ Icc (-(1 / 4) : ℝ) (1 / 4),
        HasDerivAt (frozenFourthTailSquareCoordinate β (cdf (D.μ : Measure ℝ)) a s h z i) (g₁ k) k ∧
        HasDerivAt g₁ (g₂ k) k ∧
        |frozenFourthTailSquareCoordinate β (cdf (D.μ : Measure ℝ)) a s h z i k| ≤ C * h ^ 4 ∧
        |g₁ k| ≤ C * h ^ 4 ∧ |g₂ k| ≤ C * h ^ 4 := by
  let B := scalarTerminalJetBound D 4 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 4]
  obtain ⟨M, η, hM, hη, _, hP⟩ := frozenGaussianParameter_uniform_control β B hB
  obtain ⟨ξ, hξ, hA⟩ := terminalTaylorQuadratic_uniform_admissible β B hB
  let J : ℝ := ∫ g, gaussianPolynomialWeight 8 g ∂gaussianReal 0 1
  have hJ : 0 ≤ J := integral_nonneg (fun _ => by unfold gaussianPolynomialWeight; positivity)
  let C := 8 * B ^ 2 * M ^ 8 * (J + 1)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, min η ξ, hC, by positivity, ?_⟩
  intro a s h z ha hh hh₀ ht i
  let α := cdf (D.μ : Measure ℝ)
  let f := Phi β α (s + 4 * h)
  let u := jet β α 1 (s + 4 * h) z
  let χ := jet β α 2 (s + 4 * h) z
  let m : ℝ → ℝ := fun _ => frozenGaussianMean β a u χ h z
  let σ := frozenGaussianScale β a χ h i
  let σ₁ := frozenGaussianScaleFirst β a χ h i
  let σ₂ := frozenGaussianScaleSecond β a χ h i
  have hf : ContDiff ℝ ∞ f := scalarData_phi_contDiff D ht
  have hj (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (y : ℝ) : |jet β α j (s + 4 * h) y| ≤ B :=
    (scalarData_jet_le D hj₁ hj₄ ht y).trans (by dsimp only [B]; linarith)
  have hu : |u| ≤ B := hj 1 le_rfl (by norm_num) z
  have hχ : |χ| ≤ B := hj 2 (by norm_num) (by norm_num) z
  have H := scalarFourthTailSquare_gaussian_control (z := z) hf hB.le (hj 4 (by norm_num) le_rfl)
    hM.le (Real.sqrt_nonneg h) (m := m) (σ := σ) (m₁ := fun _ => 0) (σ₁ := σ₁)
    (m₂ := fun _ => 0) (σ₂ := σ₂) isOpen_Ioo
    (fun k hk => by
      have HP := hP a u χ h z ha hu hχ hh (hh₀.trans (min_le_left _ _)) i k (abs_le.mpr ⟨hk.1.le, hk.2.le⟩)
      exact ⟨hasDerivAt_const k _, hasDerivAt_const k 0, HP.2.2.2.2.2.1, HP.2.2.2.2.2.2⟩)
    (fun k hk => by
      have HP := hP a u χ h z ha hu hχ hh (hh₀.trans (min_le_left _ _)) i k (abs_le.mpr ⟨hk.1.le, hk.2.le⟩)
      exact ⟨HP.2.1, HP.2.2.1, by simpa only [abs_zero] using mul_nonneg hM.le (Real.sqrt_nonneg h),
        HP.2.2.2.1, by simpa only [abs_zero] using mul_nonneg hM.le (Real.sqrt_nonneg h), HP.2.2.2.2.1⟩)
  have he (k : ℝ) (hk : |k| ≤ 1 / 2) :
      frozenFourthTailSquareCoordinate β α a s h z i k =
        gaussianAffineExpectation (fun y => scalarFourthTail f z y ^ 2) m σ k := by
    exact frozenSchedule_coordinate_standardGaussian β a h k _ u χ z (ne_of_gt ha.1) hh hk
      (hA α a s h k z ha hh (hh₀.trans (min_le_right _ _)) hk hχ)
      (hP a u χ h z ha hu hχ hh (hh₀.trans (min_le_left _ _)) i k hk).1 _
      (((hf.sub (scalarTaylorPolynomial_contDiff f 3 z)).continuous.pow 2).measurable)
      (scalarFourthTailSquare_integrable hf hB.le (hj 4 (by norm_num) le_rfl) z) i
  let g₁ := gaussianAffineFirst (scalarFourthTailSquareFirst f z) m σ (fun _ => 0) σ₁
  let g₂ := gaussianAffineSecond (scalarFourthTailSquareFirst f z) (scalarFourthTailSquareSecond f z) m σ (fun _ => 0) σ₁ (fun _ => 0) σ₂
  have hs : Real.sqrt h ^ 8 = h ^ 4 := by
    rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, Real.sq_sqrt hh]
  have hb (x : ℝ) (hx : |x| ≤ (8 * B ^ 2 * M ^ 8 * Real.sqrt h ^ 8) * J) : |x| ≤ C * h ^ 4 := by
    rw [hs] at hx
    have HJ := mul_le_mul_of_nonneg_left (by linarith : J ≤ J + 1)
      (by positivity : 0 ≤ 8 * B ^ 2 * M ^ 8 * h ^ 4)
    dsimp only [C]
    nlinarith
  refine ⟨g₁, g₂, ?_⟩
  intro k hk
  have hk' : k ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := ⟨by linarith [hk.1], by linarith [hk.2]⟩
  have hnear : frozenFourthTailSquareCoordinate β α a s h z i =ᶠ[𝓝 k]
      gaussianAffineExpectation (fun y => scalarFourthTail f z y ^ 2) m σ := by
    filter_upwards [isOpen_Ioo.mem_nhds hk'] with x hx
    exact he x (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
  have HK := H k hk'
  refine ⟨HK.1.congr_of_eventuallyEq hnear, HK.2.1, ?_, hb _ HK.2.2.2.1, hb _ HK.2.2.2.2⟩
  rw [he k (abs_le.mpr ⟨hk'.1.le, hk'.2.le⟩)]
  exact hb _ HK.2.2.1

def firstTaylorCoefficientError (β : ℝ) (α : ℝ → ℝ) (a s h z k : ℝ) : ℝ :=
  (quadraticFirst (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z)
      (terminalTaylorResidual β α s h z 6) (fun _ => z) -
    quadraticFirst (frozenSchedule β a (1 / 2) h 0) (terminalTaylorQuadratic β α s h z)
      (terminalTaylorResidual β α s h z 6) (fun _ => z)) -
    firstMomentRow k h a (β ^ 2) (jet β α 1 (s + 4 * h) z) (jet β α 2 (s + 4 * h) z)
      (jet β α 3 (s + 4 * h) z) (jet β α 4 (s + 4 * h) z)

theorem firstCoefficientError_split (β : ℝ) (α : ℝ → ℝ) (a s h z k B : ℝ)
    (hQk : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z))
    (hQ₀ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h 0) (terminalTaylorQuadratic β α s h z))
    (hφ : BoundedDerivs (Phi β α (s + 4 * h)))
    (hf : ContDiff ℝ ∞ (Phi β α (s + 4 * h))) (hB : 0 ≤ B)
    (hb : ∀ y, |jet β α 7 (s + 4 * h) y| ≤ B) :
    firstCoefficientError β α a s h z k = firstTaylorCoefficientError β α a s h z k +
      (frozenSixthTailMoment β α a s h z k - frozenSixthTailMoment β α a s h z 0) := by
  have Hk := frozenFirstMoment_eq_Taylor_add_sixthTail β α a s h k z B hQk hφ hf hB hb
  have H₀ := frozenFirstMoment_eq_Taylor_add_sixthTail β α a s h 0 z B hQ₀ hφ hf hB hb
  unfold firstCoefficientError firstTaylorCoefficientError
  rw [Hk, H₀]
  ring

end SKBarriers2.Corner
