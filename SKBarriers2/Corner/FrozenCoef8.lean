module

public import SKBarriers2.Corner.FrozenCoef7

@[expose] public section

noncomputable section
open scoped BigOperators Matrix ContDiff Topology NNReal
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

theorem gaussian_polynomial_integral_controls
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
    IntegralDerivativeControl (gaussianReal 0 1) F F₁ k ∧
      IntegralDerivativeControl (gaussianReal 0 1) F₁ F₂ k := by
  have hk : k ∈ U := mem_of_mem_nhds hU
  have hi₀ := integrable_of_gaussianPolynomialWeight_bound (hm k hk).1
    (fun g => (hb k hk g).1)
  have hi₁ := integrable_of_gaussianPolynomialWeight_bound (hm k hk).2.1
    (fun g => (hb k hk g).2.1)
  have hdom := (gaussianPolynomialWeight_integrable n).const_mul B
  constructor
  · exact ⟨U, hU, (fun g => B * gaussianPolynomialWeight n g),
      Filter.mem_of_superset hU (fun x hx => (hm x hx).1), hi₀,
      (hm k hk).2.1, hdom,
      ae_of_all _ (fun g x hx => by
        simpa only [Real.norm_eq_abs] using (hb x hx g).2.1),
      ae_of_all _ (fun g x hx => (hd g x hx).1)⟩
  · exact ⟨U, hU, (fun g => B * gaussianPolynomialWeight n g),
      Filter.mem_of_superset hU (fun x hx => (hm x hx).2.1), hi₁,
      (hm k hk).2.2, hdom,
      ae_of_all _ (fun g x hx => by
        simpa only [Real.norm_eq_abs] using (hb x hx g).2.2),
      ae_of_all _ (fun g x hx => (hd g x hx).2)⟩

def jointGaussianIntegral (F : ℝ → ℝ → ℝ → ℝ) (k : ℝ) : ℝ :=
  ∫ g, ∫ t, F k g t ∂gaussianReal 0 1 ∂gaussianReal 0 1

theorem jointGaussianIntegral_abs_le {F : ℝ → ℝ → ℝ → ℝ} {k B : ℝ} {n : ℕ}
    (hb : ∀ g t, |F k g t| ≤
      B * gaussianPolynomialWeight n g * gaussianPolynomialWeight n t) :
    |jointGaussianIntegral F k| ≤
      B * (∫ g, gaussianPolynomialWeight n g ∂gaussianReal 0 1) ^ 2 := by
  let J := ∫ g, gaussianPolynomialWeight n g ∂gaussianReal 0 1
  have hJ : 0 ≤ J := integral_nonneg (fun g => by
    unfold gaussianPolynomialWeight
    positivity)
  have hi (g : ℝ) : |∫ t, F k g t ∂gaussianReal 0 1| ≤
      B * gaussianPolynomialWeight n g * J :=
    gaussian_integral_abs_le_polynomial (hb g)
  have ho := gaussian_integral_abs_le_polynomial (B := B * J) (n := n)
    (F := fun g => ∫ t, F k g t ∂gaussianReal 0 1) (fun g => by
      calc
        _ ≤ B * gaussianPolynomialWeight n g * J := hi g
        _ = _ := by ring)
  simpa only [jointGaussianIntegral, J, pow_two, mul_assoc] using ho

theorem jointGaussianIntegral_controls
    {F F₁ F₂ : ℝ → ℝ → ℝ → ℝ} {U : Set ℝ} {B : ℝ} {n : ℕ}
    (hU : IsOpen U)
    (hc : ∀ k ∈ U, Continuous (fun p : ℝ × ℝ => F k p.1 p.2) ∧
      Continuous (fun p : ℝ × ℝ => F₁ k p.1 p.2) ∧
      Continuous (fun p : ℝ × ℝ => F₂ k p.1 p.2))
    (hd : ∀ k ∈ U, ∀ g t, HasDerivAt (fun x => F x g t) (F₁ k g t) k ∧
      HasDerivAt (fun x => F₁ x g t) (F₂ k g t) k)
    (hb : ∀ k ∈ U, ∀ g t,
      |F k g t| ≤ B * gaussianPolynomialWeight n g * gaussianPolynomialWeight n t ∧
      |F₁ k g t| ≤ B * gaussianPolynomialWeight n g * gaussianPolynomialWeight n t ∧
      |F₂ k g t| ≤ B * gaussianPolynomialWeight n g * gaussianPolynomialWeight n t) :
    ∀ k ∈ U,
      IntegralDerivativeControl (gaussianReal 0 1)
        (fun x g => ∫ t, F x g t ∂gaussianReal 0 1)
        (fun x g => ∫ t, F₁ x g t ∂gaussianReal 0 1) k ∧
      IntegralDerivativeControl (gaussianReal 0 1)
        (fun x g => ∫ t, F₁ x g t ∂gaussianReal 0 1)
        (fun x g => ∫ t, F₂ x g t ∂gaussianReal 0 1) k := by
  let J := ∫ g, gaussianPolynomialWeight n g ∂gaussianReal 0 1
  have hi (k : ℝ) (hk : k ∈ U) (g : ℝ) :=
    gaussian_polynomial_integral_controls (hU.mem_nhds hk)
      (F := fun x t => F x g t) (F₁ := fun x t => F₁ x g t)
      (F₂ := fun x t => F₂ x g t)
      (fun x hx =>
        ⟨((hc x hx).1.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable,
          ((hc x hx).2.1.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable,
          ((hc x hx).2.2.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable⟩)
      (fun t x hx => hd x hx g t) (fun x hx t => hb x hx g t)
  intro k hk
  apply gaussian_polynomial_integral_controls (hU.mem_nhds hk) (B := B * J) (n := n)
  · intro x hx
    exact ⟨(hc x hx).1.stronglyMeasurable.integral_prod_right.aestronglyMeasurable,
      (hc x hx).2.1.stronglyMeasurable.integral_prod_right.aestronglyMeasurable,
      (hc x hx).2.2.stronglyMeasurable.integral_prod_right.aestronglyMeasurable⟩
  · intro g x hx
    exact ⟨(hi x hx g).1.hasDerivAt, (hi x hx g).2.hasDerivAt⟩
  · intro x hx g
    have h₀ := gaussian_integral_abs_le_polynomial (fun t => (hb x hx g t).1)
    have h₁ := gaussian_integral_abs_le_polynomial (fun t => (hb x hx g t).2.1)
    have h₂ := gaussian_integral_abs_le_polynomial (fun t => (hb x hx g t).2.2)
    exact ⟨by simpa only [J, mul_assoc, mul_left_comm, mul_comm] using h₀,
      by simpa only [J, mul_assoc, mul_left_comm, mul_comm] using h₁,
      by simpa only [J, mul_assoc, mul_left_comm, mul_comm] using h₂⟩

structure JointGaussianJet where
  value : ℝ → ℝ → ℝ → ℝ
  first : ℝ → ℝ → ℝ → ℝ
  second : ℝ → ℝ → ℝ → ℝ

namespace JointGaussianJet

def RegularOn (F : JointGaussianJet) (U : Set ℝ) : Prop :=
  (∀ k ∈ U, Continuous (fun p : ℝ × ℝ => F.value k p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => F.first k p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => F.second k p.1 p.2)) ∧
  (∀ k ∈ U, ∀ g t, HasDerivAt (fun x => F.value x g t) (F.first k g t) k ∧
    HasDerivAt (fun x => F.first x g t) (F.second k g t) k)

def PolynomialBound (F : JointGaussianJet) (U : Set ℝ) (n : ℕ) (B : ℝ) : Prop :=
  ∀ k ∈ U, ∀ g t,
    |F.value k g t| ≤ B * gaussianPolynomialWeight n g * gaussianPolynomialWeight n t ∧
    |F.first k g t| ≤ B * gaussianPolynomialWeight n g * gaussianPolynomialWeight n t ∧
    |F.second k g t| ≤ B * gaussianPolynomialWeight n g * gaussianPolynomialWeight n t

def mul (F G : JointGaussianJet) : JointGaussianJet where
  value := fun k g t => F.value k g t * G.value k g t
  first := fun k g t => F.first k g t * G.value k g t + F.value k g t * G.first k g t
  second := fun k g t => F.second k g t * G.value k g t +
    2 * F.first k g t * G.first k g t + F.value k g t * G.second k g t

def add (F G : JointGaussianJet) : JointGaussianJet where
  value := fun k g t => F.value k g t + G.value k g t
  first := fun k g t => F.first k g t + G.first k g t
  second := fun k g t => F.second k g t + G.second k g t

theorem RegularOn.add {F G : JointGaussianJet} {U : Set ℝ}
    (hF : F.RegularOn U) (hG : G.RegularOn U) : (F.add G).RegularOn U := by
  constructor
  · intro k hk
    exact ⟨((hF.1 k hk).1.add (hG.1 k hk).1),
      ((hF.1 k hk).2.1.add (hG.1 k hk).2.1),
      ((hF.1 k hk).2.2.add (hG.1 k hk).2.2)⟩
  · intro k hk g t
    exact ⟨((hF.2 k hk g t).1.add (hG.2 k hk g t).1),
      ((hF.2 k hk g t).2.add (hG.2 k hk g t).2)⟩

theorem PolynomialBound.add {F G : JointGaussianJet} {U : Set ℝ}
    {n : ℕ} {A B : ℝ}
    (hF : F.PolynomialBound U n A) (hG : G.PolynomialBound U n B) :
    (F.add G).PolynomialBound U n (A + B) := by
  intro k hk g t
  have H {x y : ℝ}
      (hx : |x| ≤ A * gaussianPolynomialWeight n g * gaussianPolynomialWeight n t)
      (hy : |y| ≤ B * gaussianPolynomialWeight n g * gaussianPolynomialWeight n t) :
      |x + y| ≤ (A + B) * gaussianPolynomialWeight n g * gaussianPolynomialWeight n t := by
    calc
      _ ≤ |x| + |y| := abs_add_le _ _
      _ ≤ A * gaussianPolynomialWeight n g * gaussianPolynomialWeight n t +
          B * gaussianPolynomialWeight n g * gaussianPolynomialWeight n t := add_le_add hx hy
      _ = _ := by ring
  exact ⟨H (hF k hk g t).1 (hG k hk g t).1,
    H (hF k hk g t).2.1 (hG k hk g t).2.1,
    H (hF k hk g t).2.2 (hG k hk g t).2.2⟩

theorem PolynomialBound.mono {F : JointGaussianJet} {U : Set ℝ}
    {n m : ℕ} {A B : ℝ} (hA : 0 ≤ A) (hnm : n ≤ m) (hAB : A ≤ B)
    (hF : F.PolynomialBound U n A) : F.PolynomialBound U m B := by
  intro k hk g t
  have hW (x : ℝ) : gaussianPolynomialWeight n x ≤ gaussianPolynomialWeight m x :=
    pow_le_pow_right₀ (by have H := abs_nonneg x; linarith : 1 ≤ 1 + |x|) hnm
  have hb : A * gaussianPolynomialWeight n g * gaussianPolynomialWeight n t ≤
      B * gaussianPolynomialWeight m g * gaussianPolynomialWeight m t := by
    have hn (x : ℝ) : 0 ≤ gaussianPolynomialWeight n x := by
      unfold gaussianPolynomialWeight
      positivity
    have hm (x : ℝ) : 0 ≤ gaussianPolynomialWeight m x := by
      unfold gaussianPolynomialWeight
      positivity
    calc
      _ ≤ A * gaussianPolynomialWeight m g * gaussianPolynomialWeight m t :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hW g) hA) (hW t) (hn t) (mul_nonneg hA (hm g))
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hAB (by unfold gaussianPolynomialWeight; positivity))
          (by unfold gaussianPolynomialWeight; positivity)
  exact ⟨(hF k hk g t).1.trans hb, (hF k hk g t).2.1.trans hb,
    (hF k hk g t).2.2.trans hb⟩

theorem RegularOn.mul {F G : JointGaussianJet} {U : Set ℝ}
    (hF : F.RegularOn U) (hG : G.RegularOn U) : (F.mul G).RegularOn U := by
  constructor
  · intro k hk
    rcases hF.1 k hk with ⟨hF₀, hF₁, hF₂⟩
    rcases hG.1 k hk with ⟨hG₀, hG₁, hG₂⟩
    exact ⟨hF₀.mul hG₀, (hF₁.mul hG₀).add (hF₀.mul hG₁),
      ((hF₂.mul hG₀).add ((continuous_const.mul hF₁).mul hG₁)).add (hF₀.mul hG₂)⟩
  · intro k hk g t
    have hF' := hF.2 k hk g t
    have hG' := hG.2 k hk g t
    refine ⟨hF'.1.mul hG'.1, ?_⟩
    convert (hF'.2.mul hG'.1).add (hF'.1.mul hG'.2) using 1
    · rfl
    · dsimp only [JointGaussianJet.mul]
      ring

private theorem product_jet_bounds {f f₁ f₂ g g₁ g₂ A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : |f| ≤ A ∧ |f₁| ≤ A ∧ |f₂| ≤ A)
    (hg : |g| ≤ B ∧ |g₁| ≤ B ∧ |g₂| ≤ B) :
    |f * g| ≤ 4 * A * B ∧
    |f₁ * g + f * g₁| ≤ 4 * A * B ∧
    |f₂ * g + 2 * f₁ * g₁ + f * g₂| ≤ 4 * A * B := by
  have H (x y : ℝ) (hx : |x| ≤ A) (hy : |y| ≤ B) : |x * y| ≤ A * B := by
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) hA
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  refine ⟨(H f g hf.1 hg.1).trans (by nlinarith), ?_, ?_⟩
  · exact (abs_add_le _ _).trans (by
      have h₁ := H f₁ g hf.2.1 hg.1
      have h₂ := H f g₁ hf.1 hg.2.1
      nlinarith only [h₁, h₂, hAB])
  · have h₀ := H f₂ g hf.2.2 hg.1
    have h₁ := H f₁ g₁ hf.2.1 hg.2.1
    have h₂ := H f g₂ hf.1 hg.2.2
    have he : |2 * f₁ * g₁| = 2 * |f₁ * g₁| := by
      rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ |f₂ * g + 2 * f₁ * g₁| + |f * g₂| := abs_add_le _ _
      _ ≤ (|f₂ * g| + |2 * f₁ * g₁|) + |f * g₂| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ 4 * A * B := by rw [he]; nlinarith only [h₀, h₁, h₂]

theorem PolynomialBound.mul {F G : JointGaussianJet} {U : Set ℝ}
    {n m : ℕ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : F.PolynomialBound U n A) (hG : G.PolynomialBound U m B) :
    (F.mul G).PolynomialBound U (n + m) (4 * A * B) := by
  intro k hk g t
  have H := product_jet_bounds (by unfold gaussianPolynomialWeight; positivity)
    (by unfold gaussianPolynomialWeight; positivity) (hF k hk g t) (hG k hk g t)
  have he : 4 * (A * gaussianPolynomialWeight n g * gaussianPolynomialWeight n t) *
      (B * gaussianPolynomialWeight m g * gaussianPolynomialWeight m t) =
      (4 * A * B) * gaussianPolynomialWeight (n + m) g *
        gaussianPolynomialWeight (n + m) t := by
    simp only [gaussianPolynomialWeight, pow_add]
    ring
  rw [he] at H
  exact H

theorem integral_derivatives {F : JointGaussianJet} {U : Set ℝ} {n : ℕ} {B : ℝ}
    (hU : IsOpen U) (hF : F.RegularOn U) (hb : F.PolynomialBound U n B) :
    ∀ k ∈ U,
      HasDerivAt (jointGaussianIntegral F.value) (jointGaussianIntegral F.first k) k ∧
      HasDerivAt (jointGaussianIntegral F.first) (jointGaussianIntegral F.second k) k := by
  intro k hk
  have H := jointGaussianIntegral_controls hU hF.1 hF.2 hb k hk
  exact ⟨H.1.hasDerivAt, H.2.hasDerivAt⟩

theorem integral_bounds {F : JointGaussianJet} {U : Set ℝ} {n : ℕ} {B : ℝ}
    (hb : F.PolynomialBound U n B) {k : ℝ} (hk : k ∈ U) :
    |jointGaussianIntegral F.value k| ≤
        B * (∫ g, gaussianPolynomialWeight n g ∂gaussianReal 0 1) ^ 2 ∧
      |jointGaussianIntegral F.first k| ≤
        B * (∫ g, gaussianPolynomialWeight n g ∂gaussianReal 0 1) ^ 2 ∧
      |jointGaussianIntegral F.second k| ≤
        B * (∫ g, gaussianPolynomialWeight n g ∂gaussianReal 0 1) ^ 2 :=
  ⟨jointGaussianIntegral_abs_le (fun g t => (hb k hk g t).1),
    jointGaussianIntegral_abs_le (fun g t => (hb k hk g t).2.1),
    jointGaussianIntegral_abs_le (fun g t => (hb k hk g t).2.2)⟩

end JointGaussianJet

def jointGaussianAffine (A : Fin 3 → ℝ → ℝ) (k g t : ℝ) : ℝ :=
  A 0 k + A 1 k * g + A 2 k * t

def jointAffineRemainderJet (R R₁ R₂ : ℝ → ℝ)
    (A A₁ A₂ : Fin 3 → ℝ → ℝ) : JointGaussianJet where
  value := fun k g t => R (jointGaussianAffine A k g t)
  first := fun k g t => R₁ (jointGaussianAffine A k g t) * jointGaussianAffine A₁ k g t
  second := fun k g t => R₂ (jointGaussianAffine A k g t) *
      jointGaussianAffine A₁ k g t ^ 2 +
    R₁ (jointGaussianAffine A k g t) * jointGaussianAffine A₂ k g t

theorem jointAffineRemainderJet_regular
    {R R₁ R₂ : ℝ → ℝ} {A A₁ A₂ : Fin 3 → ℝ → ℝ} {U : Set ℝ}
    (hc : Continuous R ∧ Continuous R₁ ∧ Continuous R₂)
    (hdR : ∀ y, HasDerivAt R (R₁ y) y ∧ HasDerivAt R₁ (R₂ y) y)
    (hdA : ∀ k ∈ U, ∀ i, HasDerivAt (A i) (A₁ i k) k ∧
      HasDerivAt (A₁ i) (A₂ i k) k) :
    (jointAffineRemainderJet R R₁ R₂ A A₁ A₂).RegularOn U := by
  have hX (B : Fin 3 → ℝ → ℝ) (k : ℝ) :
      Continuous (fun p : ℝ × ℝ => jointGaussianAffine B k p.1 p.2) := by
    unfold jointGaussianAffine
    fun_prop
  constructor
  · intro k _
    exact ⟨hc.1.comp (hX A k), (hc.2.1.comp (hX A k)).mul (hX A₁ k),
      ((hc.2.2.comp (hX A k)).mul ((hX A₁ k).pow 2)).add
        ((hc.2.1.comp (hX A k)).mul (hX A₂ k))⟩
  · intro k hk g t
    have h₀ : HasDerivAt (fun x => jointGaussianAffine A x g t)
        (jointGaussianAffine A₁ k g t) k :=
      (((hdA k hk 0).1.add ((hdA k hk 1).1.mul_const g)).add
        ((hdA k hk 2).1.mul_const t))
    have h₁ : HasDerivAt (fun x => jointGaussianAffine A₁ x g t)
        (jointGaussianAffine A₂ k g t) k :=
      (((hdA k hk 0).2.add ((hdA k hk 1).2.mul_const g)).add
        ((hdA k hk 2).2.mul_const t))
    refine ⟨(hdR _).1.comp k h₀, ?_⟩
    convert ((hdR _).2.comp k h₀).mul h₁ using 1
    · rfl
    · dsimp only [jointAffineRemainderJet, Function.comp_def]
      ring

private theorem joint_affine_intercept_bound {a b z M ρ : ℝ}
    (ha : |a - z| ≤ M * ρ) (hb : |b| ≤ M * ρ) (g : ℝ) :
    |a + b * g - z| ≤ (M * (1 + |g|)) * ρ := by
  calc
    _ = |(a - z) + b * g| := by congr 1; ring
    _ ≤ |a - z| + |b * g| := abs_add_le _ _
    _ = |a - z| + |b| * |g| := by rw [abs_mul]
    _ ≤ M * ρ + M * ρ * |g| := by gcongr
    _ = _ := by ring

theorem jointAffineRemainderJet_bound
    {R R₁ R₂ : ℝ → ℝ} {n : ℕ} {B M ρ z : ℝ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hR : ∀ y, |R y| ≤ B * |y - z| ^ (n + 2) ∧
      |R₁ y| ≤ B * |y - z| ^ (n + 1) ∧ |R₂ y| ≤ B * |y - z| ^ n)
    {A A₁ A₂ : Fin 3 → ℝ → ℝ} {U : Set ℝ}
    (hp : ∀ k ∈ U, ∀ i,
      |A i k - (if i = 0 then z else 0)| ≤ M * ρ ∧
      |A₁ i k| ≤ M * ρ ∧ |A₂ i k| ≤ M * ρ) :
    (jointAffineRemainderJet R R₁ R₂ A A₁ A₂).PolynomialBound U (n + 2)
      (2 * B * M ^ (n + 2) * ρ ^ (n + 2)) := by
  intro k hk g t
  have h₀ : |A 0 k - z| ≤ M * ρ := by simpa using (hp k hk 0).1
  have h₁ : |A 1 k| ≤ M * ρ := by simpa using (hp k hk 1).1
  have h₂ : |A 2 k| ≤ M * ρ := by simpa using (hp k hk 2).1
  have hA : |A 0 k + A 1 k * g - z| ≤ (M * (1 + |g|)) * ρ :=
    joint_affine_intercept_bound h₀ h₁ g
  have hA₁ : |A₁ 0 k + A₁ 1 k * g| ≤ (M * (1 + |g|)) * ρ := by
    simpa only [sub_zero] using joint_affine_intercept_bound
      (z := 0) (by simpa only [sub_zero] using (hp k hk 0).2.1) (hp k hk 1).2.1 g
  have hA₂ : |A₂ 0 k + A₂ 1 k * g| ≤ (M * (1 + |g|)) * ρ := by
    simpa only [sub_zero] using joint_affine_intercept_bound
      (z := 0) (by simpa only [sub_zero] using (hp k hk 0).2.2) (hp k hk 1).2.2 g
  have hscale {x : ℝ} (hx : |x| ≤ M * ρ) : |x| ≤ (M * (1 + |g|)) * ρ := by
    have H := mul_nonneg (mul_nonneg hM hρ) (abs_nonneg g)
    nlinarith only [hx, H]
  have H := affine_remainder_integrand_bounds hB
    (mul_nonneg hM (by positivity : 0 ≤ 1 + |g|)) hρ hR
    hA (hscale h₂) hA₁ (hscale (hp k hk 2).2.1) hA₂ (hscale (hp k hk 2).2.2) t
  have he : (2 * B * (M * (1 + |g|)) ^ (n + 2) * ρ ^ (n + 2)) *
      gaussianPolynomialWeight (n + 2) t =
      (2 * B * M ^ (n + 2) * ρ ^ (n + 2)) *
        gaussianPolynomialWeight (n + 2) g * gaussianPolynomialWeight (n + 2) t := by
    simp only [gaussianPolynomialWeight, mul_pow]
    ring
  rw [he] at H
  exact H

def scalarCubicPart (f : ℝ → ℝ) (z y : ℝ) : ℝ :=
  iteratedDeriv 3 f z / 6 * (y - z) ^ 3

def scalarCubicPartFirst (f : ℝ → ℝ) (z y : ℝ) : ℝ :=
  iteratedDeriv 3 f z / 2 * (y - z) ^ 2

def scalarCubicPartSecond (f : ℝ → ℝ) (z y : ℝ) : ℝ :=
  iteratedDeriv 3 f z * (y - z)

theorem scalarCubicPart_derivatives (f : ℝ → ℝ) (z y : ℝ) :
    HasDerivAt (scalarCubicPart f z) (scalarCubicPartFirst f z y) y ∧
      HasDerivAt (scalarCubicPartFirst f z) (scalarCubicPartSecond f z y) y := by
  constructor
  · convert ((((hasDerivAt_id y).sub_const z).pow 3).const_mul
      (iteratedDeriv 3 f z / 6)) using 1
    · rfl
    · dsimp only [scalarCubicPartFirst, id_eq]
      ring
  · convert ((((hasDerivAt_id y).sub_const z).pow 2).const_mul
      (iteratedDeriv 3 f z / 2)) using 1
    · rfl
    · dsimp only [scalarCubicPartSecond, id_eq]
      ring

theorem scalarCubicPart_jet_bounds {f : ℝ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) {z : ℝ} (hb : |iteratedDeriv 3 f z| ≤ B) (y : ℝ) :
    |scalarCubicPart f z y| ≤ B * |y - z| ^ 3 ∧
      |scalarCubicPartFirst f z y| ≤ B * |y - z| ^ 2 ∧
      |scalarCubicPartSecond f z y| ≤ B * |y - z| := by
  have hb₆ : |iteratedDeriv 3 f z / 6| ≤ B := by
    rw [abs_div]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    linarith only [hb, hB]
  have hb₂ : |iteratedDeriv 3 f z / 2| ≤ B := by
    rw [abs_div]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith only [hb, hB]
  exact ⟨by
      dsimp only [scalarCubicPart]
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_right hb₆ (by positivity),
    by
      dsimp only [scalarCubicPartFirst]
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_right hb₂ (by positivity),
    by
      dsimp only [scalarCubicPartSecond]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)⟩

theorem scalarResidual_eq_cubic_add_fourth (f : ℝ → ℝ) (z y : ℝ) :
    f y - scalarTaylorPolynomial f 2 z y = scalarCubicPart f z y + scalarFourthTail f z y := by
  rw [scalarFourthTail, scalarTaylorPolynomial_succ f 2 z y]
  norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  dsimp only [scalarCubicPart]
  ring

def jointCubicJet (f : ℝ → ℝ) (z : ℝ) (A A₁ A₂ : Fin 3 → ℝ → ℝ) : JointGaussianJet :=
  jointAffineRemainderJet (scalarCubicPart f z) (scalarCubicPartFirst f z)
    (scalarCubicPartSecond f z) A A₁ A₂

def jointFourthTailJet (f : ℝ → ℝ) (z : ℝ) (A A₁ A₂ : Fin 3 → ℝ → ℝ) : JointGaussianJet :=
  jointAffineRemainderJet (scalarFourthTail f z) (scalarFourthTailFirst f z)
    (scalarFourthTailSecond f z) A A₁ A₂

def JointAffineRegularOn (A A₁ A₂ : Fin 3 → ℝ → ℝ) (U : Set ℝ) : Prop :=
  ∀ k ∈ U, ∀ i, HasDerivAt (A i) (A₁ i k) k ∧ HasDerivAt (A₁ i) (A₂ i k) k

def JointAffineScaleBound (A A₁ A₂ : Fin 3 → ℝ → ℝ) (U : Set ℝ) (z M ρ : ℝ) : Prop :=
  ∀ k ∈ U, ∀ i, |A i k - (if i = 0 then z else 0)| ≤ M * ρ ∧
    |A₁ i k| ≤ M * ρ ∧ |A₂ i k| ≤ M * ρ

theorem jointCubicJet_regular (f : ℝ → ℝ) (z : ℝ)
    {A A₁ A₂ : Fin 3 → ℝ → ℝ} {U : Set ℝ} (hA : JointAffineRegularOn A A₁ A₂ U) :
    (jointCubicJet f z A A₁ A₂).RegularOn U := by
  exact jointAffineRemainderJet_regular
    ⟨by unfold scalarCubicPart; fun_prop,
      by unfold scalarCubicPartFirst; fun_prop,
      by unfold scalarCubicPartSecond; fun_prop⟩ (scalarCubicPart_derivatives f z) hA

theorem jointCubicJet_bound {f : ℝ → ℝ} {B M ρ z : ℝ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hρ : 0 ≤ ρ) (hb : |iteratedDeriv 3 f z| ≤ B)
    {A A₁ A₂ : Fin 3 → ℝ → ℝ} {U : Set ℝ}
    (hA : JointAffineScaleBound A A₁ A₂ U z M ρ) :
    (jointCubicJet f z A A₁ A₂).PolynomialBound U 3 (2 * B * M ^ 3 * ρ ^ 3) := by
  exact jointAffineRemainderJet_bound (n := 1) hB hM hρ
    (fun y => by simpa only [pow_one] using scalarCubicPart_jet_bounds hB hb y) hA

theorem jointFourthTailJet_regular {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (z : ℝ)
    {A A₁ A₂ : Fin 3 → ℝ → ℝ} {U : Set ℝ} (hA : JointAffineRegularOn A A₁ A₂ U) :
    (jointFourthTailJet f z A A₁ A₂).RegularOn U := by
  have hf₁ := contDiff_deriv_infty hf
  have hf₂ : ContDiff ℝ ∞ (iteratedDeriv 2 f) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      contDiff_deriv_infty hf₁
  exact jointAffineRemainderJet_regular
    ⟨hf.continuous.sub (scalarTaylorPolynomial_contDiff f 3 z).continuous,
      hf₁.continuous.sub (scalarTaylorPolynomial_contDiff (deriv f) 2 z).continuous,
      hf₂.continuous.sub (scalarTaylorPolynomial_contDiff (iteratedDeriv 2 f) 1 z).continuous⟩
    (scalarFourthTail_derivatives hf z) hA

theorem jointFourthTailJet_bound {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {B M ρ z : ℝ}
    (hB : 0 ≤ B) (hM : 0 ≤ M) (hρ : 0 ≤ ρ) (hb : ∀ y, |iteratedDeriv 4 f y| ≤ B)
    {A A₁ A₂ : Fin 3 → ℝ → ℝ} {U : Set ℝ}
    (hA : JointAffineScaleBound A A₁ A₂ U z M ρ) :
    (jointFourthTailJet f z A A₁ A₂).PolynomialBound U 4 (2 * B * M ^ 4 * ρ ^ 4) :=
  jointAffineRemainderJet_bound (n := 2) hB hM hρ (scalarFourthTail_jet_bounds hf hB hb z) hA

def jointTailProductJet (f : ℝ → ℝ) (z : ℝ)
    (A A₁ A₂ B B₁ B₂ : Fin 3 → ℝ → ℝ) : JointGaussianJet :=
  (((jointCubicJet f z A A₁ A₂).mul (jointFourthTailJet f z B B₁ B₂)).add
    ((jointFourthTailJet f z A A₁ A₂).mul (jointCubicJet f z B B₁ B₂))).add
    ((jointFourthTailJet f z A A₁ A₂).mul (jointFourthTailJet f z B B₁ B₂))

theorem jointTailProductJet_regular {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (z : ℝ)
    {A A₁ A₂ B B₁ B₂ : Fin 3 → ℝ → ℝ} {U : Set ℝ}
    (hA : JointAffineRegularOn A A₁ A₂ U) (hB : JointAffineRegularOn B B₁ B₂ U) :
    (jointTailProductJet f z A A₁ A₂ B B₁ B₂).RegularOn U :=
  (((jointCubicJet_regular f z hA).mul (jointFourthTailJet_regular hf z hB)).add
    ((jointFourthTailJet_regular hf z hA).mul (jointCubicJet_regular f z hB))).add
    ((jointFourthTailJet_regular hf z hA).mul (jointFourthTailJet_regular hf z hB))

theorem jointTailProductJet_bound {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {J M ρ z : ℝ}
    (hJ : 0 ≤ J) (hM : 0 ≤ M) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (h₃ : |iteratedDeriv 3 f z| ≤ J) (h₄ : ∀ y, |iteratedDeriv 4 f y| ≤ J)
    {A A₁ A₂ B B₁ B₂ : Fin 3 → ℝ → ℝ} {U : Set ℝ}
    (hA : JointAffineScaleBound A A₁ A₂ U z M ρ)
    (hB : JointAffineScaleBound B B₁ B₂ U z M ρ) :
    (jointTailProductJet f z A A₁ A₂ B B₁ B₂).PolynomialBound U 8
      (16 * J ^ 2 * (2 * M ^ 7 + M ^ 8) * ρ ^ 7) := by
  have hCA := jointCubicJet_bound hJ hM hρ h₃ hA
  have hCB := jointCubicJet_bound hJ hM hρ h₃ hB
  have hTA := jointFourthTailJet_bound hf hJ hM hρ h₄ hA
  have hTB := jointFourthTailJet_bound hf hJ hM hρ h₄ hB
  have hCT := (hCA.mul (by positivity) (by positivity) hTB).mono
    (by positivity) (by norm_num : 3 + 4 ≤ 8) (le_refl _)
  have hTC := (hTA.mul (by positivity) (by positivity) hCB).mono
    (by positivity) (by norm_num : 4 + 3 ≤ 8) (le_refl _)
  have hTT := hTA.mul (by positivity) (by positivity) hTB
  have H := (hCT.add hTC).add hTT
  apply H.mono (by positivity) le_rfl
  have hpow : ρ ^ 8 ≤ ρ ^ 7 := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hρ 7) hρ₁
  calc
    _ = 32 * J ^ 2 * M ^ 7 * ρ ^ 7 + 16 * J ^ 2 * M ^ 8 * ρ ^ 8 := by ring
    _ ≤ 32 * J ^ 2 * M ^ 7 * ρ ^ 7 + 16 * J ^ 2 * M ^ 8 * ρ ^ 7 := by gcongr
    _ = _ := by ring

def jointTaylorTailError (f : ℝ → ℝ) (z : ℝ)
    (A B : Fin 3 → ℝ → ℝ) : ℝ → ℝ :=
  jointGaussianIntegral (fun k g t =>
    (f (jointGaussianAffine A k g t) - scalarTaylorPolynomial f 2 z (jointGaussianAffine A k g t)) *
      (f (jointGaussianAffine B k g t) - scalarTaylorPolynomial f 2 z (jointGaussianAffine B k g t)) -
    scalarCubicPart f z (jointGaussianAffine A k g t) *
      scalarCubicPart f z (jointGaussianAffine B k g t))

theorem jointTaylorTailError_eq (f : ℝ → ℝ) (z : ℝ)
    (A A₁ A₂ B B₁ B₂ : Fin 3 → ℝ → ℝ) :
    jointTaylorTailError f z A B =
      jointGaussianIntegral (jointTailProductJet f z A A₁ A₂ B B₁ B₂).value := by
  apply congrArg jointGaussianIntegral
  funext k g t
  rw [scalarResidual_eq_cubic_add_fourth, scalarResidual_eq_cubic_add_fourth]
  dsimp only [jointTailProductJet, JointGaussianJet.add, JointGaussianJet.mul,
    jointCubicJet, jointFourthTailJet, jointAffineRemainderJet]
  ring

theorem jointTaylorTailError_control {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {J M h z : ℝ} (hJ : 0 ≤ J) (hM : 0 ≤ M) (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (h₃ : |iteratedDeriv 3 f z| ≤ J) (h₄ : ∀ y, |iteratedDeriv 4 f y| ≤ J)
    {A A₁ A₂ B B₁ B₂ : Fin 3 → ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hA : JointAffineRegularOn A A₁ A₂ U) (hB : JointAffineRegularOn B B₁ B₂ U)
    (hpA : JointAffineScaleBound A A₁ A₂ U z M (Real.sqrt h))
    (hpB : JointAffineScaleBound B B₁ B₂ U z M (Real.sqrt h)) :
    ∃ f₁ f₂ : ℝ → ℝ, ∀ k ∈ U,
      HasDerivAt (jointTaylorTailError f z A B) (f₁ k) k ∧ HasDerivAt f₁ (f₂ k) k ∧
      |jointTaylorTailError f z A B k| ≤
        (16 * J ^ 2 * (2 * M ^ 7 + M ^ 8) *
          (∫ g, gaussianPolynomialWeight 8 g ∂gaussianReal 0 1) ^ 2) * Real.sqrt h * h ^ 3 ∧
      |f₁ k| ≤ (16 * J ^ 2 * (2 * M ^ 7 + M ^ 8) *
          (∫ g, gaussianPolynomialWeight 8 g ∂gaussianReal 0 1) ^ 2) * Real.sqrt h * h ^ 3 ∧
      |f₂ k| ≤ (16 * J ^ 2 * (2 * M ^ 7 + M ^ 8) *
          (∫ g, gaussianPolynomialWeight 8 g ∂gaussianReal 0 1) ^ 2) * Real.sqrt h * h ^ 3 := by
  let F := jointTailProductJet f z A A₁ A₂ B B₁ B₂
  have hF : F.RegularOn U := jointTailProductJet_regular hf z hA hB
  have hb : F.PolynomialBound U 8
      (16 * J ^ 2 * (2 * M ^ 7 + M ^ 8) * Real.sqrt h ^ 7) :=
    jointTailProductJet_bound hf hJ hM (Real.sqrt_nonneg h)
      (Real.sqrt_le_one.mpr hh₁) h₃ h₄ hpA hpB
  have he := jointTaylorTailError_eq f z A A₁ A₂ B B₁ B₂
  have hs : Real.sqrt h ^ 7 = Real.sqrt h * h ^ 3 := by
    calc
      _ = Real.sqrt h * (Real.sqrt h ^ 2) ^ 3 := by ring
      _ = _ := by rw [Real.sq_sqrt hh]
  have hen : (16 * J ^ 2 * (2 * M ^ 7 + M ^ 8) * Real.sqrt h ^ 7) *
      (∫ g, gaussianPolynomialWeight 8 g ∂gaussianReal 0 1) ^ 2 =
      (16 * J ^ 2 * (2 * M ^ 7 + M ^ 8) *
        (∫ g, gaussianPolynomialWeight 8 g ∂gaussianReal 0 1) ^ 2) * Real.sqrt h * h ^ 3 := by
    rw [hs]
    ring
  refine ⟨jointGaussianIntegral F.first, jointGaussianIntegral F.second, ?_⟩
  intro k hk
  have hd := JointGaussianJet.integral_derivatives hU hF hb k hk
  have hbound := JointGaussianJet.integral_bounds hb hk
  rw [hen] at hbound
  exact ⟨by simpa only [he] using hd.1, hd.2,
    by simpa only [he] using hbound.1, hbound.2.1, hbound.2.2⟩

theorem scalarData_jointTaylorTailError_control {β : ℝ} (D : ScalarData β)
    (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ s h z : ℝ,
      0 ≤ h → h ≤ 1 → s + 4 * h ∈ Icc (0 : ℝ) 1 →
      ∀ (U : Set ℝ), IsOpen U → ∀ A A₁ A₂ B B₁ B₂ : Fin 3 → ℝ → ℝ,
      JointAffineRegularOn A A₁ A₂ U → JointAffineRegularOn B B₁ B₂ U →
      JointAffineScaleBound A A₁ A₂ U z M (Real.sqrt h) →
      JointAffineScaleBound B B₁ B₂ U z M (Real.sqrt h) →
      ∃ f₁ f₂ : ℝ → ℝ, ∀ k ∈ U,
        HasDerivAt (jointTaylorTailError (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)) z A B)
          (f₁ k) k ∧ HasDerivAt f₁ (f₂ k) k ∧
        |jointTaylorTailError (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)) z A B k| ≤
          C * Real.sqrt h * h ^ 3 ∧
        |f₁ k| ≤ C * Real.sqrt h * h ^ 3 ∧ |f₂ k| ≤ C * Real.sqrt h * h ^ 3 := by
  let J := scalarTerminalJetBound D 4 + 1
  have hJ : 0 < J := by dsimp only [J]; linarith [scalarTerminalJetBound_nonneg D 4]
  let K := 16 * J ^ 2 * (2 * M ^ 7 + M ^ 8) *
    (∫ g, gaussianPolynomialWeight 8 g ∂gaussianReal 0 1) ^ 2
  refine ⟨K + 1, by dsimp only [K]; positivity, ?_⟩
  intro s h z hh hh₁ ht U hU A A₁ A₂ B B₁ B₂ hA hB hpA hpB
  let f := Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)
  have hj (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (y : ℝ) :
      |iteratedDeriv j f y| ≤ J :=
    (scalarData_jet_le D hj₁ hj₄ ht y).trans (by dsimp only [J]; linarith)
  obtain ⟨f₁, f₂, H⟩ := jointTaylorTailError_control (scalarData_phi_contDiff D ht)
    hJ.le hM hh hh₁ (hj 3 (by norm_num) (by norm_num) z)
    (hj 4 (by norm_num) le_rfl) hU hA hB hpA hpB
  have hen : K * Real.sqrt h * h ^ 3 ≤ (K + 1) * Real.sqrt h * h ^ 3 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : K ≤ K + 1) (Real.sqrt_nonneg h))
      (pow_nonneg hh 3)
  refine ⟨f₁, f₂, ?_⟩
  intro k hk
  have Hk := H k hk
  exact ⟨Hk.1, Hk.2.1, Hk.2.2.1.trans hen, Hk.2.2.2.1.trans hen, Hk.2.2.2.2.trans hen⟩

end SKBarriers2.Corner
