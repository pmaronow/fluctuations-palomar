module

public import SKBarriers2.Corner.FrozenDiff

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def epsilonSuffixRemainder (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) (ε : ℝ) (x : Vec3) : ℝ :=
  epsilonChain l Q K ε x - (riccatiRecursion l Q).value x

theorem epsilonSuffixRemainder_nil (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    (ε : ℝ) (x : Vec3) : epsilonSuffixRemainder [] Q K ε x = ε * K x := by
  unfold epsilonSuffixRemainder epsilonChain vectorIncrementChain riccatiRecursion
  ring

theorem epsilonSuffixRemainder_zero (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) (hQ : RiccatiAdmissible l Q) (x : Vec3) :
    epsilonSuffixRemainder l Q K 0 x = 0 := by
  rw [epsilonSuffixRemainder, epsilonChain_zero l Q K hQ]
  exact sub_self _

theorem QuadraticTerminal.vectorStep_add_correction (Q : QuadraticTerminal)
    (m : ℝ) (v x : Vec3) (R : Vec3 → ℝ) (hm : m ≠ 0)
    (hD : 0 < Q.precision m v)
    (hR : 0 < quadraticAverage Q m v (fun y => Real.exp (m * R y)) x) :
    vectorStep m v (fun y => Q.value y + R y) x =
      (Q.update m v).value x +
        Real.log (quadraticAverage Q m v (fun y => Real.exp (m * R y)) x) / m := by
  let : IsProbabilityMeasure (quadraticGaussian (Q.precision m v) (m * Q.slope v x)) := by
    unfold quadraticGaussian
    infer_instance
  have he (t : ℝ) : Real.exp (m * (Q.value (x + t • v) + R (x + t • v))) =
      Real.exp (m * Q.value (x + t • v)) * Real.exp (m * R (x + t • v)) := by
    rw [mul_add, Real.exp_add]
  have hpartition : (∫ t, Real.exp (m * Q.value (x + t • v)) ∂gaussianReal 0 1) =
      quadraticPartition Q m v x := by
    simpa only [mul_one, quadraticAverage, integral_const, probReal_univ, smul_eq_mul]
      using quadratic_weighted_moment Q m v x hD (fun _ => 1)
  have hquadratic : Real.log (quadraticPartition Q m v x) / m = (Q.update m v).value x := by
    rw [← hpartition]
    simpa only [vectorStep, gaussianStep, ite_eq_right hm, positiveGaussianLogStep]
      using congrFun (Q.vectorStep_value m v hm hD) x
  simp only [vectorStep, gaussianStep, ite_eq_right hm, positiveGaussianLogStep, he]
  rw [quadratic_weighted_moment Q m v x hD (fun y => Real.exp (m * R y)),
    Real.log_mul (ne_of_gt (quadraticPartition_pos Q m v x hD)) (ne_of_gt hR), add_div,
    hquadratic]

theorem epsilonSuffixRemainder_cons (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) (u : ℝ × Vec3) (ε : ℝ) (x : Vec3) (hm : u.1 ≠ 0)
    (hD : 0 < (riccatiRecursion l Q).precision u.1 u.2)
    (hR : 0 < quadraticAverage (riccatiRecursion l Q) u.1 u.2
      (fun y => Real.exp (u.1 * epsilonSuffixRemainder l Q K ε y)) x) :
    epsilonSuffixRemainder (u :: l) Q K ε x =
      Real.log (quadraticAverage (riccatiRecursion l Q) u.1 u.2
        (fun y => Real.exp (u.1 * epsilonSuffixRemainder l Q K ε y)) x) / u.1 := by
  have he : epsilonChain (u :: l) Q K ε x =
      vectorStep u.1 u.2 (fun y => (riccatiRecursion l Q).value y +
        epsilonSuffixRemainder l Q K ε y) x := by
    change vectorStep u.1 u.2 (epsilonChain l Q K ε) x = _
    apply congrArg (fun f => vectorStep u.1 u.2 f x)
    funext y
    unfold epsilonSuffixRemainder
    ring
  rw [epsilonSuffixRemainder, he,
    QuadraticTerminal.vectorStep_add_correction _ _ _ _ _ hm hD hR]
  simp only [riccatiRecursion]
  ring

theorem quadraticPerturbation_linear (ε : ℝ) :
    quadraticPerturbation 1 0 0 0 (fun t => t) ε = ε ^ 2 / 2 := by
  have he : quadraticPerturbation 1 0 0 0 (fun t => t) ε =
      gaussianStep 1 (fun p : Unit × ℝ => 0 + ε * p.2 + 0 / 2 * p.2 ^ 2) () := by
    simp only [quadraticPerturbation, zero_mul, zero_div, zero_add, add_zero]
  rw [he, gaussianStep_quadratic (by norm_num : (1 : ℝ) ≠ 0) (by norm_num)]
  norm_num

theorem quadraticPerturbation_not_affine :
    ¬ ∃ R : ℝ, ∀ ε : ℝ, quadraticPerturbation 1 0 0 0 (fun t => t) ε =
      quadraticPerturbation 1 0 0 0 (fun t => t) 0 + ε * R := by
  rintro ⟨R, hR⟩
  have hp := hR 1
  have hm := hR (-1)
  simp only [quadraticPerturbation_linear] at hp hm
  norm_num at hp hm
  linarith

namespace NonlinearEpsilonStep

def weight (m : ℝ) (F : ℝ → ℝ → ℝ) (ε t : ℝ) : ℝ := Real.exp (m * F ε t)

def weightFirst (m : ℝ) (F F₁ : ℝ → ℝ → ℝ) (ε t : ℝ) : ℝ :=
  m * (weight m F ε t * F₁ ε t)

def weightSecond (m : ℝ) (F F₁ F₂ : ℝ → ℝ → ℝ) (ε t : ℝ) : ℝ :=
  m * (weight m F ε t * (F₂ ε t + m * F₁ ε t ^ 2))

def weightThird (m : ℝ) (F F₁ F₂ F₃ : ℝ → ℝ → ℝ) (ε t : ℝ) : ℝ :=
  m * (weight m F ε t *
    (F₃ ε t + 3 * m * F₁ ε t * F₂ ε t + m ^ 2 * F₁ ε t ^ 3))

theorem weight_hasDerivAt {m ε t : ℝ} {F F₁ : ℝ → ℝ → ℝ}
    (hF : HasDerivAt (fun e => F e t) (F₁ ε t) ε) :
    HasDerivAt (fun e => weight m F e t) (weightFirst m F F₁ ε t) ε := by
  change HasDerivAt (fun e => Real.exp (m * F e t)) _ ε
  convert (hF.const_mul m).exp using 1
  unfold weightFirst weight
  ring

theorem weightFirst_hasDerivAt {m ε t : ℝ} {F F₁ F₂ : ℝ → ℝ → ℝ}
    (hF : HasDerivAt (fun e => F e t) (F₁ ε t) ε)
    (hF₁ : HasDerivAt (fun e => F₁ e t) (F₂ ε t) ε) :
    HasDerivAt (fun e => weightFirst m F F₁ e t) (weightSecond m F F₁ F₂ ε t) ε := by
  unfold weightFirst
  convert (((weight_hasDerivAt (m := m) hF).mul hF₁).const_mul m) using 1
  unfold weightFirst weightSecond
  ring

theorem weightSecond_hasDerivAt {m ε t : ℝ} {F F₁ F₂ F₃ : ℝ → ℝ → ℝ}
    (hF : HasDerivAt (fun e => F e t) (F₁ ε t) ε)
    (hF₁ : HasDerivAt (fun e => F₁ e t) (F₂ ε t) ε)
    (hF₂ : HasDerivAt (fun e => F₂ e t) (F₃ ε t) ε) :
    HasDerivAt (fun e => weightSecond m F F₁ F₂ e t)
      (weightThird m F F₁ F₂ F₃ ε t) ε := by
  unfold weightSecond
  convert (((weight_hasDerivAt (m := m) hF).mul
    (hF₂.add ((hF₁.pow 2).const_mul m))).const_mul m) using 1
  simp only [weightFirst, weightThird, Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat,
    Nat.reduceSub, pow_one]
  ring

end NonlinearEpsilonStep

theorem integrable_polynomial_exp_square {B : ℝ} (hB : 0 ≤ B) (hsmall : 2 * B < 1)
    (A : ℝ) (p : ℕ) :
    Integrable (fun t : ℝ => (1 + t ^ 2) ^ p * Real.exp (A + B * t ^ 2))
      (gaussianReal 0 1) := by
  have hX : B ∈ interior (integrableExpSet (fun t : ℝ => 1 + t ^ 2) (gaussianReal 0 1)) := by
    have H := quadraticGrowth_mem_interior_at (D := 1) (C := 1) (ε := B)
      (by norm_num) (by norm_num) 0 1 (K := fun t : ℝ => 1 + t ^ 2) (by fun_prop)
      (fun t => by rw [abs_of_nonneg (by positivity : 0 ≤ 1 + t ^ 2)]; ring_nf; rfl)
      (by simpa only [abs_of_nonneg hB, mul_one] using hsmall)
    simpa only [quadraticGaussian, div_one, inv_one, Real.toNNReal_one] using H
  have hi := (integrable_pow_mul_exp_of_mem_interior_integrableExpSet hX p).const_mul
    (Real.exp (A - B))
  convert hi using 1
  ext t
  rw [← mul_assoc, mul_comm (Real.exp (A - B)), mul_assoc, ← Real.exp_add]
  congr 2
  ring

namespace NonlinearEpsilonStep

theorem integral_controls_of_polynomial_bounds
    {m A B M : ℝ} {p : ℕ} {U : Set ℝ} (hU : IsOpen U)
    {F F₁ F₂ F₃ : ℝ → ℝ → ℝ}
    (hB : 0 ≤ B) (hsmall : 2 * B < 1) (hM : 0 ≤ M)
    (hc : ∀ e ∈ U, Continuous (F e) ∧ Continuous (F₁ e) ∧
      Continuous (F₂ e) ∧ Continuous (F₃ e))
    (hd : ∀ e ∈ U, ∀ t, HasDerivAt (fun a => F a t) (F₁ e t) e ∧
      HasDerivAt (fun a => F₁ a t) (F₂ e t) e ∧
      HasDerivAt (fun a => F₂ a t) (F₃ e t) e)
    (hval : ∀ e ∈ U, ∀ t, m * F e t ≤ A + B * t ^ 2)
    (hjets : ∀ e ∈ U, ∀ t, |F₁ e t| ≤ M * (1 + t ^ 2) ^ p ∧
      |F₂ e t| ≤ M * (1 + t ^ 2) ^ p ∧ |F₃ e t| ≤ M * (1 + t ^ 2) ^ p)
    {ε : ℝ} (hε : ε ∈ U) :
    IntegralDerivativeControl (gaussianReal 0 1) (weight m F) (weightFirst m F F₁) ε ∧
      IntegralDerivativeControl (gaussianReal 0 1) (weightFirst m F F₁)
        (weightSecond m F F₁ F₂) ε ∧
      IntegralDerivativeControl (gaussianReal 0 1) (weightSecond m F F₁ F₂)
        (weightThird m F F₁ F₂ F₃) ε := by
  let P : ℝ → ℝ := fun t => (1 + t ^ 2) ^ p
  let W : ℝ → ℝ := fun t => Real.exp (A + B * t ^ 2)
  let b₁ : ℝ → ℝ := fun t => |m| * (W t * (M * P t))
  let b₂ : ℝ → ℝ := fun t => |m| * (W t * (M * P t + |m| * (M * P t) ^ 2))
  let b₃ : ℝ → ℝ := fun t => |m| * (W t *
    (M * P t + 3 * |m| * (M * P t) ^ 2 + m ^ 2 * (M * P t) ^ 3))
  have hP (t : ℝ) : 0 ≤ P t := by dsimp only [P]; positivity
  have hW (t : ℝ) : 0 ≤ W t := (Real.exp_pos _).le
  have hWP (n : ℕ) : Integrable (fun t => W t * P t ^ n) (gaussianReal 0 1) := by
    have H := integrable_polynomial_exp_square hB hsmall A (p * n)
    convert H using 1
    ext t
    simp only [P, W, ← pow_mul]
    ring
  have hb₁ : Integrable b₁ (gaussianReal 0 1) := by
    convert (hWP 1).const_mul (|m| * M) using 1
    ext t
    dsimp only [b₁]
    ring
  have hb₂ : Integrable b₂ (gaussianReal 0 1) := by
    convert ((hWP 1).const_mul (|m| * M)).add
      ((hWP 2).const_mul (|m| ^ 2 * M ^ 2)) using 1
    ext t
    dsimp only [b₂, Pi.add_apply]
    ring
  have hb₃ : Integrable b₃ (gaussianReal 0 1) := by
    convert (((hWP 1).const_mul (|m| * M)).add
      ((hWP 2).const_mul (3 * |m| ^ 2 * M ^ 2))).add
      ((hWP 3).const_mul (|m| * m ^ 2 * M ^ 3)) using 1
    ext t
    dsimp only [b₃, Pi.add_apply]
    ring
  have hc₀ (e : ℝ) (he : e ∈ U) : Continuous (weight m F e) := by
    exact Real.continuous_exp.comp (continuous_const.mul (hc e he).1)
  have hc₁ (e : ℝ) (he : e ∈ U) : Continuous (weightFirst m F F₁ e) := by
    exact continuous_const.mul ((hc₀ e he).mul (hc e he).2.1)
  have hc₂ (e : ℝ) (he : e ∈ U) : Continuous (weightSecond m F F₁ F₂ e) := by
    exact continuous_const.mul ((hc₀ e he).mul
      ((hc e he).2.2.1.add (continuous_const.mul ((hc e he).2.1.pow 2))))
  have hc₃ (e : ℝ) (he : e ∈ U) : Continuous (weightThird m F F₁ F₂ F₃ e) := by
    exact continuous_const.mul ((hc₀ e he).mul
      (((hc e he).2.2.2.add (((continuous_const.mul (hc e he).2.1).mul (hc e he).2.2.1))).add
        (continuous_const.mul ((hc e he).2.1.pow 3))))
  have hbound₀ (e : ℝ) (he : e ∈ U) (t : ℝ) : ‖weight m F e t‖ ≤ W t := by
    rw [Real.norm_eq_abs, weight, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (hval e he t)
  have hbound₁ (e : ℝ) (he : e ∈ U) (t : ℝ) : ‖weightFirst m F F₁ e t‖ ≤ b₁ t := by
    rw [Real.norm_eq_abs, weightFirst, abs_mul, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg m)
    exact mul_le_mul (hbound₀ e he t) (hjets e he t).1 (abs_nonneg _) (hW t)
  have hbound₂ (e : ℝ) (he : e ∈ U) (t : ℝ) : ‖weightSecond m F F₁ F₂ e t‖ ≤ b₂ t := by
    rw [Real.norm_eq_abs, weightSecond, abs_mul, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg m)
    apply mul_le_mul (hbound₀ e he t) _ (abs_nonneg _) (hW t)
    calc
      _ ≤ |F₂ e t| + |m * F₁ e t ^ 2| := abs_add_le _ _
      _ = |F₂ e t| + |m| * |F₁ e t| ^ 2 := by rw [abs_mul, abs_pow]
      _ ≤ M * P t + |m| * (M * P t) ^ 2 := by
        gcongr
        · exact (hjets e he t).2.1
        · exact (hjets e he t).1
  have hbound₃ (e : ℝ) (he : e ∈ U) (t : ℝ) : ‖weightThird m F F₁ F₂ F₃ e t‖ ≤ b₃ t := by
    rw [Real.norm_eq_abs, weightThird, abs_mul, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg m)
    apply mul_le_mul (hbound₀ e he t) _ (abs_nonneg _) (hW t)
    calc
      _ ≤ |F₃ e t| + |3 * m * F₁ e t * F₂ e t| + |m ^ 2 * F₁ e t ^ 3| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))
      _ = |F₃ e t| + 3 * |m| * |F₁ e t| * |F₂ e t| + m ^ 2 * |F₁ e t| ^ 3 := by
        simp only [abs_mul, abs_pow, sq_abs]
        norm_num
      _ ≤ M * P t + 3 * |m| * (M * P t) * (M * P t) + m ^ 2 * (M * P t) ^ 3 := by
        gcongr
        · exact (hjets e he t).2.2
        · exact (hjets e he t).1
        · exact (hjets e he t).2.1
        · exact (hjets e he t).1
      _ = _ := by ring
  have hi₀ : Integrable (weight m F ε) (gaussianReal 0 1) :=
    (integrable_polynomial_exp_square hB hsmall A 0).mono'
      (hc₀ ε hε).aestronglyMeasurable (ae_of_all _ (by simpa only [pow_zero, one_mul] using hbound₀ ε hε))
  have hi₁ : Integrable (weightFirst m F F₁ ε) (gaussianReal 0 1) :=
    hb₁.mono' (hc₁ ε hε).aestronglyMeasurable (ae_of_all _ (hbound₁ ε hε))
  have hi₂ : Integrable (weightSecond m F F₁ F₂ ε) (gaussianReal 0 1) :=
    hb₂.mono' (hc₂ ε hε).aestronglyMeasurable (ae_of_all _ (hbound₂ ε hε))
  refine ⟨⟨U, hU.mem_nhds hε, b₁,
      Filter.mem_of_superset (hU.mem_nhds hε) (fun e he => (hc₀ e he).aestronglyMeasurable),
      hi₀, (hc₁ ε hε).aestronglyMeasurable, hb₁, ae_of_all _ (fun t e he => hbound₁ e he t),
      ae_of_all _ (fun t e he => weight_hasDerivAt (hd e he t).1)⟩,
    ⟨U, hU.mem_nhds hε, b₂,
      Filter.mem_of_superset (hU.mem_nhds hε) (fun e he => (hc₁ e he).aestronglyMeasurable),
      hi₁, (hc₂ ε hε).aestronglyMeasurable, hb₂, ae_of_all _ (fun t e he => hbound₂ e he t),
      ae_of_all _ (fun t e he => weightFirst_hasDerivAt (hd e he t).1 (hd e he t).2.1)⟩,
    ⟨U, hU.mem_nhds hε, b₃,
      Filter.mem_of_superset (hU.mem_nhds hε) (fun e he => (hc₂ e he).aestronglyMeasurable),
      hi₂, (hc₃ ε hε).aestronglyMeasurable, hb₃, ae_of_all _ (fun t e he => hbound₃ e he t),
      ae_of_all _ (fun t e he => weightSecond_hasDerivAt (hd e he t).1
        (hd e he t).2.1 (hd e he t).2.2)⟩⟩

end NonlinearEpsilonStep

theorem logPartition_third_of_tower {Z Z₁ Z₂ Z₃ : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) {m ε : ℝ} (hm : m ≠ 0) (hε : ε ∈ U)
    (h₀ : ∀ e ∈ U, HasDerivAt Z (Z₁ e) e)
    (h₁ : ∀ e ∈ U, HasDerivAt Z₁ (Z₂ e) e)
    (h₂ : ∀ e ∈ U, HasDerivAt Z₂ (Z₃ e) e) (hpos : Z ε ≠ 0) :
    HasDerivAt (iteratedDeriv 2 (fun e => Real.log (Z e) / m))
      ((Z₃ ε * Z ε ^ 2 - 3 * Z₂ ε * Z₁ ε * Z ε + 2 * Z₁ ε ^ 3) / Z ε ^ 3 / m) ε := by
  have hnear : ∀ᶠ e in 𝓝 ε, e ∈ U := hU.mem_nhds hε
  have hn : ∀ᶠ e in 𝓝 ε, Z e ≠ 0 := (h₀ ε hε).continuousAt.eventually_ne hpos
  have hderiv₁ (e : ℝ) (he : e ∈ U) : HasDerivAt (deriv Z) (Z₂ e) e := by
    have heq : deriv Z =ᶠ[𝓝 e] Z₁ := by
      filter_upwards [hU.mem_nhds he] with a ha
      exact (h₀ a ha).deriv
    exact (h₁ e he).congr_of_eventuallyEq heq
  have he₂ : iteratedDeriv 2 (fun e => Real.log (Z e) / m) =ᶠ[𝓝 ε]
      (fun e => (Z₂ e * Z e - Z₁ e ^ 2) / Z e ^ 2 / m) := by
    filter_upwards [hnear, hn] with e he hne
    have hdZ : ∀ᶠ a in 𝓝 e, DifferentiableAt ℝ Z a := by
      filter_upwards [hU.mem_nhds he] with a ha
      exact (h₀ a ha).differentiableAt
    have H := (logPartition_second (m := m) (h₀ e he) (hderiv₁ e he) hdZ hne).deriv
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using H
  have hd := ((((h₂ ε hε).mul (h₀ ε hε)).sub ((h₁ ε hε).pow 2)).div
    ((h₀ ε hε).pow 2) (pow_ne_zero 2 hpos)).div_const m
  convert hd.congr_of_eventuallyEq he₂ using 1
  dsimp only [Pi.pow_apply, Pi.sub_apply, Pi.mul_apply]
  field_simp [hm, hpos]
  ring

theorem logPartition_third_of_moments {Z Z₁ Z₂ Z₃ : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) {m ε a b c d e f : ℝ} (hm : m ≠ 0) (hε : ε ∈ U)
    (h₀ : ∀ t ∈ U, HasDerivAt Z (Z₁ t) t)
    (h₁ : ∀ t ∈ U, HasDerivAt Z₁ (Z₂ t) t)
    (h₂ : ∀ t ∈ U, HasDerivAt Z₂ (Z₃ t) t) (hpos : Z ε ≠ 0)
    (ha : Z₁ ε = m * (Z ε * a))
    (hb : Z₂ ε = m * (Z ε * (b + m * c)))
    (hc : Z₃ ε = m * (Z ε * (d + 3 * m * e + m ^ 2 * f))) :
    HasDerivAt (iteratedDeriv 2 (fun t => Real.log (Z t) / m))
      (d + 3 * m * (e - a * b) + m ^ 2 * (f - 3 * a * c + 2 * a ^ 3)) ε := by
  have H := logPartition_third_of_tower hU hm hε h₀ h₁ h₂ hpos
  rw [ha, hb, hc] at H
  convert H using 1
  field_simp [hm, hpos]
  ring

theorem logPartition_regular_of_tower {Z Z₁ Z₂ Z₃ : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) {m ε : ℝ} (hm : m ≠ 0) (hε : ε ∈ U)
    (h₀ : ∀ e ∈ U, HasDerivAt Z (Z₁ e) e)
    (h₁ : ∀ e ∈ U, HasDerivAt Z₁ (Z₂ e) e)
    (h₂ : ∀ e ∈ U, HasDerivAt Z₂ (Z₃ e) e) (hpos : Z ε ≠ 0) :
    let θ := fun e => Real.log (Z e) / m
    HasDerivAt θ (deriv θ ε) ε ∧
      HasDerivAt (deriv θ) (iteratedDeriv 2 θ ε) ε ∧
      HasDerivAt (iteratedDeriv 2 θ) (iteratedDeriv 3 θ ε) ε := by
  have hdZ : ∀ᶠ e in 𝓝 ε, DifferentiableAt ℝ Z e := by
    filter_upwards [hU.mem_nhds hε] with e he
    exact (h₀ e he).differentiableAt
  have heq : deriv Z =ᶠ[𝓝 ε] Z₁ := by
    filter_upwards [hU.mem_nhds hε] with e he
    exact (h₀ e he).deriv
  have hd₁ := logPartition_hasDerivAt (m := m) (h₀ ε hε) hpos
  have hd₂ := logPartition_second (m := m) (h₀ ε hε)
    ((h₁ ε hε).congr_of_eventuallyEq heq) hdZ hpos
  have hd₃ := logPartition_third_of_tower hU hm hε h₀ h₁ h₂ hpos
  refine ⟨hd₁.differentiableAt.hasDerivAt, ?_, ?_⟩
  · simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      hd₂.differentiableAt.hasDerivAt
  · simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      hd₃.differentiableAt.hasDerivAt

theorem IntegralDerivativeControl.integrable {μ : Measure ℝ}
    {F F₁ : ℝ → ℝ → ℝ} {ε : ℝ} (H : IntegralDerivativeControl μ F F₁ ε) :
    Integrable (F ε) μ := by
  rcases H with ⟨S, hS, b, hm, hi, hmeas, hb, hbound, hd⟩
  exact hi

namespace NonlinearEpsilonStep

theorem epsilon_regular_of_integral_controls {m : ℝ} (hm : m ≠ 0)
    {F F₁ F₂ F₃ : ℝ → ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (H : ∀ e ∈ U,
      IntegralDerivativeControl (gaussianReal 0 1) (weight m F) (weightFirst m F F₁) e ∧
      IntegralDerivativeControl (gaussianReal 0 1) (weightFirst m F F₁)
        (weightSecond m F F₁ F₂) e ∧
      IntegralDerivativeControl (gaussianReal 0 1) (weightSecond m F F₁ F₂)
        (weightThird m F F₁ F₂ F₃) e)
    {ε : ℝ} (hε : ε ∈ U) :
    let θ := fun e => Real.log (∫ t, weight m F e t ∂gaussianReal 0 1) / m
    HasDerivAt θ (deriv θ ε) ε ∧
      HasDerivAt (deriv θ) (iteratedDeriv 2 θ ε) ε ∧
      HasDerivAt (iteratedDeriv 2 θ) (iteratedDeriv 3 θ ε) ε := by
  exact logPartition_regular_of_tower hU hm hε
    (fun e he => (H e he).1.hasDerivAt)
    (fun e he => (H e he).2.1.hasDerivAt)
    (fun e he => (H e he).2.2.hasDerivAt)
    (ne_of_gt (integral_exp_pos (H ε hε).1.integrable))

end NonlinearEpsilonStep

def EpsilonRegularAt (θ : ℝ → ℝ) (ε : ℝ) : Prop :=
  HasDerivAt θ (deriv θ ε) ε ∧
    HasDerivAt (deriv θ) (iteratedDeriv 2 θ ε) ε ∧
    HasDerivAt (iteratedDeriv 2 θ) (iteratedDeriv 3 θ ε) ε

def epsilonSuffixNoiseJet (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) (u : ℝ × Vec3) (x : Vec3) (n : ℕ) (ε t : ℝ) : ℝ :=
  iteratedDeriv n (fun e => epsilonChain l Q K e (x + t • u.2)) ε

def EpsilonChainDominationOn : List (ℝ × Vec3) → QuadraticTerminal →
    (Vec3 → ℝ) → Set ℝ → Prop
  | [], _, _, _ => True
  | u :: l, Q, K, U => EpsilonChainDominationOn l Q K U ∧ ∀ x : Vec3, ∀ ε ∈ U,
      let F := epsilonSuffixNoiseJet l Q K u x
      IntegralDerivativeControl (gaussianReal 0 1)
        (NonlinearEpsilonStep.weight u.1 (F 0)) (NonlinearEpsilonStep.weightFirst u.1 (F 0) (F 1)) ε ∧
      IntegralDerivativeControl (gaussianReal 0 1)
        (NonlinearEpsilonStep.weightFirst u.1 (F 0) (F 1))
        (NonlinearEpsilonStep.weightSecond u.1 (F 0) (F 1) (F 2)) ε ∧
      IntegralDerivativeControl (gaussianReal 0 1)
        (NonlinearEpsilonStep.weightSecond u.1 (F 0) (F 1) (F 2))
        (NonlinearEpsilonStep.weightThird u.1 (F 0) (F 1) (F 2) (F 3)) ε

theorem EpsilonChainDominationOn.regular {l : List (ℝ × Vec3)} {Q : QuadraticTerminal}
    {K : Vec3 → ℝ} {U : Set ℝ} (H : EpsilonChainDominationOn l Q K U)
    (hU : IsOpen U) (hm : ∀ u ∈ l, u.1 ≠ 0) (x : Vec3) {ε : ℝ} (hε : ε ∈ U) :
    EpsilonRegularAt (fun e => epsilonChain l Q K e x) ε := by
  cases l with
  | nil =>
    have ha : AnalyticAt ℝ (fun e => epsilonChain [] Q K e x) ε :=
      analyticAt_const.add (analyticAt_id.mul analyticAt_const)
    refine ⟨ha.differentiableAt.hasDerivAt, ?_, ?_⟩
    · simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
        ha.deriv.differentiableAt.hasDerivAt
    · simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
        ha.deriv.deriv.differentiableAt.hasDerivAt
  | cons u l =>
    have hfun : (fun e => epsilonChain (u :: l) Q K e x) = fun e =>
        Real.log (∫ t, NonlinearEpsilonStep.weight u.1
          (epsilonSuffixNoiseJet l Q K u x 0) e t ∂gaussianReal 0 1) / u.1 := by
      funext e
      simp only [epsilonChain, vectorIncrementChain, vectorStep, gaussianStep,
        ite_eq_right (hm u List.mem_cons_self), positiveGaussianLogStep,
        NonlinearEpsilonStep.weight, epsilonSuffixNoiseJet, iteratedDeriv_zero]
    rw [EpsilonRegularAt, hfun]
    exact NonlinearEpsilonStep.epsilon_regular_of_integral_controls
      (hm u List.mem_cons_self) hU (H.2 x) hε

private theorem suffix_weight (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) (u : ℝ × Vec3) (x : Vec3) :
    NonlinearEpsilonStep.weight u.1 (epsilonSuffixNoiseJet l Q K u x 0) =
      epsilonWeight l Q K u x := by
  funext e t
  rfl

private theorem suffix_weightFirst (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) (u : ℝ × Vec3) (x : Vec3) :
    NonlinearEpsilonStep.weightFirst u.1 (epsilonSuffixNoiseJet l Q K u x 0)
      (epsilonSuffixNoiseJet l Q K u x 1) = epsilonWeightFirst l Q K u x := by
  funext e t
  simp only [NonlinearEpsilonStep.weightFirst, NonlinearEpsilonStep.weight,
    epsilonSuffixNoiseJet, iteratedDeriv_zero, iteratedDeriv_one, epsilonWeightFirst, epsilonWeight]

private theorem suffix_weightSecond (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) (u : ℝ × Vec3) (x : Vec3) :
    NonlinearEpsilonStep.weightSecond u.1 (epsilonSuffixNoiseJet l Q K u x 0)
      (epsilonSuffixNoiseJet l Q K u x 1) (epsilonSuffixNoiseJet l Q K u x 2) =
        epsilonWeightSecond l Q K u x := by
  funext e t
  simp only [NonlinearEpsilonStep.weightSecond, NonlinearEpsilonStep.weight,
    epsilonSuffixNoiseJet, iteratedDeriv_zero, iteratedDeriv_one, epsilonWeightSecond, epsilonWeight]

theorem EpsilonChainDominationOn.chainControl {l : List (ℝ × Vec3)} {Q : QuadraticTerminal}
    {K : Vec3 → ℝ} {U : Set ℝ} (H : EpsilonChainDominationOn l Q K U)
    (hU : IsOpen U) (hzero : 0 ∈ U) : EpsilonChainControl l Q K := by
  induction l with
  | nil => exact True.intro
  | cons u l ih =>
    refine ⟨ih H.1, ?_⟩
    intro x
    constructor
    · filter_upwards [hU.mem_nhds hzero] with e he
      simpa only [suffix_weight, suffix_weightFirst] using (H.2 x e he).1
    · simpa only [suffix_weightFirst, suffix_weightSecond] using (H.2 x 0 hzero).2.1

def EpsilonSuffixPolynomialBounds : List (ℝ × Vec3) → QuadraticTerminal →
    (Vec3 → ℝ) → Set ℝ → Prop
  | [], _, _, _ => True
  | u :: l, Q, K, U => EpsilonSuffixPolynomialBounds l Q K U ∧ ∀ x : Vec3,
      ∃ A B M : ℝ, ∃ p : ℕ, 0 ≤ B ∧ 2 * B < 1 ∧ 0 ≤ M ∧
        let F := epsilonSuffixNoiseJet l Q K u x
        (∀ e ∈ U, Continuous (F 0 e) ∧ Continuous (F 1 e) ∧
          Continuous (F 2 e) ∧ Continuous (F 3 e)) ∧
        (∀ e ∈ U, ∀ t, u.1 * F 0 e t ≤ A + B * t ^ 2) ∧
        (∀ e ∈ U, ∀ t, |F 1 e t| ≤ M * (1 + t ^ 2) ^ p ∧
          |F 2 e t| ≤ M * (1 + t ^ 2) ^ p ∧ |F 3 e t| ≤ M * (1 + t ^ 2) ^ p)

theorem epsilonChainDominationOn_of_polynomial_bounds {l : List (ℝ × Vec3)}
    {Q : QuadraticTerminal} {K : Vec3 → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hm : ∀ u ∈ l, u.1 ≠ 0) (H : EpsilonSuffixPolynomialBounds l Q K U) :
    EpsilonChainDominationOn l Q K U := by
  induction l with
  | nil => exact True.intro
  | cons u l ih =>
    have hm' : ∀ w ∈ l, w.1 ≠ 0 := fun w hw => hm w (List.mem_cons_of_mem u hw)
    have hinner := ih hm' H.1
    refine ⟨hinner, ?_⟩
    intro x ε hε
    rcases H.2 x with ⟨A, B, M, p, hB, hsmall, hM, hc, hval, hjets⟩
    apply NonlinearEpsilonStep.integral_controls_of_polynomial_bounds hU hB hsmall hM hc _ hval hjets hε
    intro e he t
    have hreg := hinner.regular hU hm' (x + t • u.2) he
    simpa only [EpsilonRegularAt, epsilonSuffixNoiseJet, iteratedDeriv_zero, iteratedDeriv_one]
      using hreg

theorem epsilonChainControl_of_polynomial_bounds {l : List (ℝ × Vec3)}
    {Q : QuadraticTerminal} {K : Vec3 → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hzero : 0 ∈ U) (hm : ∀ u ∈ l, u.1 ≠ 0)
    (H : EpsilonSuffixPolynomialBounds l Q K U) : EpsilonChainControl l Q K := by
  exact (epsilonChainDominationOn_of_polynomial_bounds hU hm H).chainControl hU hzero

theorem scalarData_terminalChainDifferentiation_of_polynomial_bounds
    {β h₀ κ l u : ℝ} (D : ScalarData β) (hl : 0 < l) (hh₀ : h₀ ≤ l / 2)
    {U : Set ℝ} (hU : IsOpen U) (hzero : 0 ∈ U)
    (H : ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ κ → ∀ z : ℝ,
      EpsilonSuffixPolynomialBounds
        (frozenSchedule β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k)
        (terminalTaylorQuadratic β (cdf (D.μ : Measure ℝ)) (r - h) h z)
        (terminalResidual β (cdf (D.μ : Measure ℝ)) (r - h) h z) U) :
    TerminalChainDifferentiation β (cdf (D.μ : Measure ℝ)) (Icc l u) h₀ κ := by
  intro r hr h hh hhsmall k hk z
  have hs : 0 < r - h := by linarith only [hl, hr.1, hh₀, hhsmall]
  have hm := frozenSchedule_masses β (cdf (D.μ : Measure ℝ) (r - h)) (1 / 2) h k
    ⟨scalarData_cdf_pos_of_pos D hs, cdf_le_one _ _⟩
  exact epsilonChainControl_of_polynomial_bounds hU hzero
    (fun w hw => ne_of_gt (hm w hw).1) (H r hr h hh hhsmall k hk z)

theorem epsilonRegularAt_sub {f g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ∀ e ∈ U, EpsilonRegularAt f e) (hg : ∀ e ∈ U, EpsilonRegularAt g e)
    {ε : ℝ} (hε : ε ∈ U) : EpsilonRegularAt (fun e => f e - g e) ε := by
  have he₁ (e : ℝ) (he : e ∈ U) : deriv (fun a => f a - g a) =ᶠ[𝓝 e]
      (fun a => deriv f a - deriv g a) := by
    filter_upwards [hU.mem_nhds he] with a ha
    exact ((hf a ha).1.sub (hg a ha).1).deriv
  have hd₂ (e : ℝ) (he : e ∈ U) : HasDerivAt (deriv (fun a => f a - g a))
      (iteratedDeriv 2 f e - iteratedDeriv 2 g e) e :=
    ((hf e he).2.1.sub (hg e he).2.1).congr_of_eventuallyEq (he₁ e he)
  have he₂ : iteratedDeriv 2 (fun a => f a - g a) =ᶠ[𝓝 ε]
      (fun a => iteratedDeriv 2 f a - iteratedDeriv 2 g a) := by
    filter_upwards [hU.mem_nhds hε] with a ha
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using (hd₂ a ha).deriv
  have hd₃ := ((hf ε hε).2.2.sub (hg ε hε).2.2).congr_of_eventuallyEq he₂
  refine ⟨((hf ε hε).1.sub (hg ε hε).1).differentiableAt.hasDerivAt, ?_, ?_⟩
  · simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      (hd₂ ε hε).differentiableAt.hasDerivAt
  · simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      hd₃.differentiableAt.hasDerivAt

theorem frozenThetaDifference_regular_of_polynomial_bounds
    (β : ℝ) (α : ℝ → ℝ) (a s h k z : ℝ) (ha : a ∈ Ioc (0 : ℝ) 1)
    {U : Set ℝ} (hU : IsOpen U)
    (Hk : EpsilonSuffixPolynomialBounds (frozenSchedule β a (1 / 2) h k)
      (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z) U)
    (H₀ : EpsilonSuffixPolynomialBounds (frozenSchedule β a (1 / 2) h 0)
      (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z) U)
    {ε : ℝ} (hε : ε ∈ U) : EpsilonRegularAt (frozenThetaDifference β α a s h k z) ε := by
  have hmk : ∀ w ∈ frozenSchedule β a (1 / 2) h k, w.1 ≠ 0 :=
    fun w hw => ne_of_gt (frozenSchedule_masses β a (1 / 2) h k ha w hw).1
  have hm₀ : ∀ w ∈ frozenSchedule β a (1 / 2) h 0, w.1 ≠ 0 :=
    fun w hw => ne_of_gt (frozenSchedule_masses β a (1 / 2) h 0 ha w hw).1
  exact epsilonRegularAt_sub hU
    (fun e he => (epsilonChainDominationOn_of_polynomial_bounds hU hmk Hk).regular hU hmk (fun _ => z) he)
    (fun e he => (epsilonChainDominationOn_of_polynomial_bounds hU hm₀ H₀).regular hU hm₀ (fun _ => z) he) hε

def quadraticThird : List (ℝ × Vec3) → QuadraticTerminal → (Vec3 → ℝ) → Vec3 → ℝ
  | [], _, _ => fun _ => 0
  | u :: l, Q, K => fun x =>
      quadraticAverage (riccatiRecursion l Q) u.1 u.2
        (fun y => quadraticThird l Q K y + 3 * u.1 * quadraticFirst l Q K y * quadraticSecond l Q K y +
          u.1 ^ 2 * quadraticFirst l Q K y ^ 3) x -
      3 * u.1 * quadraticFirst (u :: l) Q K x *
        (quadraticSecond (u :: l) Q K x + u.1 * quadraticFirst (u :: l) Q K x ^ 2) +
      2 * u.1 ^ 2 * quadraticFirst (u :: l) Q K x ^ 3

theorem epsilonChain_third (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (K : Vec3 → ℝ)
    {U : Set ℝ} (hU : IsOpen U) (hzero : 0 ∈ U)
    (hQ : RiccatiAdmissible l Q) (H : EpsilonChainDominationOn l Q K U) (x : Vec3) :
    HasDerivAt (iteratedDeriv 2 (fun ε => epsilonChain l Q K ε x)) (quadraticThird l Q K x) 0 := by
  induction l generalizing x with
  | nil =>
    have hd (e : ℝ) : HasDerivAt (fun ε => epsilonChain [] Q K ε x) (K x) e := by
      simpa only [epsilonChain, vectorIncrementChain, one_mul, id_eq] using
        ((hasDerivAt_id e).mul_const (K x)).const_add (Q.value x)
    have he : deriv (fun ε => epsilonChain [] Q K ε x) = fun _ => K x :=
      funext (fun e => (hd e).deriv)
    have he₂ : iteratedDeriv 2 (fun ε => epsilonChain [] Q K ε x) = fun _ => 0 := by
      rw [iteratedDeriv_succ, iteratedDeriv_one, he]
      funext e
      exact deriv_const e (K x)
    rw [he₂]
    exact hasDerivAt_const 0 0
  | cons u l ih =>
    rcases hQ with ⟨hQ, hm, hp⟩
    have hchild := H.1.chainControl hU hzero
    have hfirstSecond (y : Vec3) := epsilonChain_first_second l Q K hQ hchild y
    have hfirst (y : Vec3) : deriv (fun e => epsilonChain l Q K e y) 0 = quadraticFirst l Q K y :=
      (hfirstSecond y).1.deriv
    have hsecond (y : Vec3) : iteratedDeriv 2 (fun e => epsilonChain l Q K e y) 0 =
        quadraticSecond l Q K y := by
      simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
        (hfirstSecond y).2.deriv
    have hthird (y : Vec3) : iteratedDeriv 3 (fun e => epsilonChain l Q K e y) 0 =
        quadraticThird l Q K y := by
      simpa only [iteratedDeriv_succ] using (ih hQ H.1 y).deriv
    let R := riccatiRecursion l Q
    let P := quadraticPartition R u.1 u.2 x
    let A := quadraticFirst (u :: l) Q K x
    let B := quadraticAverage R u.1 u.2
      (fun y => quadraticSecond l Q K y + u.1 * quadraticFirst l Q K y ^ 2) x
    let T := quadraticAverage R u.1 u.2
      (fun y => quadraticThird l Q K y + 3 * u.1 * quadraticFirst l Q K y * quadraticSecond l Q K y +
        u.1 ^ 2 * quadraticFirst l Q K y ^ 3) x
    let F := epsilonSuffixNoiseJet l Q K u x
    let Z : ℝ → ℝ := fun e => ∫ t, NonlinearEpsilonStep.weight u.1 (F 0) e t ∂gaussianReal 0 1
    let Z₁ : ℝ → ℝ := fun e => ∫ t, NonlinearEpsilonStep.weightFirst u.1 (F 0) (F 1) e t ∂gaussianReal 0 1
    let Z₂ : ℝ → ℝ := fun e => ∫ t, NonlinearEpsilonStep.weightSecond u.1 (F 0) (F 1) (F 2) e t ∂gaussianReal 0 1
    let Z₃ : ℝ → ℝ := fun e => ∫ t, NonlinearEpsilonStep.weightThird u.1 (F 0) (F 1) (F 2) (F 3) e t ∂gaussianReal 0 1
    have hZ : Z 0 = P := by
      dsimp only [Z, F, NonlinearEpsilonStep.weight, epsilonSuffixNoiseJet, iteratedDeriv_zero]
      simp_rw [iteratedDeriv_zero, epsilonChain_zero l Q K hQ]
      have hw := quadratic_weighted_moment R u.1 u.2 x hp (fun _ => 1)
      simpa [P, quadraticAverage, quadraticGaussian] using hw
    have hP : P ≠ 0 := ne_of_gt (quadraticPartition_pos R u.1 u.2 x hp)
    have hZ₁ : Z₁ 0 = u.1 * (P * A) := by
      dsimp only [Z₁, F, NonlinearEpsilonStep.weightFirst, NonlinearEpsilonStep.weight, epsilonSuffixNoiseJet]
      simp_rw [iteratedDeriv_zero, iteratedDeriv_one, epsilonChain_zero l Q K hQ, hfirst]
      rw [integral_const_mul, quadratic_weighted_moment R u.1 u.2 x hp
        (quadraticFirst l Q K)]
      rfl
    have hZ₂ : Z₂ 0 = u.1 * (P * B) := by
      dsimp only [Z₂, F, NonlinearEpsilonStep.weightSecond, NonlinearEpsilonStep.weight, epsilonSuffixNoiseJet]
      simp_rw [iteratedDeriv_zero, iteratedDeriv_one, epsilonChain_zero l Q K hQ, hfirst, hsecond]
      rw [integral_const_mul, quadratic_weighted_moment R u.1 u.2 x hp
        (fun y => quadraticSecond l Q K y + u.1 * quadraticFirst l Q K y ^ 2)]
    have hZ₃ : Z₃ 0 = u.1 * (P * T) := by
      dsimp only [Z₃, F, NonlinearEpsilonStep.weightThird, NonlinearEpsilonStep.weight, epsilonSuffixNoiseJet]
      simp_rw [iteratedDeriv_zero, iteratedDeriv_one, epsilonChain_zero l Q K hQ, hfirst, hsecond, hthird]
      rw [integral_const_mul, quadratic_weighted_moment R u.1 u.2 x hp
        (fun y => quadraticThird l Q K y + 3 * u.1 * quadraticFirst l Q K y * quadraticSecond l Q K y +
          u.1 ^ 2 * quadraticFirst l Q K y ^ 3)]
    have hd₀ (e : ℝ) (he : e ∈ U) : HasDerivAt Z (Z₁ e) e := (H.2 x e he).1.hasDerivAt
    have hd₁ (e : ℝ) (he : e ∈ U) : HasDerivAt Z₁ (Z₂ e) e := (H.2 x e he).2.1.hasDerivAt
    have hd₂ (e : ℝ) (he : e ∈ U) : HasDerivAt Z₂ (Z₃ e) e := (H.2 x e he).2.2.hasDerivAt
    have hfun : (fun e => epsilonChain (u :: l) Q K e x) = fun e => Real.log (Z e) / u.1 := by
      funext e
      simp only [epsilonChain, vectorIncrementChain, vectorStep, gaussianStep, ite_eq_right hm,
        positiveGaussianLogStep, Z, F, NonlinearEpsilonStep.weight, epsilonSuffixNoiseJet, iteratedDeriv_zero]
    rw [hfun]
    have hd := logPartition_third_of_tower hU hm hzero hd₀ hd₁ hd₂ (hZ ▸ hP)
    rw [hZ, hZ₁, hZ₂, hZ₃] at hd
    convert hd using 1
    change T - 3 * u.1 * A * ((B - u.1 * A ^ 2) + u.1 * A ^ 2) + 2 * u.1 ^ 2 * A ^ 3 = _
    field_simp [hm, hP]
    ring

end SKBarriers2.Corner
