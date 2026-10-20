module

public import SKBarriers2.Corner.FrozenDiffEps
public import SKBarriers2.Corner.FrozenCoef4

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def quadraticTaylorTail (f : ℝ → ℝ) (z y : ℝ) : ℝ :=
  f y - scalarTaylorPolynomial f 2 z y

def quadraticTaylorTailFirst (f : ℝ → ℝ) (z y : ℝ) : ℝ :=
  deriv f y - scalarTaylorPolynomial (deriv f) 1 z y

def quadraticTaylorTailSecond (f : ℝ → ℝ) (z y : ℝ) : ℝ :=
  deriv (deriv f) y - scalarTaylorPolynomial (deriv (deriv f)) 0 z y

theorem quadraticTaylorTail_derivatives {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (z y : ℝ) :
    HasDerivAt (quadraticTaylorTail f z) (quadraticTaylorTailFirst f z y) y ∧
      HasDerivAt (quadraticTaylorTailFirst f z) (quadraticTaylorTailSecond f z y) y := by
  have hf₁ : ContDiff ℝ ∞ (deriv f) := contDiff_deriv_infty hf
  exact ⟨(hf.differentiable (by simp) y).hasDerivAt.sub (scalarTaylorPolynomial_hasDerivAt f 1 z y),
    (hf₁.differentiable (by simp) y).hasDerivAt.sub (scalarTaylorPolynomial_hasDerivAt (deriv f) 0 z y)⟩

theorem quadraticTaylorTail_bounds {f : ℝ → ℝ} {B : ℝ} (hf : ContDiff ℝ ∞ f)
    (hb : ∀ y, |iteratedDeriv 3 f y| ≤ B) (z y : ℝ) :
    |quadraticTaylorTail f z y| ≤ B * |y - z| ^ 3 / 6 ∧
      |quadraticTaylorTailFirst f z y| ≤ B * |y - z| ^ 2 / 2 ∧
      |quadraticTaylorTailSecond f z y| ≤ B * |y - z| := by
  have hf₁ : ContDiff ℝ ∞ (deriv f) := contDiff_deriv_infty hf
  have hf₂ : ContDiff ℝ ∞ (deriv (deriv f)) := contDiff_deriv_infty hf₁
  have hb₁ (x : ℝ) : |iteratedDeriv 2 (deriv f) x| ≤ B := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hb x
  have hb₂ (x : ℝ) : |iteratedDeriv 1 (deriv (deriv f)) x| ≤ B := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using hb x
  have H₀ := scalarTaylorPolynomial_remainder_le (n := 2) (hf.of_le (by simp)) hb z y
  have H₁ := scalarTaylorPolynomial_remainder_le (n := 1) (hf₁.of_le (by simp)) hb₁ z y
  have H₂ := scalarTaylorPolynomial_remainder_le (n := 0) (hf₂.of_le (by simp)) hb₂ z y
  norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, pow_one, div_one] at H₀ H₁ H₂
  exact ⟨H₀, H₁, H₂⟩

theorem quadraticTaylorTail_comp_derivatives {f y y₁ y₂ : ℝ → ℝ} {k z : ℝ}
    (hf : ContDiff ℝ ∞ f) (hy : HasDerivAt y (y₁ k) k) (hy₁ : HasDerivAt y₁ (y₂ k) k) :
    HasDerivAt (fun x => quadraticTaylorTail f z (y x))
        (quadraticTaylorTailFirst f z (y k) * y₁ k) k ∧
      HasDerivAt (fun x => quadraticTaylorTailFirst f z (y x) * y₁ x)
        (quadraticTaylorTailSecond f z (y k) * y₁ k ^ 2 +
          quadraticTaylorTailFirst f z (y k) * y₂ k) k := by
  constructor
  · exact ((quadraticTaylorTail_derivatives hf z (y k)).1).comp k hy
  · convert (((quadraticTaylorTail_derivatives hf z (y k)).2).comp k hy).mul hy₁ using 1
    · rfl
    · simp only [Function.comp_apply]
      ring

theorem quadraticTaylorTail_comp_bounds {f : ℝ → ℝ} {B L z y y₁ y₂ : ℝ}
    (hf : ContDiff ℝ ∞ f) (hb : ∀ x, |iteratedDeriv 3 f x| ≤ B)
    (hB : 0 ≤ B) (hL : 0 ≤ L) (hy : |y - z| ≤ L) (hy₁ : |y₁| ≤ L) (hy₂ : |y₂| ≤ L) :
    |quadraticTaylorTail f z y| ≤ 2 * B * L ^ 3 ∧
      |quadraticTaylorTailFirst f z y * y₁| ≤ 2 * B * L ^ 3 ∧
      |quadraticTaylorTailSecond f z y * y₁ ^ 2 + quadraticTaylorTailFirst f z y * y₂| ≤
        2 * B * L ^ 3 := by
  have H := quadraticTaylorTail_bounds hf hb z y
  have h₀ : |quadraticTaylorTail f z y| ≤ B * L ^ 3 / 6 := H.1.trans (by gcongr)
  have h₁ : |quadraticTaylorTailFirst f z y| ≤ B * L ^ 2 / 2 := H.2.1.trans (by gcongr)
  have h₂ : |quadraticTaylorTailSecond f z y| ≤ B * L :=
    H.2.2.trans (mul_le_mul_of_nonneg_left hy hB)
  have hp₁ : |quadraticTaylorTailFirst f z y * y₁| ≤ B * L ^ 3 / 2 := by
    rw [abs_mul]
    exact (mul_le_mul h₁ hy₁ (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hp₂ : |quadraticTaylorTailSecond f z y * y₁ ^ 2| ≤ B * L ^ 3 := by
    rw [abs_mul, abs_pow]
    exact (mul_le_mul h₂ (pow_le_pow_left₀ (abs_nonneg _) hy₁ 2)
      (by positivity) (by positivity)).trans_eq (by ring)
  have hp₃ : |quadraticTaylorTailFirst f z y * y₂| ≤ B * L ^ 3 / 2 := by
    rw [abs_mul]
    exact (mul_le_mul h₁ hy₂ (abs_nonneg _) (by positivity)).trans_eq (by ring)
  have hscale : 0 ≤ B * L ^ 3 := mul_nonneg hB (pow_nonneg hL _)
  refine ⟨h₀.trans ?_, hp₁.trans ?_, ((abs_add_le _ _).trans (add_le_add hp₂ hp₃)).trans ?_⟩ <;>
    linarith

theorem terminalResidual_eq_quadraticTaylorTails (β : ℝ) (α : ℝ → ℝ) (s h z : ℝ) (x : Vec3) :
    terminalResidual β α s h z x =
      ∑ i : Fin 3, quadraticTaylorTail (Phi β α (s + 4 * h)) z (x i) := by
  rw [terminalResidual, terminalTaylorQuadratic_value]
  simp only [frozenTerminal, quadraticTaylorTail, scalarTaylorPolynomial,
    Finset.sum_range_succ, Finset.sum_range_zero, jet, iteratedDeriv_zero,
    Nat.factorial, Nat.cast_mul, Nat.cast_one, Fin.sum_univ_succ]
  ring

theorem scalarData_terminalResidual_cubic_scale {β s h : ℝ} (D : ScalarData β)
    (ht : s + 4 * h ∈ Icc (0 : ℝ) 1) (hh : 0 ≤ h) (z : ℝ) (y : Vec3) :
    |terminalResidual β (cdf (D.μ : Measure ℝ)) s h z (fun i => z + Real.sqrt h * y i)| ≤
      (scalarTerminalJetBound D 3 / 6) * (Real.sqrt h * h) * ∑ i : Fin 3, |y i| ^ 3 := by
  have H (i : Fin 3) := (quadraticTaylorTail_bounds (scalarData_phi_contDiff D ht)
    (fun x => scalarData_jet_le D (by norm_num : 1 ≤ 3) le_rfl ht x)
    z (z + Real.sqrt h * y i)).1
  rw [terminalResidual_eq_quadraticTaylorTails]
  calc
    _ ≤ ∑ i : Fin 3, |quadraticTaylorTail (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h))
        z (z + Real.sqrt h * y i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, scalarTerminalJetBound D 3 *
        |z + Real.sqrt h * y i - z| ^ 3 / 6 := Finset.sum_le_sum (fun i _ => H i)
    _ = _ := by
      simp only [add_sub_cancel_left, abs_mul, abs_of_nonneg (Real.sqrt_nonneg h), mul_pow]
      have hs : (Real.sqrt h) ^ 3 = Real.sqrt h * h := by
        calc
          _ = Real.sqrt h * (Real.sqrt h) ^ 2 := by ring
          _ = _ := by rw [Real.sq_sqrt hh]
      rw [hs, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

def epsilonPartitionWeight (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) (x : Vec3) (ε : ℝ) (n : Fin 4) (g : ℝ) : ℝ :=
  match l with
  | [] => 0
  | w :: t =>
    let F := epsilonSuffixNoiseJet t Q K w x
    ![NonlinearEpsilonStep.weight w.1 (F 0) ε g,
      NonlinearEpsilonStep.weightFirst w.1 (F 0) (F 1) ε g,
      NonlinearEpsilonStep.weightSecond w.1 (F 0) (F 1) (F 2) ε g,
      NonlinearEpsilonStep.weightThird w.1 (F 0) (F 1) (F 2) (F 3) ε g] n

def epsilonPartitionMoment (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) (x : Vec3) (ε : ℝ) (n : Fin 4) : ℝ :=
  ∫ g, epsilonPartitionWeight l Q K x ε n g ∂gaussianReal 0 1

def thirdPartitionRows (m : ℝ) (P : Fin 4 → ℝ → ℝ) (i : Fin 3) (k : ℝ) : ℝ :=
  ![P 3 k / (m * P 0 k),
    P 2 k * P 1 k / (m * P 0 k ^ 2),
    P 1 k ^ 3 / (m * P 0 k ^ 3)] i

theorem epsilonThirdPartitionRow_eq_moments (w : ℝ × Vec3) (t : List (ℝ × Vec3))
    (Q : QuadraticTerminal) (K : Vec3 → ℝ) (x : Vec3) (ε : ℝ) (i : Fin 3) :
    epsilonThirdPartitionRow (w :: t) Q K x ε i =
      thirdPartitionRows w.1 (fun n _ => epsilonPartitionMoment (w :: t) Q K x ε n) i 0 := by
  fin_cases i <;> rfl

def normalizedPartitionMoment (P : Fin 4 → ℝ → ℝ) (n : Fin 4) (k : ℝ) : ℝ :=
  P n k / P 0 k

def normalizedPartitionFirst (P P₁ : Fin 4 → ℝ → ℝ) (n : Fin 4) (k : ℝ) : ℝ :=
  P₁ n k / P 0 k - normalizedPartitionMoment P n k * (P₁ 0 k / P 0 k)

def normalizedPartitionSecond (P P₁ P₂ : Fin 4 → ℝ → ℝ) (n : Fin 4) (k : ℝ) : ℝ :=
  P₂ n k / P 0 k - normalizedPartitionMoment P n k * (P₂ 0 k / P 0 k) -
    2 * (P₁ n k / P 0 k) * (P₁ 0 k / P 0 k) +
    2 * normalizedPartitionMoment P n k * (P₁ 0 k / P 0 k) ^ 2

theorem normalizedPartition_derivatives {P P₁ P₂ : Fin 4 → ℝ → ℝ} {k : ℝ}
    (hP : ∀ n, HasDerivAt (P n) (P₁ n k) k)
    (hP₁ : ∀ n, HasDerivAt (P₁ n) (P₂ n k) k) (hZ : P 0 k ≠ 0) (n : Fin 4) :
    HasDerivAt (normalizedPartitionMoment P n) (normalizedPartitionFirst P P₁ n k) k ∧
      HasDerivAt (normalizedPartitionFirst P P₁ n)
        (normalizedPartitionSecond P P₁ P₂ n k) k := by
  constructor
  · change HasDerivAt (fun x => P n x / P 0 x) _ k
    convert (hP n).div (hP 0) hZ using 1
    unfold normalizedPartitionFirst normalizedPartitionMoment
    field_simp
  · have H := ((hP₁ n).div (hP 0) hZ).sub
      (((hP n).div (hP 0) hZ).mul ((hP₁ 0).div (hP 0) hZ))
    convert H using 1
    · rfl
    · unfold normalizedPartitionSecond normalizedPartitionMoment
      simp only [Pi.div_apply]
      field_simp
      ring

theorem normalizedPartition_bounds {P P₁ P₂ : Fin 4 → ℝ → ℝ} {k B t : ℝ}
    (hB : 1 ≤ B) (ht : 0 ≤ t)
    (hb : ∀ n : Fin 4,
      |P n k / P 0 k| ≤ B * t ^ n.val ∧
      |P₁ n k / P 0 k| ≤ B * t ^ n.val ∧
      |P₂ n k / P 0 k| ≤ B * t ^ n.val) (n : Fin 4) :
    |normalizedPartitionMoment P n k| ≤ (6 * B ^ 3) * t ^ n.val ∧
      |normalizedPartitionFirst P P₁ n k| ≤ (6 * B ^ 3) * t ^ n.val ∧
      |normalizedPartitionSecond P P₁ P₂ n k| ≤ (6 * B ^ 3) * t ^ n.val := by
  have hB₀ : 0 ≤ B := le_trans (by norm_num) hB
  have hpow : 0 ≤ t ^ n.val := pow_nonneg ht _
  have hb₀ : |P₁ 0 k / P 0 k| ≤ B := by simpa only [Fin.val_zero, pow_zero, mul_one] using (hb 0).2.1
  have hb₂ : |P₂ 0 k / P 0 k| ≤ B := by simpa only [Fin.val_zero, pow_zero, mul_one] using (hb 0).2.2
  have hprod₁ : |normalizedPartitionMoment P n k * (P₁ 0 k / P 0 k)| ≤ B ^ 2 * t ^ n.val := by
    rw [abs_mul]
    exact (mul_le_mul (hb n).1 hb₀ (abs_nonneg _) (mul_nonneg hB₀ hpow)).trans_eq (by ring)
  have hprod₂ : |normalizedPartitionMoment P n k * (P₂ 0 k / P 0 k)| ≤ B ^ 2 * t ^ n.val := by
    rw [abs_mul]
    exact (mul_le_mul (hb n).1 hb₂ (abs_nonneg _) (mul_nonneg hB₀ hpow)).trans_eq (by ring)
  have hprod₃ : |2 * (P₁ n k / P 0 k) * (P₁ 0 k / P 0 k)| ≤ 2 * B ^ 2 * t ^ n.val := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    calc
      _ ≤ 2 * (B * t ^ n.val) * B := by gcongr; exact (hb n).2.1
      _ = _ := by ring
  have hprod₄ : |2 * normalizedPartitionMoment P n k * (P₁ 0 k / P 0 k) ^ 2| ≤
      2 * B ^ 3 * t ^ n.val := by
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    calc
      _ ≤ 2 * (B * t ^ n.val) * B ^ 2 := by gcongr; exact (hb n).1
      _ = _ := by ring
  have hlarge : B + 3 * B ^ 2 + 2 * B ^ 3 ≤ 6 * B ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg B) (sub_nonneg.mpr hB),
      mul_nonneg hB₀ (sub_nonneg.mpr hB)]
  have hfirst : |normalizedPartitionFirst P P₁ n k| ≤ (B + B ^ 2) * t ^ n.val := by
    exact (abs_sub _ _).trans ((add_le_add (hb n).2.1 hprod₁).trans_eq (by ring))
  have hsecond : |normalizedPartitionSecond P P₁ P₂ n k| ≤
      (B + 3 * B ^ 2 + 2 * B ^ 3) * t ^ n.val := by
    exact (abs_add_le _ _).trans ((add_le_add
      ((abs_sub _ _).trans ((add_le_add
        ((abs_sub _ _).trans (add_le_add (hb n).2.2 hprod₂)) hprod₃))) hprod₄).trans_eq (by ring))
  refine ⟨(hb n).1.trans (mul_le_mul_of_nonneg_right ?_ hpow),
    hfirst.trans (mul_le_mul_of_nonneg_right ?_ hpow),
    hsecond.trans (mul_le_mul_of_nonneg_right hlarge hpow)⟩ <;>
    nlinarith [sq_nonneg B, mul_nonneg (sq_nonneg B) hB₀]

def normalizedThirdRows (m : ℝ) (A : Fin 4 → ℝ → ℝ) (i : Fin 3) (k : ℝ) : ℝ :=
  ![A 3 k / m, A 2 k * A 1 k / m, A 1 k ^ 3 / m] i

def normalizedThirdRowsFirst (m : ℝ) (A A₁ : Fin 4 → ℝ → ℝ)
    (i : Fin 3) (k : ℝ) : ℝ :=
  ![A₁ 3 k / m, (A₁ 2 k * A 1 k + A 2 k * A₁ 1 k) / m,
    (3 * A 1 k ^ 2 * A₁ 1 k) / m] i

def normalizedThirdRowsSecond (m : ℝ) (A A₁ A₂ : Fin 4 → ℝ → ℝ)
    (i : Fin 3) (k : ℝ) : ℝ :=
  ![A₂ 3 k / m,
    (A₂ 2 k * A 1 k + 2 * A₁ 2 k * A₁ 1 k + A 2 k * A₂ 1 k) / m,
    (6 * A 1 k * A₁ 1 k ^ 2 + 3 * A 1 k ^ 2 * A₂ 1 k) / m] i

theorem thirdPartitionRows_eq_normalized (m : ℝ) (P : Fin 4 → ℝ → ℝ)
    (i : Fin 3) (k : ℝ) :
    thirdPartitionRows m P i k = normalizedThirdRows m (normalizedPartitionMoment P) i k := by
  fin_cases i
  · change P 3 k / (m * P 0 k) = (P 3 k / P 0 k) / m
    rw [div_div, mul_comm]
  · change P 2 k * P 1 k / (m * P 0 k ^ 2) =
      (P 2 k / P 0 k) * (P 1 k / P 0 k) / m
    rw [div_mul_div_comm, div_div, pow_two]
    congr 1
    ring
  · change P 1 k ^ 3 / (m * P 0 k ^ 3) = (P 1 k / P 0 k) ^ 3 / m
    rw [div_pow, div_div, mul_comm]

theorem normalizedThirdRows_derivatives {A A₁ A₂ : Fin 4 → ℝ → ℝ} {k : ℝ}
    (hA : ∀ n, HasDerivAt (A n) (A₁ n k) k)
    (hA₁ : ∀ n, HasDerivAt (A₁ n) (A₂ n k) k) (m : ℝ) (i : Fin 3) :
    HasDerivAt (normalizedThirdRows m A i) (normalizedThirdRowsFirst m A A₁ i k) k ∧
      HasDerivAt (normalizedThirdRowsFirst m A A₁ i)
        (normalizedThirdRowsSecond m A A₁ A₂ i k) k := by
  fin_cases i
  · exact ⟨(hA 3).div_const m, (hA₁ 3).div_const m⟩
  · constructor
    · exact ((hA 2).mul (hA 1)).div_const m
    · change HasDerivAt (fun x => (A₁ 2 x * A 1 x + A 2 x * A₁ 1 x) / m) _ k
      convert (((hA₁ 2).mul (hA 1)).add ((hA 2).mul (hA₁ 1))).div_const m using 1
      change (_ + 2 * _ * _ + _) / m = _
      ring
  · constructor
    · change HasDerivAt (fun x => A 1 x ^ 3 / m) _ k
      convert ((hA 1).pow 3).div_const m using 1
      rfl
    · change HasDerivAt (fun x => (3 * A 1 x ^ 2 * A₁ 1 x) / m) _ k
      convert ((((hA 1).pow 2).const_mul 3).mul (hA₁ 1)).div_const m using 1
      change (6 * _ * _ ^ 2 + 3 * _ ^ 2 * _) / m = _
      norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply]
      ring

theorem normalizedThirdRowsSecond_bound {A A₁ A₂ : Fin 4 → ℝ → ℝ} {k M t m : ℝ}
    (hM : 0 ≤ M) (ht : 0 ≤ t) (hm : 0 < m)
    (hb : ∀ n : Fin 4, |A n k| ≤ M * t ^ n.val ∧
      |A₁ n k| ≤ M * t ^ n.val ∧ |A₂ n k| ≤ M * t ^ n.val) (i : Fin 3) :
    |normalizedThirdRowsSecond m A A₁ A₂ i k| ≤
      ((M + 4 * M ^ 2 + 9 * M ^ 3) / m) * t ^ 3 := by
  have htwo₀ : |A₂ 2 k * A 1 k| ≤ M ^ 2 * t ^ 3 := by
    rw [abs_mul]
    calc
      _ ≤ (M * t ^ 2) * (M * t) := by
        gcongr
        · exact (hb 2).2.2
        · simpa only [Fin.val_one, pow_one] using (hb 1).1
      _ = _ := by ring
  have htwo₁ : |2 * A₁ 2 k * A₁ 1 k| ≤ 2 * M ^ 2 * t ^ 3 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    calc
      _ ≤ 2 * (M * t ^ 2) * (M * t) := by
        gcongr
        · exact (hb 2).2.1
        · simpa only [Fin.val_one, pow_one] using (hb 1).2.1
      _ = _ := by ring
  have htwo₂ : |A 2 k * A₂ 1 k| ≤ M ^ 2 * t ^ 3 := by
    rw [abs_mul]
    calc
      _ ≤ (M * t ^ 2) * (M * t) := by
        gcongr
        · exact (hb 2).1
        · simpa only [Fin.val_one, pow_one] using (hb 1).2.2
      _ = _ := by ring
  have hthree₀ : |6 * A 1 k * A₁ 1 k ^ 2| ≤ 6 * M ^ 3 * t ^ 3 := by
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : 0 ≤ (6 : ℝ))]
    calc
      _ ≤ 6 * (M * t) * (M * t) ^ 2 := by
        gcongr
        · simpa only [Fin.val_one, pow_one] using (hb 1).1
        · simpa only [Fin.val_one, pow_one] using (hb 1).2.1
      _ = _ := by ring
  have hthree₁ : |3 * A 1 k ^ 2 * A₂ 1 k| ≤ 3 * M ^ 3 * t ^ 3 := by
    rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg (by norm_num : 0 ≤ (3 : ℝ))]
    calc
      _ ≤ 3 * (M * t) ^ 2 * (M * t) := by
        gcongr
        · simpa only [Fin.val_one, pow_one] using (hb 1).1
        · simpa only [Fin.val_one, pow_one] using (hb 1).2.2
      _ = _ := by ring
  have hcoeff₀ : M ≤ M + 4 * M ^ 2 + 9 * M ^ 3 := by nlinarith [pow_nonneg hM 3]
  have hcoeff₁ : 4 * M ^ 2 ≤ M + 4 * M ^ 2 + 9 * M ^ 3 := by nlinarith [pow_nonneg hM 3]
  have hcoeff₂ : 9 * M ^ 3 ≤ M + 4 * M ^ 2 + 9 * M ^ 3 := by nlinarith
  fin_cases i
  · change |A₂ 3 k / m| ≤ _
    rw [abs_div, abs_of_pos hm]
    calc
      _ ≤ (M * t ^ 3) / m := div_le_div_of_nonneg_right (hb 3).2.2 hm.le
      _ ≤ _ := by
        rw [mul_div_right_comm]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcoeff₀ hm.le) (pow_nonneg ht _)
  · change |(A₂ 2 k * A 1 k + 2 * A₁ 2 k * A₁ 1 k + A 2 k * A₂ 1 k) / m| ≤ _
    rw [abs_div, abs_of_pos hm]
    have H := (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add htwo₀ htwo₁)) htwo₂)
    calc
      _ ≤ (4 * M ^ 2 * t ^ 3) / m := div_le_div_of_nonneg_right (H.trans_eq (by ring)) hm.le
      _ ≤ _ := by
        rw [mul_div_right_comm]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcoeff₁ hm.le) (pow_nonneg ht _)
  · change |(6 * A 1 k * A₁ 1 k ^ 2 + 3 * A 1 k ^ 2 * A₂ 1 k) / m| ≤ _
    rw [abs_div, abs_of_pos hm]
    calc
      _ ≤ (9 * M ^ 3 * t ^ 3) / m := div_le_div_of_nonneg_right
        (((abs_add_le _ _).trans (add_le_add hthree₀ hthree₁)).trans_eq (by ring)) hm.le
      _ ≤ _ := by
        rw [mul_div_right_comm]
        exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hcoeff₂ hm.le) (pow_nonneg ht _)

theorem thirdPartitionRows_second_control {P P₁ P₂ : Fin 4 → ℝ → ℝ}
    {U : Set ℝ} {B t m : ℝ} (hB : 1 ≤ B) (ht : 0 ≤ t) (hm : 0 < m)
    (hZ : ∀ k ∈ U, P 0 k ≠ 0)
    (hd : ∀ k ∈ U, ∀ n, HasDerivAt (P n) (P₁ n k) k ∧ HasDerivAt (P₁ n) (P₂ n k) k)
    (hb : ∀ k ∈ U, ∀ n : Fin 4,
      |P n k / P 0 k| ≤ B * t ^ n.val ∧
      |P₁ n k / P 0 k| ≤ B * t ^ n.val ∧
      |P₂ n k / P 0 k| ≤ B * t ^ n.val) :
    ∃ d₁ d₂ : Fin 3 → ℝ → ℝ,
      (∀ i, ∀ k ∈ U, HasDerivAt (thirdPartitionRows m P i) (d₁ i k) k ∧
        HasDerivAt (d₁ i) (d₂ i k) k) ∧
      (∀ i, ∀ k ∈ U, |d₂ i k| ≤
        (((6 * B ^ 3) + 4 * (6 * B ^ 3) ^ 2 + 9 * (6 * B ^ 3) ^ 3) / m) * t ^ 3) := by
  let A := normalizedPartitionMoment P
  let A₁ := normalizedPartitionFirst P P₁
  let A₂ := normalizedPartitionSecond P P₁ P₂
  refine ⟨normalizedThirdRowsFirst m A A₁, normalizedThirdRowsSecond m A A₁ A₂, ?_, ?_⟩
  · intro i k hk
    have H (n : Fin 4) : HasDerivAt (A n) (A₁ n k) k ∧ HasDerivAt (A₁ n) (A₂ n k) k :=
      normalizedPartition_derivatives (fun n => (hd k hk n).1) (fun n => (hd k hk n).2) (hZ k hk) n
    have Hrow := normalizedThirdRows_derivatives (fun n => (H n).1) (fun n => (H n).2) m i
    have heq : thirdPartitionRows m P i = normalizedThirdRows m A i :=
      funext (thirdPartitionRows_eq_normalized m P i)
    rw [heq]
    exact Hrow
  · intro i k hk
    exact normalizedThirdRowsSecond_bound (by positivity : 0 ≤ 6 * B ^ 3) ht hm
      (normalizedPartition_bounds hB ht (hb k hk)) i

def partitionIntegral (W : Fin 4 → ℝ → ℝ → ℝ) (n : Fin 4) (k : ℝ) : ℝ :=
  ∫ g, W n k g ∂gaussianReal 0 1

structure PartitionIntegralKControl (W W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ)
    (U : Set ℝ) (B t : ℝ) : Prop where
  nonzero : ∀ k ∈ U, partitionIntegral W 0 k ≠ 0
  domination : ∀ k ∈ U, ∀ n : Fin 4,
    IntegralDerivativeControl (gaussianReal 0 1) (W n) (W₁ n) k ∧
      IntegralDerivativeControl (gaussianReal 0 1) (W₁ n) (W₂ n) k
  bounds : ∀ k ∈ U, ∀ n : Fin 4,
    |partitionIntegral W n k / partitionIntegral W 0 k| ≤ B * t ^ n.val ∧
    |partitionIntegral W₁ n k / partitionIntegral W 0 k| ≤ B * t ^ n.val ∧
    |partitionIntegral W₂ n k / partitionIntegral W 0 k| ≤ B * t ^ n.val

theorem PartitionIntegralKControl.rows {W W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ}
    {U : Set ℝ} {B t m : ℝ} (H : PartitionIntegralKControl W W₁ W₂ U B t)
    (hB : 1 ≤ B) (ht : 0 ≤ t) (hm : 0 < m) :
    ∃ d₁ d₂ : Fin 3 → ℝ → ℝ,
      (∀ i, ∀ k ∈ U, HasDerivAt (thirdPartitionRows m (partitionIntegral W) i) (d₁ i k) k ∧
        HasDerivAt (d₁ i) (d₂ i k) k) ∧
      (∀ i, ∀ k ∈ U, |d₂ i k| ≤
        (((6 * B ^ 3) + 4 * (6 * B ^ 3) ^ 2 + 9 * (6 * B ^ 3) ^ 3) / m) * t ^ 3) := by
  exact thirdPartitionRows_second_control hB ht hm H.nonzero
    (fun k hk n => ⟨(H.domination k hk n).1.hasDerivAt, (H.domination k hk n).2.hasDerivAt⟩) H.bounds

def frozenPartitionMass (a : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then a / 3 else if j = 1 then a / 2 else a

def frozenPartitionWeight (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    (j : ℕ) (n : Fin 4) (k g : ℝ) : ℝ :=
  epsilonPartitionWeight ((frozenSchedule β a (1 / 2) h k).drop j)
    (terminalTaylorQuadratic β α s h z) (terminalResidual β α s h z) (fun _ => z) ε n g

theorem frozenThirdPartitionRow_eq_moments (β : ℝ) (α : ℝ → ℝ) (a s h z ε : ℝ)
    {j : ℕ} (hj : j < 12) (i : Fin 3) (k : ℝ) :
    frozenThirdPartitionRow β α a s h z ε j i k =
      thirdPartitionRows (frozenPartitionMass a j)
        (partitionIntegral (frozenPartitionWeight β α a s h z ε j)) i k := by
  interval_cases j <;> fin_cases i <;> rfl

theorem frozenPartitionMass_lower {a a₀ : ℝ} (ha₀ : 0 < a₀) (ha : a₀ ≤ a) (j : ℕ) :
    a₀ / 3 ≤ frozenPartitionMass a j := by
  unfold frozenPartitionMass
  split_ifs <;> linarith

theorem cubic_residual_scale_le {h : ℝ} (hh : 0 ≤ h) (hh₁ : h ≤ 1) :
    (Real.sqrt h * h) ^ 3 ≤ Real.sqrt h * h ^ 3 := by
  have he : (Real.sqrt h * h) ^ 3 = (Real.sqrt h * h ^ 3) * h := by
    calc
      _ = (Real.sqrt h) ^ 2 * (Real.sqrt h * h ^ 3) := by ring
      _ = _ := by rw [Real.sq_sqrt hh]; ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left hh₁ (by positivity)).trans_eq (mul_one _)

theorem frozenKRegularity_of_partition_integral_controls
    {β B a₀ h₀ κ : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (hB : 1 ≤ B) (ha₀ : 0 < a₀) (hh₀ : h₀ ≤ 1)
    (hmass : ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → a₀ ≤ α (r - h))
    (H : ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
      ∀ j : ℕ, j < 12 → ∃ W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ,
        PartitionIntegralKControl
          (frozenPartitionWeight β α (α (r - h)) (r - h) h z ε j) W₁ W₂
          (Icc (-κ) κ) B (Real.sqrt h * h)) :
    FrozenKRegularity β α I
      (3 * ((6 * B ^ 3) + 4 * (6 * B ^ 3) ^ 2 + 9 * (6 * B ^ 3) ^ 3) / a₀) h₀ κ := by
  intro r hr h hh hhsmall z ε hε j hj
  rcases H r hr h hh hhsmall z ε hε j hj with ⟨W₁, W₂, HW⟩
  have hm := frozenPartitionMass_lower ha₀ (hmass r hr h hh hhsmall) j
  have hmpos : 0 < frozenPartitionMass (α (r - h)) j := (div_pos ha₀ (by norm_num)).trans_le hm
  rcases HW.rows hB (by positivity) hmpos with ⟨d₁, d₂, hd, hb⟩
  refine ⟨d₁, d₂, ?_, ?_⟩
  · intro i k hk
    have heq : frozenThirdPartitionRow β α (α (r - h)) (r - h) h z ε j i =
        thirdPartitionRows (frozenPartitionMass (α (r - h)) j)
          (partitionIntegral (frozenPartitionWeight β α (α (r - h)) (r - h) h z ε j)) i :=
      funext (frozenThirdPartitionRow_eq_moments β α _ _ h z ε hj i)
    rw [heq]
    exact hd i k hk
  · intro i k hk
    let R := (6 * B ^ 3) + 4 * (6 * B ^ 3) ^ 2 + 9 * (6 * B ^ 3) ^ 3
    have hR : 0 ≤ R := by dsimp only [R]; positivity
    have hcoeff : R / frozenPartitionMass (α (r - h)) j ≤ 3 * R / a₀ := by
      calc
        _ ≤ R / (a₀ / 3) := div_le_div_of_nonneg_left hR (div_pos ha₀ (by norm_num)) hm
        _ = _ := by ring
    calc
      _ ≤ (R / frozenPartitionMass (α (r - h)) j) * (Real.sqrt h * h) ^ 3 := hb i k hk
      _ ≤ (3 * R / a₀) * (Real.sqrt h * h ^ 3) :=
        mul_le_mul hcoeff (cubic_residual_scale_le hh.le (hhsmall.trans hh₀))
          (by positivity) (by positivity)
      _ = _ := by ring

theorem scalarData_frozenKRegularity_of_partition_integral_controls
    {β B h₀ κ l u : ℝ} (D : ScalarData β) (hl : 0 < l) (hB : 1 ≤ B) (hh₀ : 0 < h₀)
    (H : ∀ r ∈ Icc l u, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ z : ℝ, ∀ ε ∈ Icc (0 : ℝ) 1,
      ∀ j : ℕ, j < 12 → ∃ W₁ W₂ : Fin 4 → ℝ → ℝ → ℝ,
        PartitionIntegralKControl
          (frozenPartitionWeight β (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r - h)) (r - h) h z ε j) W₁ W₂
          (Icc (-κ) κ) B (Real.sqrt h * h)) :
    ∃ C h₁ : ℝ, 0 < C ∧ 0 < h₁ ∧ h₁ ≤ h₀ ∧
      FrozenKRegularity β (cdf (D.μ : Measure ℝ)) (Icc l u) C h₁ κ := by
  let a₀ := cdf (D.μ : Measure ℝ) (l / 2)
  have ha₀ : 0 < a₀ := scalarData_cdf_pos_of_pos D (by positivity : 0 < l / 2)
  let h₁ := min h₀ (min 1 (l / 2))
  have hh₁ : 0 < h₁ := lt_min hh₀ (lt_min (by norm_num) (by positivity))
  have hh₁₀ : h₁ ≤ h₀ := min_le_left _ _
  have hh₁one : h₁ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hh₁l : h₁ ≤ l / 2 := (min_le_right _ _).trans (min_le_right _ _)
  let C := 3 * ((6 * B ^ 3) + 4 * (6 * B ^ 3) ^ 2 + 9 * (6 * B ^ 3) ^ 3) / a₀
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, h₁, hC, hh₁, hh₁₀, ?_⟩
  apply frozenKRegularity_of_partition_integral_controls hB ha₀ hh₁one
  · intro r hr h hh hhsmall
    apply monotone_cdf (D.μ : Measure ℝ)
    linarith [hr.1, hhsmall.trans hh₁l]
  · intro r hr h hh hhsmall
    exact H r hr h hh (hhsmall.trans hh₁₀)

end SKBarriers2.Corner
