module

public import SKBarriers2.Analysis.WeightedJets

@[expose] public section

noncomputable section
open scoped BigOperators Topology

namespace SKBarriers2

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem WJets.const {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r : ℕ) (c : F) : WJets r ‖c‖ 0 (fun _ : E => c) := by
  refine ⟨norm_nonneg c, contDiff_const, ?_⟩
  intro j hj x
  by_cases hj0 : j = 0
  · subst j
    simp only [norm_iteratedFDeriv_zero, pow_zero, mul_one]
    exact le_rfl
  · simp only [iteratedFDeriv_const_of_ne hj0, Pi.zero_apply, norm_zero, pow_zero, mul_one]
    exact norm_nonneg c

theorem WJets.clm_apply {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {r p q : ℕ} {B C : ℝ} {f : E → F →L[ℝ] G} {g : E → F}
    (hf : WJets r B p f) (hg : WJets r C q g) :
    WJets r ((2 : ℝ) ^ r * B * C) (p + q) (fun x => f x (g x)) := by
  have hB := hf.nonneg
  have hC := hg.nonneg
  refine ⟨by positivity, hf.smooth.clm_apply hg.smooth, ?_⟩
  intro j hj x
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (j - i) g x‖ :=
      norm_iteratedFDeriv_clm_apply hf.smooth hg.smooth x (by exact_mod_cast hj)
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
        (B * (1 + ‖x‖) ^ p) * (C * (1 + ‖x‖) ^ q) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
      gcongr
      · exact hf.bound i (hi'.trans hj) x
      · exact hg.bound (j - i) (by omega) x
    _ = (2 : ℝ) ^ j * B * C * (1 + ‖x‖) ^ (p + q) := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, pow_add]
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hB) hC) (by positivity)

theorem WJets.affine {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r : ℕ) (A : E →L[ℝ] F) (b : F) :
    WJets r (‖A‖ + ‖b‖) 1 (fun x => A x + b) := by
  refine ⟨by positivity, A.contDiff.add contDiff_const, ?_⟩
  intro j hj x
  cases j with
  | zero =>
      rw [norm_iteratedFDeriv_zero, pow_one]
      have H := (norm_add_le (A x) b).trans (add_le_add (A.le_opNorm x) le_rfl)
      nlinarith [norm_nonneg A, norm_nonneg b, norm_nonneg x,
        mul_nonneg (norm_nonneg b) (norm_nonneg x)]
  | succ j =>
      have hd : fderiv ℝ (fun x => A x + b) = fun _ => A := by
        funext y
        exact ((A.hasFDerivAt).add_const b).fderiv
      rw [← norm_iteratedFDeriv_fderiv, hd]
      by_cases hj0 : j = 0
      · subst j
        rw [norm_iteratedFDeriv_zero, pow_one]
        nlinarith [norm_nonneg A, norm_nonneg b, norm_nonneg x,
          mul_nonneg (norm_nonneg A) (norm_nonneg x),
          mul_nonneg (norm_nonneg b) (norm_nonneg x)]
      · simp only [iteratedFDeriv_const_of_ne hj0, Pi.zero_apply, norm_zero]
        positivity

theorem WJets.mul_small_linear_score_one_degree {r n : ℕ} {C L δ : ℝ}
    {f s₀ s₁ : E → ℝ}
    (hf : WJets r C (n + 1) f) (hδf : WJets r C n (fun x => δ * f x))
    (hs₀ : WJets r L 0 s₀) (hs₁ : WJets r L 1 s₁) :
    WJets r (2 * (2 : ℝ) ^ r * C * L) (n + 1)
      (fun x => f x * (s₀ x + δ * s₁ x)) := by
  have H₀ := (hf.mul hs₀).mono le_rfl (by omega : n + 1 + 0 ≤ n + 1)
  have H₁ := (hδf.mul hs₁).mono le_rfl (by omega : n + 1 ≤ n + 1)
  convert H₀.add H₁ using 1
  · ring
  · funext x
    ring

theorem WJets.mul_small_linear_score_of_gap {r n p : ℕ} {C L δ : ℝ}
    {f s₀ s₁ : E → ℝ}
    (hf : WJets r C p f) (hδf : WJets r C n (fun x => δ * f x))
    (hs₀ : WJets r L 0 s₀) (hs₁ : WJets r L 1 s₁) (hgap : n + 1 ≤ p) :
    WJets r (2 * (2 : ℝ) ^ r * C * L) p
      (fun x => f x * (s₀ x + δ * s₁ x)) := by
  have hp : p - 1 + 1 = p := by omega
  have H := (hf.mono le_rfl (by omega : p ≤ p - 1 + 1)).mul_small_linear_score_one_degree
    (hδf.mono le_rfl (by omega : n ≤ p - 1)) hs₀ hs₁
  simpa only [hp] using H

theorem WJets.mul_small_linear_score {r n : ℕ} {C L δ : ℝ} {f s₀ s₁ : E → ℝ}
    (hf : WJets r C (n + 2) f) (hδf : WJets r C n (fun x => δ * f x))
    (hs₀ : WJets r L 0 s₀) (hs₁ : WJets r L 1 s₁) :
    WJets r (2 * (2 : ℝ) ^ r * C * L) (n + 2)
      (fun x => f x * (s₀ x + δ * s₁ x)) := by
  have H₀ := (hf.mul hs₀).mono le_rfl (by omega : n + 2 + 0 ≤ n + 2)
  have H₁ := (hδf.mul hs₁).mono le_rfl (by omega : n + 1 ≤ n + 2)
  convert H₀.add H₁ using 1
  · ring
  · funext x
    ring

theorem WJets.mul_small_quadratic_score {r n : ℕ} {C L δ : ℝ}
    {f t₀ t₁ t₂ : E → ℝ}
    (hf : WJets r C (n + 2) f) (hδf : WJets r C n (fun x => δ * f x))
    (hδ : |δ| ≤ 1)
    (ht₀ : WJets r L 0 t₀) (ht₁ : WJets r L 1 t₁) (ht₂ : WJets r L 2 t₂) :
    WJets r (3 * (2 : ℝ) ^ r * C * L) (n + 2)
      (fun x => f x * (t₀ x + δ * t₁ x + δ ^ 2 * t₂ x)) := by
  have H₀ := (hf.mul ht₀).mono le_rfl (by omega : n + 2 + 0 ≤ n + 2)
  have H₁ := (hδf.mul ht₁).mono le_rfl (by omega : n + 1 ≤ n + 2)
  have H₂ := (hδf.mul ht₂).const_smul δ
  have H₂' : WJets r ((2 : ℝ) ^ r * C * L) (n + 2)
      (fun x => δ * ((δ * f x) * t₂ x)) := by
    apply H₂.mono _ le_rfl
    exact mul_le_of_le_one_left (by positivity [hf.nonneg, ht₂.nonneg]) hδ
  convert (H₀.add H₁).add H₂' using 1
  · ring
  · funext x
    ring

theorem WJets.linear_score_square_profile {r : ℕ} {L : ℝ} {s₀ s₁ : E → ℝ}
    (hs₀ : WJets r L 0 s₀) (hs₁ : WJets r L 1 s₁) :
    let B := 2 * (2 : ℝ) ^ r * L ^ 2
    WJets r B 0 (fun x => s₀ x ^ 2) ∧
      WJets r B 1 (fun x => 2 * s₀ x * s₁ x) ∧
      WJets r B 2 (fun x => s₁ x ^ 2) := by
  have H₀ := hs₀.mul hs₀
  have H₁ := (hs₀.mul hs₁).const_smul 2
  have H₂ := hs₁.mul hs₁
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · convert H₀.mono (show (2 : ℝ) ^ r * L * L ≤ 2 * (2 : ℝ) ^ r * L ^ 2 by
      nlinarith [mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ r) (sq_nonneg L)])
      (show 0 + 0 ≤ 0 by omega) using 1
    funext x
    ring
  · convert H₁ using 1
    · norm_num
      ring
    · funext x
      change 2 * s₀ x * s₁ x = 2 * (s₀ x * s₁ x)
      ring
  · convert H₂.mono (show (2 : ℝ) ^ r * L * L ≤ 2 * (2 : ℝ) ^ r * L ^ 2 by
      nlinarith [mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ r) (sq_nonneg L)])
      (show 1 + 1 ≤ 2 by omega) using 1
    funext x
    ring

theorem WJets.mul_small_linear_score_sq {r n : ℕ} {C L δ : ℝ} {f s₀ s₁ : E → ℝ}
    (hf : WJets r C (n + 2) f) (hδf : WJets r C n (fun x => δ * f x))
    (hδ : |δ| ≤ 1) (hs₀ : WJets r L 0 s₀) (hs₁ : WJets r L 1 s₁) :
    WJets r (6 * ((2 : ℝ) ^ r) ^ 2 * C * L ^ 2) (n + 2)
      (fun x => f x * (s₀ x + δ * s₁ x) ^ 2) := by
  obtain ⟨H₀, H₁, H₂⟩ := hs₀.linear_score_square_profile hs₁
  have H := hf.mul_small_quadratic_score hδf hδ H₀ H₁ H₂
  convert H using 1
  · ring
  · funext x
    ring

end SKBarriers2
