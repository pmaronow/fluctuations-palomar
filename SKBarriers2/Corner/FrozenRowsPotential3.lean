module

public import SKBarriers2.Corner.FrozenRowsPotential2

@[expose] public section

noncomputable section
open scoped Topology
open Set

namespace SKBarriers2.Corner
open StepCalculus

local notation "E" => (Fin 3 → ℝ)

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem movingFirstMajorant_length_bound
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) {A K : ℝ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (q u : P)
    (H : ∀ c ∈ ps, c.1 u = 0 ∧ ‖c.2 q‖ ≤ 1 ∧ ‖c.2 u‖ ≤ 1) :
    movingFirstMajorant A K q u ps ≤ (1 + 6 * K) ^ ps.length * (A + 1) := by
  induction ps with
  | nil => simp only [movingFirstMajorant, List.length_nil, pow_zero, one_mul]; linarith
  | cons c ps ih =>
    have htail := fun d hd => H d (List.mem_cons_of_mem c hd)
    have hc := H c (List.mem_cons_self ..)
    have hC : 1 ≤ 1 + 6 * K := by linarith
    have hT : 1 ≤ (1 + 6 * K) ^ ps.length * (A + 1) :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC) (by linarith)
    have hv₂ : ‖c.2 q‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (c.2 q)]
    have hvw : ‖c.2 q‖ * ‖c.2 u‖ ≤ 1 := by
      exact (mul_le_mul hc.2.1 hc.2.2 (norm_nonneg _) (by norm_num)).trans_eq (by ring)
    simp only [movingFirstMajorant, hc.1, mul_zero, abs_zero, add_zero,
      List.length_cons, pow_succ]
    calc
      _ ≤ (1 + K) * ((1 + 6 * K) ^ ps.length * (A + 1)) + K := by
        apply add_le_add
        · exact mul_le_mul (by nlinarith) (ih htail)
            (movingFirstMajorant_nonneg hA hK _ _ _) (by positivity)
        · exact mul_le_of_le_one_right hK hvw
      _ ≤ (1 + 6 * K) ^ ps.length * (1 + 6 * K) * (A + 1) := by
        have hKT := mul_le_mul_of_nonneg_left hT hK
        nlinarith

theorem movingSecondMajorant_length_bound
    (ps : List ((P →L[ℝ] ℝ) × (P →L[ℝ] E))) {A H K : ℝ}
    (hA : 0 ≤ A) (hH : 0 ≤ H) (hK : 0 ≤ K) (q u a : P)
    (HG : ∀ c ∈ ps, c.1 u = 0 ∧ c.1 a = 0 ∧
      ‖c.2 q‖ ≤ 1 ∧ ‖c.2 u‖ ≤ 1 ∧ ‖c.2 a‖ ≤ 1) :
    movingSecondMajorant A H K q u a ps ≤
      (1 + 6 * K) ^ (2 * ps.length) * (H + (A + 1) ^ 2) := by
  induction ps with
  | nil =>
    simp only [movingSecondMajorant, List.length_nil, mul_zero, pow_zero, one_mul]
    nlinarith [sq_nonneg (A + 1)]
  | cons c ps ih =>
    have htail := fun d hd => HG d (List.mem_cons_of_mem c hd)
    have hc := HG c (List.mem_cons_self ..)
    let C := 1 + 6 * K
    let F := C ^ ps.length * (A + 1)
    let T := C ^ (2 * ps.length) * (H + (A + 1) ^ 2)
    have hC : 1 ≤ C := by dsimp only [C]; linarith
    have hF : 1 ≤ F :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC) (by linarith)
    have hFF : F ^ 2 ≤ T := by
      dsimp only [F, T]
      rw [mul_pow, ← pow_mul]
      have he : ps.length * 2 = 2 * ps.length := by omega
      rw [he]
      exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (by linarith : 0 ≤ C) _)
    have hT : 1 ≤ T := hF.trans ((le_self_pow₀ hF (by norm_num : (2 : ℕ) ≠ 0)).trans hFF)
    have hN := movingFirstMajorant_nonneg hA hK q u ps
    have hNF : movingFirstMajorant A K q u ps ≤ F :=
      movingFirstMajorant_length_bound ps hA hK q u
        (fun d hd => let h := htail d hd; ⟨h.1, h.2.2.1, h.2.2.2.1⟩)
    have hNF₂ : movingFirstMajorant A K q u ps ^ 2 ≤ T :=
      (pow_le_pow_left₀ hN hNF 2).trans hFF
    have hNFT : movingFirstMajorant A K q u ps ≤ T :=
      hNF.trans ((le_self_pow₀ hF (by norm_num : (2 : ℕ) ≠ 0)).trans hFF)
    have hv₂ : ‖c.2 q‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (c.2 q), hc.2.2.1]
    have hw₂ : ‖c.2 u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (c.2 u), hc.2.2.2.1]
    have hvw : ‖c.2 q‖ * ‖c.2 u‖ ≤ 1 :=
      (mul_le_mul hc.2.2.1 hc.2.2.2.1 (norm_nonneg _) (by norm_num)).trans_eq (by ring)
    have hvb : ‖c.2 q‖ * ‖c.2 a‖ ≤ 1 :=
      (mul_le_mul hc.2.2.1 hc.2.2.2.2 (norm_nonneg _) (by norm_num)).trans_eq (by ring)
    have hsource : secondVariationSource (movingFirstMajorant A K q u ps)
        (Real.exp (c.1 q) * c.1 u)
        (Real.exp (c.1 q) * ((c.1 u) ^ 2 + c.1 a)) (c.2 q) (c.2 u) (c.2 a) ≤ 4 * T := by
      simp only [hc.1, hc.2.1, mul_zero, zero_pow (by norm_num : 2 ≠ 0),
        abs_zero, secondVariationSource, mul_zero, add_zero]
      have h₁ : ‖c.2 q‖ ^ 2 * movingFirstMajorant A K q u ps ^ 2 ≤ T :=
        (mul_le_of_le_one_left (sq_nonneg _) hv₂).trans hNF₂
      have h₂ : ‖c.2 q‖ * ‖c.2 u‖ * movingFirstMajorant A K q u ps ≤ T :=
        (mul_le_of_le_one_left hN hvw).trans hNFT
      linarith
    have hstep : movingSecondMajorant A H K q u a (c :: ps) ≤ (1 + 5 * K) * T := by
      change (1 + K * ‖c.2 q‖ ^ 2) * movingSecondMajorant A H K q u a ps + _ ≤ _
      have hmain : (1 + K * ‖c.2 q‖ ^ 2) * movingSecondMajorant A H K q u a ps ≤
          (1 + K) * T := mul_le_mul (by nlinarith) (ih htail)
            (movingSecondMajorant_nonneg hA hH hK _ _ _ _) (by positivity)
      have hs := mul_le_mul_of_nonneg_left hsource hK
      linarith
    apply hstep.trans
    have he : 2 * (c :: ps).length = 2 * ps.length + 2 := by simp; omega
    rw [he, pow_add]
    change (1 + 5 * K) * T ≤ C ^ (2 * ps.length) * C ^ 2 * (H + (A + 1) ^ 2)
    have hcoef : 1 + 5 * K ≤ C ^ 2 := by dsimp only [C]; nlinarith
    exact (mul_le_mul_of_nonneg_right hcoef (by linarith : 0 ≤ T)).trans_eq (by dsimp only [T]; ring)

end SKBarriers2.Corner
