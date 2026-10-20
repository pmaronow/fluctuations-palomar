module

public import SKConstants.Completion.N13e.Linearization
public import SKConstants.Completion.LM4b.ZetaAlgebra
public import SKConstants.Completion.LM4b.CoarseNoiseBudget

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators NNReal RealInnerProductSpace Matrix.Norms.L2Operator

namespace SKConstants.Completion.N13e
open LC5 LGram LM4b SKConstantsOAI.ZeroTemperatureSK

theorem energyLinearPart_eq_uncentered {k : ℕ}
    (A H H0 : Matrix (Fin k) (Fin k) ℝ)
    (s q b v : EuclideanSpace ℝ (Fin k))
    (hH0 : ∀ i j, i ≤ j → H0 i j = 0) :
    inner (𝕜 := ℝ) s b + energyLinearPart (A-1) (H-H0) s (q-s) b (v-b) =
      inner (𝕜 := ℝ) q b + inner (𝕜 := ℝ) s v -
      inner (𝕜 := ℝ) s
        (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) (halfUpperTruncation A) b) -
      inner (𝕜 := ℝ) s
        (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ) (fullUpperTruncation H) s) -
      inner (𝕜 := ℝ) s b / 2 := by
  have hJ : halfUpperTruncation (A-1) = halfUpperTruncation A -
      (1/2:ℝ) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    ext i j
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [halfUpperTruncation, hij, hij.ne]
    · subst j
      simp [halfUpperTruncation]
      ring
    · simp [halfUpperTruncation, not_lt.mpr hij.le, hij.ne']
  have hT : fullUpperTruncation (H-H0) = fullUpperTruncation H := by
    ext i j
    by_cases hij : i ≤ j
    · simp [fullUpperTruncation, hij, hH0 i j hij]
    · simp [fullUpperTruncation, hij]
  rw [energyLinearPart, hJ, hT]
  simp only [map_sub, map_smul, map_one, sub_apply,
    smul_apply, one_apply_eq_self,
    inner_sub_left, inner_sub_right, real_inner_smul_right]
  ring

def empiricalCross {N k : ℕ} (T g : Fin N → Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => (∑ l, T l i * g l j) / (N:ℝ)

def empiricalSpin {N k : ℕ} (T : Fin N → Fin k → ℝ) (x : Fin N → ℝ) :
    EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (fun j => (∑ l, T l j * x l) / (N:ℝ))

theorem empiricalSpin_pairing {N k : ℕ} (T : Fin N → Fin k → ℝ)
    (x : Fin N → ℝ) (b : EuclideanSpace ℝ (Fin k)) :
    inner (𝕜 := ℝ) (empiricalSpin T x) b =
      (∑ l, x l * ∑ j, b j * T l j) / (N:ℝ) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
    star_trivial, empiricalSpin]
  change (∑ j, b j * ((∑ l, T l j * x l) / (N:ℝ))) = _
  simp only [← mul_div_assoc, Finset.mul_sum]
  rw [← Finset.sum_div, Finset.sum_comm]
  apply congrArg (fun a : ℝ => a / (N:ℝ))
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem empirical_halfUpper_entry {N k : ℕ} (T : Fin N → Fin k → ℝ) (i j : Fin k) :
    halfUpperTruncation (empiricalCross T T) i j =
      (∑ l, halfUpperTruncation (fun a b => T l a * T l b) i j) / (N:ℝ) := by
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [halfUpperTruncation, empiricalCross, hij]
  · subst j
    simp only [halfUpperTruncation, lt_self_iff_false, ite_false, ite_true,
      empiricalCross]
    rw [← Finset.sum_div]
    ring
  · simp [halfUpperTruncation, not_lt.mpr hij.le, hij.ne']

theorem empirical_fullUpper_entry {N k : ℕ} (T g : Fin N → Fin k → ℝ) (i j : Fin k) :
    fullUpperTruncation (empiricalCross T g) i j =
      (∑ l, fullUpperTruncation (fun a b => T l a * g l b) i j) / (N:ℝ) := by
  by_cases hij : i ≤ j <;> simp [fullUpperTruncation, empiricalCross, hij]

theorem empirical_triangle_pairing {N k : ℕ}
    (A : Fin N → Matrix (Fin k) (Fin k) ℝ)
    (s b : EuclideanSpace ℝ (Fin k)) :
    inner (𝕜 := ℝ) s (Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℝ)
      (fun i j => (∑ l, A l i j) / (N:ℝ)) b) =
      (∑ l, ∑ i, s i * ∑ j, A l i j * b j) / (N:ℝ) := by
  rw [Matrix.inner_toEuclideanCLM]
  change (∑ i, s i * ∑ j, ((∑ l, A l i j) / (N:ℝ)) * b j) = _
  calc
    _ = (∑ i, ∑ j, ∑ l, s i * (A l i j * b j)) / (N:ℝ) := by
      simp only [Finset.sum_div, mul_div_assoc, div_mul_eq_mul_div,
        Finset.mul_sum, Finset.sum_mul]
    _ = (∑ l, ∑ i, ∑ j, s i * (A l i j * b j)) / (N:ℝ) := by
      congr 1
      calc
        _ = ∑ i, ∑ l, ∑ j, s i * (A l i j * b j) :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
        _ = _ := Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

theorem empiricalLinearEnergy_eq_rowAverage {N k : ℕ} (hN : 0 < N)
    (T g : Fin N → Fin k → ℝ) (x : Fin N → ℝ)
    (s b : EuclideanSpace ℝ (Fin k)) (H0 : Matrix (Fin k) (Fin k) ℝ)
    (hH0 : ∀ i j, i ≤ j → H0 i j = 0) :
    inner (𝕜 := ℝ) s b + energyLinearPart
      (empiricalCross T T-1) (empiricalCross T g-H0)
      s (empiricalSpin T x-s) b (empiricalSpin g x-b) =
      (∑ l, rowLinearEnergy (fun j => b j) (fun j => s j) (T l) (g l) (x l)
        (inner (𝕜 := ℝ) s b)) / (N:ℝ) := by
  rw [energyLinearPart_eq_uncentered _ _ _ _ _ _ _ hH0,
    empiricalSpin_pairing, real_inner_comm (empiricalSpin g x) s, empiricalSpin_pairing]
  have hA : halfUpperTruncation (empiricalCross T T) =
      fun i j => (∑ l, halfUpperTruncation (fun a b => T l a * T l b) i j) / (N:ℝ) :=
    funext fun i => funext fun j => empirical_halfUpper_entry T i j
  have hH : fullUpperTruncation (empiricalCross T g) =
      fun i j => (∑ l, fullUpperTruncation (fun a b => T l a * g l b) i j) / (N:ℝ) :=
    funext fun i => funext fun j => empirical_fullUpper_entry T g i j
  rw [hA, hH]
  rw [empirical_triangle_pairing, empirical_triangle_pairing]
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  simp only [rowLinearEnergy, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

theorem empiricalLinearEnergy_eq_zetaAverage {N k : ℕ} (hN : 0 < N)
    (T g : Fin N → Fin k → ℝ) (x : Fin N → ℝ)
    (w : Fin k → ℝ) (s b : EuclideanSpace ℝ (Fin k))
    (hb : ∀ j, b j = w j * s j)
    (H0 : Matrix (Fin k) (Fin k) ℝ) (hH0 : ∀ i j, i ≤ j → H0 i j = 0) :
    inner (𝕜 := ℝ) s b + energyLinearPart
      (empiricalCross T T-1) (empiricalCross T g-H0)
      s (empiricalSpin T x-s) b (empiricalSpin g x-b) =
      (∑ l, rowZeta w (fun j => s j) (T l) (g l) (x l)
        (inner (𝕜 := ℝ) s b)) / (N:ℝ) := by
  rw [empiricalLinearEnergy_eq_rowAverage hN T g x s b H0 hH0]
  simp_rw [rowLinearEnergy_eq_zeta w (fun j => b j) (fun j => s j) _ _ _ _ hb]

end SKConstants.Completion.N13e
