module

public import SKConstants.DyadicNorm
import Mathlib.Tactic

public section
noncomputable section

namespace SKConstants

open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace

section LaminarCounting

variable {ι ρ κ : Type*} [DecidableEq ι] [Fintype ρ] [Fintype κ]

theorem subset_incidence_le (sets : ρ → Finset ι) (I : Finset ι) (d : ℝ)
    (hI : I.Nonempty)
    (hcount : ∀ i, (∑ u : ρ, if i ∈ sets u then (1 : ℝ) else 0) ≤ d) :
    (∑ u : ρ, if I ⊆ sets u then (1 : ℝ) else 0) ≤ d := by
  obtain ⟨i, hi⟩ := hI
  calc
    _ ≤ ∑ u : ρ, if i ∈ sets u then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro u _
      by_cases h : I ⊆ sets u
      · simp only [h, ite_true, h hi]
        exact le_refl 1
      · simp only [h, ite_false]
        split_ifs <;> norm_num
    _ ≤ _ := hcount i

theorem laminar_intersection_sum_le
    (sets : ρ → Finset ι) (right : κ → Finset ι) (embed : κ → ρ)
    (he : Function.Injective embed) (heq : ∀ u, sets (embed u) = right u)
    (hNonempty : ∀ I, (sets I).Nonempty)
    (hLaminar : ∀ I J, sets I ⊆ sets J ∨ sets J ⊆ sets I ∨ Disjoint (sets I) (sets J))
    (d : ℝ) (hd : 0 ≤ d)
    (hcount : ∀ i, (∑ I : ρ, if i ∈ sets I then (1 : ℝ) else 0) ≤ d)
    (hrcount : ∀ i, (∑ u : κ, if i ∈ right u then (1 : ℝ) else 0) ≤ d)
    (F : Finset ι → ℝ) (hF : ∀ I, 0 ≤ F I) (hzero : F ∅ = 0) :
    (∑ I : ρ, ∑ u : κ, F (sets I ∩ right u)) ≤ 2 * d * (∑ I : ρ, F (sets I)) := by
  have hPair (I : ρ) (u : κ) : F (sets I ∩ right u) ≤
      (if sets I ⊆ right u then F (sets I) else 0) +
        (if right u ⊆ sets I then F (right u) else 0) := by
    have hLam := hLaminar I (embed u)
    rw [heq u] at hLam
    rcases hLam with h | h | h
    · rw [Finset.inter_eq_left.mpr h]
      simp only [h, ite_true]
      split_ifs <;> linarith [hF (right u)]
    · rw [Finset.inter_eq_right.mpr h]
      simp only [h, ite_true]
      split_ifs <;> linarith [hF (sets I)]
    · rw [Finset.disjoint_iff_inter_eq_empty.mp h, hzero]
      split_ifs <;> linarith [hF (sets I), hF (right u)]
  have hFirst : (∑ I : ρ, ∑ u : κ,
      if sets I ⊆ right u then F (sets I) else 0) ≤ d * (∑ I : ρ, F (sets I)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro I _
    have hc := subset_incidence_le right (sets I) d (hNonempty I) hrcount
    have hm := mul_le_mul_of_nonneg_right hc (hF (sets I))
    simpa only [Finset.sum_mul, ite_mul, one_mul, zero_mul] using hm
  have hRightSum : (∑ u : κ, F (right u)) ≤ ∑ I : ρ, F (sets I) := by
    let e : κ ↪ ρ := ⟨embed, he⟩
    calc
      _ = ∑ I ∈ Finset.univ.map e, F (sets I) := by simp [Finset.sum_map, e, heq]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun I _ _ => hF (sets I))
  have hSecond : (∑ I : ρ, ∑ u : κ,
      if right u ⊆ sets I then F (right u) else 0) ≤ d * (∑ I : ρ, F (sets I)) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ u : κ, d * F (right u) := by
        apply Finset.sum_le_sum
        intro u _
        have hn : (right u).Nonempty := by rw [← heq u]; exact hNonempty (embed u)
        have hc := subset_incidence_le sets (right u) d hn hcount
        have hm := mul_le_mul_of_nonneg_right hc (hF (right u))
        simpa only [Finset.sum_mul, ite_mul, one_mul, zero_mul] using hm
      _ = d * (∑ u : κ, F (right u)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hRightSum hd
  calc
    _ ≤ ∑ I : ρ, ∑ u : κ,
        ((if sets I ⊆ right u then F (sets I) else 0) +
          (if right u ⊆ sets I then F (right u) else 0)) :=
      Finset.sum_le_sum fun I _ => Finset.sum_le_sum fun u _ => hPair I u
    _ = _ := by simp only [Finset.sum_add_distrib]
    _ ≤ d * (∑ I : ρ, F (sets I)) + d * (∑ I : ρ, F (sets I)) := add_le_add hFirst hSecond
    _ = _ := by ring

end LaminarCounting

theorem coordinateProjection_inter {ι : Type*} [DecidableEq ι]
    (I J : Finset ι) (w : EuclideanSpace ℝ ι) :
    coordinateProjection I (coordinateProjection J w) = coordinateProjection (I ∩ J) w := by
  ext i
  simp only [coordinateProjection_apply, Finset.mem_inter]
  split_ifs <;> simp_all

theorem dyadic_intersection_image_energy_le (r : ℕ)
    (Y : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ) (w : EuclideanSpace ℝ (Fin (2 ^ r))) :
    (∑ I : DyadicCore.Interval r, ∑ n : DyadicCore.Node r,
      ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) Y
        (coordinateProjection (dyadicRight r n)
          (coordinateProjection (dyadicIntervalSets r I) w))‖ ^ 2) ≤
      2 * (r + 1 : ℕ) * dyadicMatrixSeminorm r w Y ^ 2 := by
  let F : Finset (Fin (2 ^ r)) → ℝ := fun I =>
    ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) Y (coordinateProjection I w)‖ ^ 2
  have h := laminar_intersection_sum_le (dyadicIntervalSets r) (dyadicRight r)
    (DyadicCore.rightInterval r) (DyadicCore.rightInterval_injective r)
    (dyadic_rightInterval_sets r) (dyadicIntervalSets_nonempty r)
    (dyadicIntervalSets_laminar r) ((r + 1 : ℕ) : ℝ) (by positivity)
    (fun i => by simpa only [Nat.cast_add, Nat.cast_one] using (dyadicInterval_incidence_eq r i).le)
    (fun i => (dyadicRight_incidence_le r i).trans (by push_cast; linarith))
    F (fun I => sq_nonneg _) (by
      have hp : coordinateProjection (∅ : Finset (Fin (2 ^ r))) w = 0 := by ext i; simp
      simp only [F, hp, map_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0)])
  change _ ≤ 2 * (r + 1 : ℕ) * projectedMatrixSeminorm (dyadicIntervalSets r) w Y ^ 2
  rw [projectedMatrixSeminorm_sq]
  simpa only [F, coordinateProjection_inter, Finset.inter_comm] using h

theorem strictUpper_image_sq_le (r : ℕ)
    (A : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ) (w : EuclideanSpace ℝ (Fin (2 ^ r))) :
    ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) (strictUpperTruncation A) w‖ ^ 2 ≤
      r * (∑ n : DyadicCore.Node r,
        ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) A
          (coordinateProjection (dyadicRight r n) w)‖ ^ 2) := by
  generalize hvdef : Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ)
    (strictUpperTruncation A) w = v
  let e : ℝ := ∑ n : DyadicCore.Node r,
    ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) A
      (coordinateProjection (dyadicRight r n) w)‖ ^ 2
  have he : 0 ≤ e := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h := dyadic_rectangle_bound r (fun i => EuclideanSpace.single i (1 : ℝ))
    (fun j => Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) A
      (EuclideanSpace.single j (1 : ℝ))) v w
  rw [← strictUpperTruncation_inner_eq] at h
  simp_rw [← coordinateProjection_eq_sum, matrix_projected_column_sum] at h
  rw [hvdef] at h
  change |inner (𝕜 := ℝ) v v| ≤ _ * Real.sqrt e at h
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at h
  have hleft : Real.sqrt (∑ n : DyadicCore.Node r,
      ‖coordinateProjection (dyadicLeft r n) v‖ ^ 2) ≤ Real.sqrt r * ‖v‖ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg r)] using
      projection_energy_le_of_incidence (dyadicLeft r) v (r : ℝ) (dyadicLeft_incidence_le r)
  have hv : ‖v‖ ^ 2 ≤ (Real.sqrt r * ‖v‖) * Real.sqrt e :=
    h.trans (mul_le_mul_of_nonneg_right hleft (Real.sqrt_nonneg _))
  change ‖v‖ ^ 2 ≤ r * e
  by_cases hvzero : ‖v‖ = 0
  · simp only [hvzero, zero_pow (by norm_num : 2 ≠ 0)]
    exact mul_nonneg (Nat.cast_nonneg r) he
  · have hvpos : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hvzero)
    have hcancel : ‖v‖ ≤ Real.sqrt r * Real.sqrt e := by
      apply (mul_le_mul_iff_right₀ hvpos).mp
      convert hv using 1 <;> ring
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg r) (Real.sqrt_nonneg e))).2 hcancel
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg r), Real.sq_sqrt he] using hs

theorem dyadic_strict_gram_sq_le (r : ℕ)
    (X Y : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (w : EuclideanSpace ℝ (Fin (2 ^ r))) :
    dyadicMatrixSeminorm r w (strictUpperTruncation (X.transpose * Y)) ^ 2 ≤
      2 * r * (r + 1 : ℕ) * ‖X‖ ^ 2 * dyadicMatrixSeminorm r w Y ^ 2 := by
  change projectedMatrixSeminorm (dyadicIntervalSets r) w _ ^ 2 ≤ _
  rw [projectedMatrixSeminorm_sq]
  calc
    _ ≤ ∑ I : DyadicCore.Interval r, r * (∑ n : DyadicCore.Node r,
        ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) (X.transpose * Y)
          (coordinateProjection (dyadicRight r n) (coordinateProjection (dyadicIntervalSets r I) w))‖ ^ 2) :=
      Finset.sum_le_sum fun I _ => strictUpper_image_sq_le r _ _
    _ ≤ ∑ I : DyadicCore.Interval r, r * (∑ n : DyadicCore.Node r,
        ‖X‖ ^ 2 * ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) Y
          (coordinateProjection (dyadicRight r n) (coordinateProjection (dyadicIntervalSets r I) w))‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro I _
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg r)
      apply Finset.sum_le_sum
      intro n _
      have h := gramMatrix_action_norm_le X Y
        (coordinateProjection (dyadicRight r n) (coordinateProjection (dyadicIntervalSets r I) w))
      have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 h
      simpa only [mul_pow] using hs
    _ = r * ‖X‖ ^ 2 * (∑ I : DyadicCore.Interval r, ∑ n : DyadicCore.Node r,
        ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) Y
          (coordinateProjection (dyadicRight r n) (coordinateProjection (dyadicIntervalSets r I) w))‖ ^ 2) := by
      simp only [← Finset.mul_sum]
      ring
    _ ≤ r * ‖X‖ ^ 2 * (2 * (r + 1 : ℕ) * dyadicMatrixSeminorm r w Y ^ 2) :=
      mul_le_mul_of_nonneg_left (dyadic_intersection_image_energy_le r Y w)
        (mul_nonneg (Nat.cast_nonneg r) (sq_nonneg _))
    _ = _ := by ring

theorem diagonal_gram_projected_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X Y : Matrix ι ι ℝ) (I : Finset ι) (w : EuclideanSpace ℝ ι) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
      (Matrix.diagonal (fun i => (X.transpose * Y) i i)) (coordinateProjection I w)‖ ^ 2 ≤
      ‖X‖ ^ 2 * (∑ i ∈ I,
        ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) Y (coordinateProjection {i} w)‖ ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have hf : (∑ i ∈ I,
      ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) Y (coordinateProjection {i} w)‖ ^ 2) =
      ∑ i : ι, if i ∈ I then
        ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) Y (coordinateProjection {i} w)‖ ^ 2 else 0 := by simp
  rw [hf, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have heval : (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (X.transpose * Y)
      (coordinateProjection {i} w)) i = (X.transpose * Y) i i * w i := by
    rw [coordinateProjection_singleton, map_smul]
    simp only [PiLp.smul_apply, smul_eq_mul, matrix_column_apply]
    ring
  by_cases hi : i ∈ I
  · have hc := PiLp.norm_apply_le (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
      (X.transpose * Y) (coordinateProjection {i} w)) i
    rw [heval, Real.norm_eq_abs] at hc
    have hg := gramMatrix_action_norm_le X Y (coordinateProjection {i} w)
    have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 (hc.trans hg)
    simpa only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal, Pi.mul_apply,
      coordinateProjection_apply, hi, ite_true, mul_pow, sq_abs] using hs
  · simp only [Matrix.ofLp_toEuclideanCLM, Matrix.mulVec_diagonal,
      coordinateProjection_apply, hi, ite_false, mul_zero, zero_pow (by norm_num : 2 ≠ 0)]
    exact le_refl 0

theorem dyadic_diagonal_gram_sq_le (r : ℕ)
    (X Y : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (w : EuclideanSpace ℝ (Fin (2 ^ r))) :
    dyadicMatrixSeminorm r w (Matrix.diagonal (fun i => (X.transpose * Y) i i)) ^ 2 ≤
      (r + 1 : ℕ) * ‖X‖ ^ 2 * dyadicMatrixSeminorm r w Y ^ 2 := by
  let z : EuclideanSpace ℝ (Fin (2 ^ r)) := WithLp.toLp 2 fun i =>
    ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) Y (coordinateProjection {i} w)‖
  have hz : ‖z‖ ^ 2 ≤ dyadicMatrixSeminorm r w Y ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact dyadic_singleton_image_energy_le r Y w
  change projectedMatrixSeminorm (dyadicIntervalSets r) w _ ^ 2 ≤ _
  rw [projectedMatrixSeminorm_sq]
  calc
    _ ≤ ∑ I : DyadicCore.Interval r, ‖X‖ ^ 2 * ‖coordinateProjection (dyadicIntervalSets r I) z‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro I _
      rw [coordinateProjection_norm_sq]
      exact diagonal_gram_projected_sq_le X Y _ w
    _ = ‖X‖ ^ 2 * (∑ I : DyadicCore.Interval r, ‖coordinateProjection (dyadicIntervalSets r I) z‖ ^ 2) := by
      rw [Finset.mul_sum]
    _ ≤ ‖X‖ ^ 2 * ((r + 1 : ℕ) * ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (projection_energy_le_of_incidence (dyadicIntervalSets r) z
        (r + 1 : ℕ) (fun i => by simpa only [Nat.cast_add, Nat.cast_one] using (dyadicInterval_incidence_eq r i).le))
        (sq_nonneg _)
    _ ≤ ‖X‖ ^ 2 * ((r + 1 : ℕ) * dyadicMatrixSeminorm r w Y ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz (by positivity)) (sq_nonneg _)
    _ = _ := by ring

theorem dyadic_halfUpper_gram_le (r : ℕ)
    (X Y : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ)
    (w : EuclideanSpace ℝ (Fin (2 ^ r))) :
    dyadicMatrixSeminorm r w (halfUpperTruncation (X.transpose * Y)) ≤
      2 * (r + 1 : ℕ) * ‖X‖ * dyadicMatrixSeminorm r w Y := by
  let d : ℝ := (r + 1 : ℕ)
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hd1 : 1 ≤ d := by dsimp [d]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
  have hr : (r : ℝ) ≤ d := by dsimp [d]; push_cast; linarith
  have hstrict : dyadicMatrixSeminorm r w (strictUpperTruncation (X.transpose * Y)) ≤
      (3 / 2 : ℝ) * d * ‖X‖ * dyadicMatrixSeminorm r w Y := by
    apply (sq_le_sq₀ (apply_nonneg _ _) (by positivity)).mp
    have h := dyadic_strict_gram_sq_le r X Y w
    have hc : 2 * r * d ≤ ((3 / 2 : ℝ) * d) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hc
      (mul_nonneg (sq_nonneg ‖X‖) (sq_nonneg (dyadicMatrixSeminorm r w Y)))
    exact h.trans (by convert hm using 1 <;> ring)
  have hdiag : dyadicMatrixSeminorm r w (Matrix.diagonal (fun i => (X.transpose * Y) i i)) ≤
      d * ‖X‖ * dyadicMatrixSeminorm r w Y := by
    apply (sq_le_sq₀ (apply_nonneg _ _) (by positivity)).mp
    have h := dyadic_diagonal_gram_sq_le r X Y w
    have hc : d ≤ d ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_right hc
      (mul_nonneg (sq_nonneg ‖X‖) (sq_nonneg (dyadicMatrixSeminorm r w Y)))
    exact h.trans (by convert hm using 1 <;> ring)
  have heq := half_diagonal_eq_smul (X.transpose * Y)
  rw [halfUpperTruncation_eq, heq]
  calc
    _ ≤ dyadicMatrixSeminorm r w (strictUpperTruncation (X.transpose * Y)) +
        dyadicMatrixSeminorm r w ((1 / 2 : ℝ) • Matrix.diagonal (fun i => (X.transpose * Y) i i)) := map_add_le_add _ _ _
    _ = dyadicMatrixSeminorm r w (strictUpperTruncation (X.transpose * Y)) +
        (1 / 2 : ℝ) * dyadicMatrixSeminorm r w (Matrix.diagonal (fun i => (X.transpose * Y) i i)) := by
      rw [map_smul_eq_mul]; norm_num
    _ ≤ (3 / 2 : ℝ) * d * ‖X‖ * dyadicMatrixSeminorm r w Y +
        (1 / 2 : ℝ) * (d * ‖X‖ * dyadicMatrixSeminorm r w Y) :=
      add_le_add hstrict (mul_le_mul_of_nonneg_left hdiag (by norm_num))
    _ = _ := by dsimp [d]; ring

end SKConstants
