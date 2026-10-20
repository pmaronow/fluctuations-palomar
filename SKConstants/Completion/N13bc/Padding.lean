module

public import SKConstants.Completion.LC5.Padding
public import SKConstants.Completion.LW.DurationBounds

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped BigOperators NNReal InnerProductSpace RealInnerProductSpace Matrix.Norms.L2Operator

namespace SKConstants.Completion.N13bc

def liftVector {k m : ℕ} (_h : k ≤ m) (x : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun i => if hi : i.val < k then x ⟨i.val,hi⟩ else 0)

def restrictVector {k m : ℕ} (h : k ≤ m) (x : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (fun i => x (i.castLE h))

def liftMatrix {k m : ℕ} (_h : k ≤ m) (M : Matrix (Fin k) (Fin k) ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun i j => if hi : i.val < k then if hj : j.val < k then M ⟨i.val,hi⟩ ⟨j.val,hj⟩
    else 0 else 0

def restrictSet {k m : ℕ} (h : k ≤ m) (J : Finset (Fin m)) : Finset (Fin k) :=
  Finset.univ.filter (fun i => i.castLE h ∈ J)

@[simp] theorem liftVector_first {k m : ℕ} (h : k ≤ m)
    (x : EuclideanSpace ℝ (Fin k)) (i : Fin k) :
    liftVector h x (i.castLE h) = x i := by simp [liftVector]

@[simp] theorem liftVector_dummy {k m : ℕ} (h : k ≤ m)
    (x : EuclideanSpace ℝ (Fin k)) (i : Fin m) (hi : k ≤ i.val) :
    liftVector h x i = 0 := by simp [liftVector, not_lt.mpr hi]

theorem liftVector_eq_padVector {k p : ℕ} (x : EuclideanSpace ℝ (Fin k)) :
    liftVector (Nat.le_add_right k p) x = LC5.padVector p x := by
  ext i
  cases i using Fin.addCases with
  | left i => simp [liftVector, LC5.padVector_first]
  | right i => simp [liftVector, LC5.padVector, finSumFinEquiv]

theorem liftVector_inner {k m : ℕ} (h : k ≤ m)
    (x : EuclideanSpace ℝ (Fin k)) (a : EuclideanSpace ℝ (Fin m)) :
    ⟪liftVector h x,a⟫_ℝ = ⟪x,restrictVector h a⟫_ℝ := by
  obtain ⟨p,rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply, star_trivial]
  rw [Fin.sum_univ_add]
  simp only [liftVector, WithLp.ofLp_toLp, Fin.val_castAdd, Fin.is_lt, dite_true,
    Fin.val_natAdd, not_lt.mpr (Nat.le_add_right _ _), dite_false, mul_zero,
    Finset.sum_const_zero, add_zero, restrictVector]
  rfl

theorem restrictVector_norm_le {k m : ℕ} (h : k ≤ m)
    (x : EuclideanSpace ℝ (Fin m)) : ‖restrictVector h x‖ ≤ ‖x‖ := by
  obtain ⟨p,rfl⟩ := Nat.exists_eq_add_of_le h
  exact LC5.firstVector_norm_le x

theorem liftVector_norm {k m : ℕ} (h : k ≤ m)
    (x : EuclideanSpace ℝ (Fin k)) : ‖liftVector h x‖ = ‖x‖ := by
  obtain ⟨p,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [liftVector_eq_padVector, LC5.padVector_norm]

@[simp] theorem restrictVector_liftVector {k m : ℕ} (h : k ≤ m)
    (x : EuclideanSpace ℝ (Fin k)) : restrictVector h (liftVector h x) = x := by
  ext i
  exact liftVector_first h x i

theorem liftMatrix_transpose {k m : ℕ} (h : k ≤ m)
    (M : Matrix (Fin k) (Fin k) ℝ) :
    (liftMatrix h M).transpose = liftMatrix h M.transpose := by
  ext i j
  simp only [Matrix.transpose_apply, liftMatrix]
  split_ifs <;> rfl

theorem liftMatrix_halfUpper {k m : ℕ} (h : k ≤ m)
    (M : Matrix (Fin k) (Fin k) ℝ) :
    halfUpperTruncation (liftMatrix h M) = liftMatrix h (halfUpperTruncation M) := by
  ext i j
  simp only [liftMatrix, halfUpperTruncation]
  split_ifs <;> simp_all only [Fin.mk_lt_mk, Fin.mk.injEq, Fin.lt_def, Fin.ext_iff,
    zero_div, not_true_eq_false, not_false_eq_true]

theorem restrictVector_projection {k m : ℕ} (h : k ≤ m)
    (x : EuclideanSpace ℝ (Fin m)) (J : Finset (Fin m)) :
    restrictVector h (coordinateProjection J x) =
      coordinateProjection (restrictSet h J) (restrictVector h x) := by
  ext i
  simp [restrictVector, coordinateProjection_apply, restrictSet]

theorem liftVector_projection {k m : ℕ} (h : k ≤ m)
    (x : EuclideanSpace ℝ (Fin k)) (J : Finset (Fin m)) :
    coordinateProjection J (liftVector h x) =
      liftVector h (coordinateProjection (restrictSet h J) x) := by
  ext i
  simp only [coordinateProjection_apply, liftVector, WithLp.ofLp_toLp]
  split_ifs with hi hj hj
  all_goals simp_all [restrictSet]

theorem sum_liftVector {k m : ℕ} (h : k ≤ m)
    (x : EuclideanSpace ℝ (Fin k)) (J : Finset (Fin m)) :
    (∑ j ∈ J, liftVector h x j) = ∑ j ∈ restrictSet h J, x j := by
  have H := liftVector_inner h x (coordinateProjection J (WithLp.toLp 2 (fun _ => 1)))
  simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, coordinateProjection_apply,
    Pi.star_apply, star_trivial, restrictVector, restrictSet, Finset.sum_filter] using H

theorem liftVector_add {k m : ℕ} (h : k ≤ m)
    (x y : EuclideanSpace ℝ (Fin k)) :
    liftVector h (x+y) = liftVector h x + liftVector h y := by
  ext i
  simp only [liftVector, WithLp.ofLp_toLp, PiLp.add_apply]
  split_ifs <;> simp

theorem liftVector_smul {k m : ℕ} (h : k ≤ m) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin k)) :
    liftVector h (c • x) = c • liftVector h x := by
  ext i
  simp only [liftVector, WithLp.ofLp_toLp, PiLp.smul_apply, smul_eq_mul]
  split_ifs <;> simp

theorem measurable_liftVector {Ξ : Type*} [MeasurableSpace Ξ] {k m : ℕ}
    (h : k ≤ m) (x : Ξ → EuclideanSpace ℝ (Fin k)) (hx : Measurable x) :
    Measurable (fun u => liftVector h (x u)) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro i
  split_ifs with hi
  · exact (EuclideanSpace.proj ⟨i.val,hi⟩).measurable.comp hx
  · exact measurable_const

theorem measurable_liftMatrix {Ξ : Type*} [MeasurableSpace Ξ] {k m : ℕ}
    (h : k ≤ m) (F : Ξ → Matrix (Fin k) (Fin k) ℝ) (hF : Measurable F) :
    Measurable (fun u => liftMatrix h (F u)) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  dsimp only [liftMatrix]
  split_ifs with hi hj
  · exact (measurable_pi_apply ⟨j.val,hj⟩).comp
      ((measurable_pi_apply ⟨i.val,hi⟩).comp hF)
  · exact measurable_const
  · exact measurable_const

end SKConstants.Completion.N13bc
