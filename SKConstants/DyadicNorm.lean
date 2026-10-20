module

public import SKConstants.EuclideanMatrix
import Mathlib.Tactic

public section
noncomputable section

namespace SKConstants.DyadicCore

@[expose, reducible] def Interval (r : ℕ) : Type :=
  Nat.rec Unit (fun _ child => Unit ⊕ (child ⊕ child)) r

instance intervalFintype (r : ℕ) : Fintype (Interval r) :=
  Nat.rec (motive := fun r => Fintype (Interval r))
    (inferInstanceAs (Fintype Unit))
    (fun r child => by
      letI : Fintype (Interval r) := child
      exact inferInstanceAs (Fintype (Unit ⊕ (Interval r ⊕ Interval r)))) r

instance intervalDecidableEq (r : ℕ) : DecidableEq (Interval r) :=
  Nat.rec (motive := fun r => DecidableEq (Interval r))
    (inferInstanceAs (DecidableEq Unit))
    (fun r child => by
      letI : DecidableEq (Interval r) := child
      exact inferInstanceAs (DecidableEq (Unit ⊕ (Interval r ⊕ Interval r)))) r

@[expose] def intervalSets : (r : ℕ) → Interval r → Finset (Fin (leafCount r))
  | 0, _ => Finset.univ
  | _ + 1, .inl _ => Finset.univ
  | r + 1, .inr (.inl I) => (intervalSets r I).map (Fin.castAddEmb (leafCount r))
  | r + 1, .inr (.inr I) => (intervalSets r I).map (Fin.natAddEmb (leafCount r))

theorem interval_incidence_eq (r : ℕ) (i : Fin (leafCount r)) :
    (∑ I : Interval r, if i ∈ intervalSets r I then (1 : ℝ) else 0) = r + 1 := by
  induction r with
  | zero =>
      have hi : i = 0 := by
        apply Fin.ext
        change i.val = 0
        have h := i.is_lt
        change i.val < 1 at h
        omega
      subst i
      simp [Interval, intervalSets]
  | succ r ih =>
      cases i using Fin.addCases with
      | left i =>
          change (∑ I : Unit ⊕ (Interval r ⊕ Interval r),
            if Fin.castAdd _ i ∈ intervalSets (r+1) I then (1 : ℝ) else 0) = _
          simp only [Fintype.sum_sum_type, intervalSets, Finset.mem_univ, ite_true,
            castAdd_mem_castAdd, castAdd_not_mem_natAdd, ite_false, Finset.sum_const_zero,
            Fintype.sum_unique, add_zero]
          rw [ih]
          push_cast
          ring
      | right i =>
          change (∑ I : Unit ⊕ (Interval r ⊕ Interval r),
            if Fin.natAdd _ i ∈ intervalSets (r+1) I then (1 : ℝ) else 0) = _
          simp only [Fintype.sum_sum_type, intervalSets, Finset.mem_univ, ite_true,
            natAdd_mem_natAdd, natAdd_not_mem_castAdd, ite_false, Finset.sum_const_zero,
            Fintype.sum_unique, zero_add]
          rw [ih]
          push_cast
          ring

theorem intervalSets_nonempty (r : ℕ) (I : Interval r) : (intervalSets r I).Nonempty := by
  induction r with
  | zero => exact ⟨⟨0, by simp [leafCount]⟩, Finset.mem_univ _⟩
  | succ r ih =>
      rcases I with u | I
      · exact ⟨⟨0, by rw [leafCount_eq_pow]; positivity⟩, Finset.mem_univ _⟩
      · rcases I with I | I
        · exact (ih I).map
        · exact (ih I).map

theorem castAdd_natAdd_disjoint (m : ℕ) (s t : Finset (Fin m)) :
    Disjoint (s.map (Fin.castAddEmb m)) (t.map (Fin.natAddEmb m)) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  rcases Finset.mem_map.mp hi with ⟨j, _, rfl⟩
  exact castAdd_not_mem_natAdd m t j hj

theorem intervalSets_laminar (r : ℕ) (I J : Interval r) :
    intervalSets r I ⊆ intervalSets r J ∨ intervalSets r J ⊆ intervalSets r I ∨
      Disjoint (intervalSets r I) (intervalSets r J) := by
  induction r with
  | zero => exact Or.inl (by simp [intervalSets])
  | succ r ih =>
      rcases I with u | I
      · exact Or.inr (Or.inl (Finset.subset_univ _))
      · rcases J with u | J
        · exact Or.inl (Finset.subset_univ _)
        · rcases I with I | I <;> rcases J with J | J
          · rcases ih I J with h | h | h
            · exact Or.inl ((Finset.map_subset_map).2 h)
            · exact Or.inr (Or.inl ((Finset.map_subset_map).2 h))
            · exact Or.inr (Or.inr ((Finset.disjoint_map _).2 h))
          · exact Or.inr (Or.inr (castAdd_natAdd_disjoint _ _ _))
          · exact Or.inr (Or.inr (castAdd_natAdd_disjoint _ _ _).symm)
          · rcases ih I J with h | h | h
            · exact Or.inl ((Finset.map_subset_map).2 h)
            · exact Or.inr (Or.inl ((Finset.map_subset_map).2 h))
            · exact Or.inr (Or.inr ((Finset.disjoint_map _).2 h))

@[expose] def singletonInterval : (r : ℕ) → Fin (leafCount r) → Interval r
  | 0, _ => ()
  | r + 1, i => Fin.addCases
      (fun j => .inr (.inl (singletonInterval r j)))
      (fun j => .inr (.inr (singletonInterval r j))) i

theorem singletonInterval_sets (r : ℕ) (i : Fin (leafCount r)) :
    intervalSets r (singletonInterval r i) = {i} := by
  induction r with
  | zero =>
      have hi : i = ⟨0, by simp [leafCount]⟩ := by
        apply Fin.ext
        change i.val = 0
        have h := i.is_lt
        change i.val < 1 at h
        omega
      subst i
      ext j
      have hj : j = ⟨0, by simp [leafCount]⟩ := by
        apply Fin.ext
        change j.val = 0
        have h := j.is_lt
        change j.val < 1 at h
        omega
      subst j
      simp [intervalSets]
  | succ r ih =>
      cases i using Fin.addCases with
      | left i => simp [singletonInterval, intervalSets, ih]
      | right i =>
          simp only [singletonInterval, Fin.addCases_right, intervalSets, ih,
            Finset.map_singleton, Fin.natAddEmb_apply]

theorem singletonInterval_injective (r : ℕ) : Function.Injective (singletonInterval r) := by
  intro i j hij
  have h := congrArg (intervalSets r) hij
  simpa only [singletonInterval_sets, Finset.singleton_inj] using h

@[expose] def rootInterval : (r : ℕ) → Interval r
  | 0 => ()
  | _ + 1 => .inl ()

@[simp] theorem rootInterval_sets (r : ℕ) : intervalSets r (rootInterval r) = Finset.univ := by
  cases r <;> rfl

@[expose] def rightInterval : (r : ℕ) → Node r → Interval r
  | 0, n => nomatch n
  | r + 1, .inl _ => .inr (.inr (rootInterval r))
  | r + 1, .inr (.inl n) => .inr (.inl (rightInterval r n))
  | r + 1, .inr (.inr n) => .inr (.inr (rightInterval r n))

theorem rightInterval_ne_root (r : ℕ) (n : Node r) : rightInterval r n ≠ rootInterval r := by
  cases r with
  | zero => exact Empty.elim n
  | succ r =>
      rcases n with u | n
      · simp [rightInterval, rootInterval]
      · rcases n with n | n <;> simp [rightInterval, rootInterval]

theorem rightInterval_injective (r : ℕ) : Function.Injective (rightInterval r) := by
  induction r with
  | zero => intro i; exact Empty.elim i
  | succ r ih =>
      intro i j hij
      rcases i with u | i <;> rcases j with v | j
      · cases u; cases v; rfl
      · rcases j with j | j
        · simp [rightInterval] at hij
        · have h : rootInterval r = rightInterval r j := by simpa only [rightInterval, Sum.inr.injEq] using hij
          exact False.elim (rightInterval_ne_root r j h.symm)
      · rcases i with i | i
        · simp [rightInterval] at hij
        · have h : rightInterval r i = rootInterval r := by simpa only [rightInterval, Sum.inr.injEq] using hij
          exact False.elim (rightInterval_ne_root r i h)
      · rcases i with i | i <;> rcases j with j | j
        · exact congrArg (fun n => Sum.inr (Sum.inl n)) (ih (by simpa [rightInterval] using hij))
        · simp [rightInterval] at hij
        · simp [rightInterval] at hij
        · exact congrArg (fun n => Sum.inr (Sum.inr n)) (ih (by simpa [rightInterval] using hij))

theorem rightInterval_sets (r : ℕ) (n : Node r) : intervalSets r (rightInterval r n) = right r n := by
  induction r with
  | zero => exact Empty.elim n
  | succ r ih =>
      rcases n with u | n
      · simp [rightInterval, intervalSets, right]
      · rcases n with n | n <;> simp [rightInterval, intervalSets, right, ih]

@[expose] def leftInterval : (r : ℕ) → Node r → Interval r
  | 0, n => nomatch n
  | r + 1, .inl _ => .inr (.inl (rootInterval r))
  | r + 1, .inr (.inl n) => .inr (.inl (leftInterval r n))
  | r + 1, .inr (.inr n) => .inr (.inr (leftInterval r n))

theorem leftInterval_ne_root (r : ℕ) (n : Node r) : leftInterval r n ≠ rootInterval r := by
  cases r with
  | zero => exact Empty.elim n
  | succ r =>
      rcases n with u | n
      · simp [leftInterval, rootInterval]
      · rcases n with n | n <;> simp [leftInterval, rootInterval]

theorem leftInterval_injective (r : ℕ) : Function.Injective (leftInterval r) := by
  induction r with
  | zero => intro i; exact Empty.elim i
  | succ r ih =>
      intro i j hij
      rcases i with u | i <;> rcases j with v | j
      · cases u; cases v; rfl
      · rcases j with j | j
        · have h : rootInterval r = leftInterval r j := by simpa only [leftInterval, Sum.inr.injEq, Sum.inl.injEq] using hij
          exact False.elim (leftInterval_ne_root r j h.symm)
        · simp [leftInterval] at hij
      · rcases i with i | i
        · have h : leftInterval r i = rootInterval r := by simpa only [leftInterval, Sum.inr.injEq, Sum.inl.injEq] using hij
          exact False.elim (leftInterval_ne_root r i h)
        · simp [leftInterval] at hij
      · rcases i with i | i <;> rcases j with j | j
        · exact congrArg (fun n => Sum.inr (Sum.inl n)) (ih (by simpa [leftInterval] using hij))
        · simp [leftInterval] at hij
        · simp [leftInterval] at hij
        · exact congrArg (fun n => Sum.inr (Sum.inr n)) (ih (by simpa [leftInterval] using hij))

theorem leftInterval_sets (r : ℕ) (n : Node r) : intervalSets r (leftInterval r n) = left r n := by
  induction r with
  | zero => exact Empty.elim n
  | succ r ih =>
      rcases n with u | n
      · simp [leftInterval, intervalSets, left]
      · rcases n with n | n <;> simp [leftInterval, intervalSets, left, ih]

end SKConstants.DyadicCore

namespace SKConstants

open scoped Matrix Matrix.Norms.L2Operator RealInnerProductSpace

@[expose] def dyadicIntervalSets (r : ℕ) (I : DyadicCore.Interval r) : Finset (Fin (2 ^ r)) :=
  (DyadicCore.intervalSets r I).map
    (Fin.castOrderIso (DyadicCore.leafCount_eq_pow r)).toEmbedding

theorem dyadicInterval_incidence_eq (r : ℕ) (i : Fin (2 ^ r)) :
    (∑ I : DyadicCore.Interval r, if i ∈ dyadicIntervalSets r I then (1 : ℝ) else 0) = r + 1 := by
  let e := Fin.castOrderIso (DyadicCore.leafCount_eq_pow r)
  convert DyadicCore.interval_incidence_eq r (e.symm i) using 1
  apply Finset.sum_congr rfl
  intro I _
  simp only [dyadicIntervalSets, Finset.mem_map_equiv]
  rfl

theorem dyadicIntervalSets_nonempty (r : ℕ) (I : DyadicCore.Interval r) :
    (dyadicIntervalSets r I).Nonempty := (DyadicCore.intervalSets_nonempty r I).map

theorem dyadicIntervalSets_laminar (r : ℕ) (I J : DyadicCore.Interval r) :
    dyadicIntervalSets r I ⊆ dyadicIntervalSets r J ∨
      dyadicIntervalSets r J ⊆ dyadicIntervalSets r I ∨
      Disjoint (dyadicIntervalSets r I) (dyadicIntervalSets r J) := by
  rcases DyadicCore.intervalSets_laminar r I J with h | h | h
  · exact Or.inl ((Finset.map_subset_map).2 h)
  · exact Or.inr (Or.inl ((Finset.map_subset_map).2 h))
  · exact Or.inr (Or.inr ((Finset.disjoint_map _).2 h))

@[simp] theorem dyadic_rightInterval_sets (r : ℕ) (n : DyadicCore.Node r) :
    dyadicIntervalSets r (DyadicCore.rightInterval r n) = dyadicRight r n := by
  simp only [dyadicIntervalSets, dyadicRight, DyadicCore.rightInterval_sets]

@[simp] theorem dyadic_leftInterval_sets (r : ℕ) (n : DyadicCore.Node r) :
    dyadicIntervalSets r (DyadicCore.leftInterval r n) = dyadicLeft r n := by
  simp only [dyadicIntervalSets, dyadicLeft, DyadicCore.leftInterval_sets]

@[simp] theorem dyadic_rootInterval_sets (r : ℕ) :
    dyadicIntervalSets r (DyadicCore.rootInterval r) = Finset.univ := by
  simp only [dyadicIntervalSets, DyadicCore.rootInterval_sets]
  exact Finset.map_univ_equiv (Fin.castOrderIso (DyadicCore.leafCount_eq_pow r)).toEquiv

@[expose] def dyadicSingletonInterval (r : ℕ) (i : Fin (2 ^ r)) : DyadicCore.Interval r :=
  DyadicCore.singletonInterval r ((Fin.castOrderIso (DyadicCore.leafCount_eq_pow r)).symm i)

theorem dyadicSingletonInterval_injective (r : ℕ) : Function.Injective (dyadicSingletonInterval r) :=
  (DyadicCore.singletonInterval_injective r).comp
    (Fin.castOrderIso (DyadicCore.leafCount_eq_pow r)).symm.injective

@[simp] theorem dyadicSingletonInterval_sets (r : ℕ) (i : Fin (2 ^ r)) :
    dyadicIntervalSets r (dyadicSingletonInterval r i) = {i} := by
  simp only [dyadicIntervalSets, dyadicSingletonInterval, DyadicCore.singletonInterval_sets,
    Finset.map_singleton, RelIso.coe_toEmbedding]
  exact congrArg (fun j => ({j} : Finset (Fin (2 ^ r))))
    ((Fin.castOrderIso (DyadicCore.leafCount_eq_pow r)).apply_symm_apply i)

@[expose] def dyadicMatrixSeminorm (r : ℕ) (w : EuclideanSpace ℝ (Fin (2 ^ r))) :
    Seminorm ℝ (Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ) :=
  projectedMatrixSeminorm (dyadicIntervalSets r) w

theorem dyadicMatrixSeminorm_le (r : ℕ) (w : EuclideanSpace ℝ (Fin (2 ^ r)))
    (A : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ) :
    dyadicMatrixSeminorm r w A ≤ Real.sqrt (r + 1 : ℕ) * ‖A‖ * ‖w‖ := by
  apply projectedMatrixSeminorm_le
  · positivity
  · intro i
    have h := dyadicInterval_incidence_eq r i
    exact h.le.trans (by push_cast; rfl)

theorem dyadic_singleton_image_energy_le (r : ℕ)
    (Y : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ) (w : EuclideanSpace ℝ (Fin (2 ^ r))) :
    (∑ i : Fin (2 ^ r), ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) Y
      (coordinateProjection {i} w)‖ ^ 2) ≤ dyadicMatrixSeminorm r w Y ^ 2 := by
  let e : Fin (2 ^ r) ↪ DyadicCore.Interval r :=
    ⟨dyadicSingletonInterval r, dyadicSingletonInterval_injective r⟩
  change _ ≤ projectedMatrixSeminorm (dyadicIntervalSets r) w Y ^ 2
  rw [projectedMatrixSeminorm_sq]
  calc
    _ = ∑ I ∈ Finset.univ.map e,
        ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) Y
          (coordinateProjection (dyadicIntervalSets r I) w)‖ ^ 2 := by
      simp [Finset.sum_map, e]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun I _ _ => sq_nonneg _)

theorem dyadic_left_image_energy_le (r : ℕ)
    (X : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ) (a : EuclideanSpace ℝ (Fin (2 ^ r))) :
    (∑ n : DyadicCore.Node r, ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) X
      (coordinateProjection (dyadicLeft r n) a)‖ ^ 2) ≤ dyadicMatrixSeminorm r a X ^ 2 := by
  let e : DyadicCore.Node r ↪ DyadicCore.Interval r :=
    ⟨DyadicCore.leftInterval r, DyadicCore.leftInterval_injective r⟩
  change _ ≤ projectedMatrixSeminorm (dyadicIntervalSets r) a X ^ 2
  rw [projectedMatrixSeminorm_sq]
  calc
    _ = ∑ I ∈ Finset.univ.map e,
        ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) X
          (coordinateProjection (dyadicIntervalSets r I) a)‖ ^ 2 := by simp [Finset.sum_map, e]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun I _ _ => sq_nonneg _)

theorem dyadic_right_image_energy_le (r : ℕ)
    (Y : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ) (b : EuclideanSpace ℝ (Fin (2 ^ r))) :
    (∑ n : DyadicCore.Node r, ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) Y
      (coordinateProjection (dyadicRight r n) b)‖ ^ 2) ≤ dyadicMatrixSeminorm r b Y ^ 2 := by
  let e : DyadicCore.Node r ↪ DyadicCore.Interval r :=
    ⟨DyadicCore.rightInterval r, DyadicCore.rightInterval_injective r⟩
  change _ ≤ projectedMatrixSeminorm (dyadicIntervalSets r) b Y ^ 2
  rw [projectedMatrixSeminorm_sq]
  calc
    _ = ∑ I ∈ Finset.univ.map e,
        ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) Y
          (coordinateProjection (dyadicIntervalSets r I) b)‖ ^ 2 := by simp [Finset.sum_map, e]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun I _ _ => sq_nonneg _)

theorem dyadic_root_image_norm_le (r : ℕ)
    (X : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ) (a : EuclideanSpace ℝ (Fin (2 ^ r))) :
    ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) X a‖ ≤ dyadicMatrixSeminorm r a X := by
  apply (sq_le_sq₀ (norm_nonneg _) (apply_nonneg _ _)).mp
  change _ ≤ projectedMatrixSeminorm (dyadicIntervalSets r) a X ^ 2
  rw [projectedMatrixSeminorm_sq]
  have h := Finset.single_le_sum (fun I (_ : I ∈ (Finset.univ : Finset (DyadicCore.Interval r))) =>
    sq_nonneg ‖Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) X
      (coordinateProjection (dyadicIntervalSets r I) a)‖) (Finset.mem_univ (DyadicCore.rootInterval r))
  have hp : coordinateProjection (Finset.univ : Finset (Fin (2 ^ r))) a = a := by ext i; simp
  simpa only [dyadic_rootInterval_sets, hp] using h

theorem dyadicMatrixSeminorm_mul_le (r : ℕ)
    (w : EuclideanSpace ℝ (Fin (2 ^ r)))
    (X Y : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ) :
    dyadicMatrixSeminorm r w (X * Y) ≤ ‖X‖ * dyadicMatrixSeminorm r w Y := by
  apply (sq_le_sq₀ (apply_nonneg _ _) (mul_nonneg (norm_nonneg _) (apply_nonneg _ _))).mp
  simp only [dyadicMatrixSeminorm, projectedMatrixSeminorm_sq, mul_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I _
  rw [map_mul, mul_apply_eq_comp]
  have hh := (Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) X).le_opNorm
    (Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) Y
      (coordinateProjection (dyadicIntervalSets r I) w))
  rw [Matrix.l2_opNorm_toEuclideanCLM] at hh
  simpa only [mul_pow] using
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hh

theorem dyadicMatrixSeminorm_add_vector_le (r : ℕ)
    (s u : EuclideanSpace ℝ (Fin (2 ^ r)))
    (X : Matrix (Fin (2 ^ r)) (Fin (2 ^ r)) ℝ) :
    dyadicMatrixSeminorm r (s + u) X ≤
      dyadicMatrixSeminorm r s X + dyadicMatrixSeminorm r u X := by
  change ‖projectedMatrixFeatureMap (dyadicIntervalSets r) (s + u) X‖ ≤
    ‖projectedMatrixFeatureMap (dyadicIntervalSets r) s X‖ +
      ‖projectedMatrixFeatureMap (dyadicIntervalSets r) u X‖
  have hp (I : Finset (Fin (2 ^ r))) :
      coordinateProjection I (s + u) = coordinateProjection I s + coordinateProjection I u := by
    ext i
    simp only [coordinateProjection_apply, PiLp.add_apply]
    split_ifs <;> simp
  have heq : projectedMatrixFeatureMap (dyadicIntervalSets r) (s + u) X =
      projectedMatrixFeatureMap (dyadicIntervalSets r) s X +
        projectedMatrixFeatureMap (dyadicIntervalSets r) u X := by
    ext p
    change Matrix.toEuclideanCLM (n := Fin (2 ^ r)) (𝕜 := ℝ) X
      (coordinateProjection (dyadicIntervalSets r p.1) (s + u)) p.2 = _
    rw [hp, map_add]
    rfl
  rw [heq]
  exact norm_add_le _ _

end SKConstants
