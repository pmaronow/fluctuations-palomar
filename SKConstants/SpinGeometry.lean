module

public import SKConstants.GibbsComparison
public import SKConstants.HeatBath
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Data.Nat.Choose.Bounds

public section
noncomputable section
open scoped Classical Matrix Matrix.Norms.L2Operator RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

theorem spinEuclidean_norm {n : ℕ} (x : Spin n) :
    ‖spinEuclidean x‖ = Real.sqrt (n : ℝ) := by
  rw [← Real.sqrt_sq (norm_nonneg (spinEuclidean x)), spinEuclidean_norm_sq]

theorem signedSpin_flipSpin {n : ℕ} (x : Spin n) (i j : Fin n) :
    signedSpin (flipSpin x i) j = if j = i then -signedSpin x j else signedSpin x j := by
  by_cases hji : j = i
  · subst j
    cases hx : x i <;> simp [signedSpin, flipSpin, hx]
  · simp only [ite_eq_right hji, signedSpin, flipSpin_apply_ne x i j hji]

theorem spinEuclidean_flip_distance {n : ℕ} (x : Spin n) (i : Fin n) :
    ‖spinEuclidean (flipSpin x i) - spinEuclidean x‖ = 2 := by
  have hsq : ‖spinEuclidean (flipSpin x i) - spinEuclidean x‖ ^ 2 = 4 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ j : Fin n, (signedSpin (flipSpin x i) j - signedSpin x j) ^ 2) = 4
    rw [Finset.sum_eq_single i]
    · rw [signedSpin_flipSpin]
      simp only [ite_true]
      nlinarith [signedSpin_sq x i]
    · intro j _ hji
      rw [signedSpin_flipSpin, ite_eq_right hji]
      simp
    · simp
  have hnonneg := norm_nonneg (spinEuclidean (flipSpin x i) - spinEuclidean x)
  nlinarith

theorem quadraticHamiltonian_spin_difference_bound {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (x y : Spin n) :
    |quadraticHamiltonian W x - quadraticHamiltonian W y| ≤
      ‖spinEuclidean x - spinEuclidean y‖ * Real.sqrt (n : ℝ) * ‖W‖ := by
  let A := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) W
  let u := spinEuclidean x
  let v := spinEuclidean y
  have hdecomp : quadraticHamiltonian W x - quadraticHamiltonian W y =
      (1 / 2) * (inner (𝕜 := ℝ) (u - v) (A u) + inner (𝕜 := ℝ) v (A (u - v))) := by
    rw [quadraticHamiltonian_eq_inner, quadraticHamiltonian_eq_inner]
    dsimp only [u, v, A]
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  have hop1 := A.le_opNorm u
  have hop2 := A.le_opNorm (u - v)
  have hAnorm : ‖A‖ = ‖W‖ := Matrix.l2_opNorm_toEuclideanCLM W
  rw [hAnorm] at hop1 hop2
  have h1 := (abs_real_inner_le_norm (u - v) (A u)).trans
    (mul_le_mul_of_nonneg_left hop1 (norm_nonneg _))
  have h2 := (abs_real_inner_le_norm v (A (u - v))).trans
    (mul_le_mul_of_nonneg_left hop2 (norm_nonneg _))
  have hu : ‖u‖ = Real.sqrt (n : ℝ) := spinEuclidean_norm x
  have hv : ‖v‖ = Real.sqrt (n : ℝ) := spinEuclidean_norm y
  rw [hu] at h1
  rw [hv] at h2
  rw [hdecomp, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc
    (1 / 2) * |inner (𝕜 := ℝ) (u - v) (A u) + inner (𝕜 := ℝ) v (A (u - v))| ≤
        (1 / 2) * (|inner (𝕜 := ℝ) (u - v) (A u)| + |inner (𝕜 := ℝ) v (A (u - v))|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (by norm_num)
    _ ≤ (1 / 2) * (‖u - v‖ * (‖W‖ * Real.sqrt (n : ℝ)) +
        Real.sqrt (n : ℝ) * (‖W‖ * ‖u - v‖)) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by norm_num)
    _ = _ := by dsimp only [u, v]; ring

theorem quadraticHamiltonian_flip_opNorm_bound {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) (i : Fin n) :
    |quadraticHamiltonian W (flipSpin x i) - quadraticHamiltonian W x| ≤
      2 * Real.sqrt (n : ℝ) * ‖W‖ := by
  simpa only [spinEuclidean_flip_distance] using
    quadraticHamiltonian_spin_difference_bound W (flipSpin x i) x

theorem quadraticHamiltonian_flip_add_diagonal {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (x : Spin n) (i : Fin n) :
    quadraticHamiltonian (W + Matrix.diagonal d) (flipSpin x i) -
      quadraticHamiltonian (W + Matrix.diagonal d) x =
        quadraticHamiltonian W (flipSpin x i) - quadraticHamiltonian W x := by
  rw [quadraticHamiltonian_add, quadraticHamiltonian_add,
    quadraticHamiltonian_diagonal, quadraticHamiltonian_diagonal]
  ring

theorem quadraticHamiltonian_flip_add_diagonal_opNorm_bound {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (x : Spin n) (i : Fin n) :
    |quadraticHamiltonian (W + Matrix.diagonal d) (flipSpin x i) -
      quadraticHamiltonian (W + Matrix.diagonal d) x| ≤
        2 * Real.sqrt (n : ℝ) * ‖W‖ := by
  rw [quadraticHamiltonian_flip_add_diagonal]
  exact quadraticHamiltonian_flip_opNorm_bound W x i

@[expose] def spinDifferenceSet {n : ℕ} (x y : Spin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ≠ y i)

@[expose] def spinHammingBall {n : ℕ} (x : Spin n) (r : ℕ) : Finset (Spin n) :=
  Finset.univ.filter (fun y => hammingDist x y ≤ r)

@[expose] def spinHammingEnlargement {n : ℕ} (S : Finset (Spin n)) (r : ℕ) : Finset (Spin n) :=
  S.biUnion (fun x => spinHammingBall x r)

theorem spinEuclidean_distance_sq {n : ℕ} (x y : Spin n) :
    ‖spinEuclidean x - spinEuclidean y‖ ^ 2 = 4 * (hammingDist x y : ℝ) := by
  have hterm : ∀ i : Fin n, (signedSpin x i - signedSpin y i) ^ 2 =
      if x i ≠ y i then (4 : ℝ) else 0 := by
    intro i
    cases hx : x i <;> cases hy : y i <;> simp [signedSpin, hx, hy] <;> norm_num
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i : Fin n, (signedSpin x i - signedSpin y i) ^ 2) = _
  calc
    _ = ∑ i ∈ spinDifferenceSet x y, (4 : ℝ) := by
      simp only [spinDifferenceSet, Finset.sum_filter, hterm]
    _ = 4 * (hammingDist x y : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      change (hammingDist x y : ℝ) * 4 = 4 * (hammingDist x y : ℝ)
      ring

theorem spinEuclidean_distance {n : ℕ} (x y : Spin n) :
    ‖spinEuclidean x - spinEuclidean y‖ = 2 * Real.sqrt (hammingDist x y : ℝ) := by
  have hsq := spinEuclidean_distance_sq x y
  have hsqrt := Real.sq_sqrt (Nat.cast_nonneg (hammingDist x y) : (0 : ℝ) ≤ _)
  have hn := norm_nonneg (spinEuclidean x - spinEuclidean y)
  have hsr := Real.sqrt_nonneg (hammingDist x y : ℝ)
  nlinarith

theorem quadraticHamiltonian_hamming_opNorm_bound {n : ℕ}
    (W : Matrix (Fin n) (Fin n) ℝ) (x y : Spin n) (r : ℕ) (hxy : hammingDist x y ≤ r) :
    |quadraticHamiltonian W x - quadraticHamiltonian W y| ≤
      2 * Real.sqrt (r : ℝ) * Real.sqrt (n : ℝ) * ‖W‖ := by
  have h := quadraticHamiltonian_spin_difference_bound W x y
  rw [spinEuclidean_distance] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hxy)) (by norm_num))
      (Real.sqrt_nonneg _)) (norm_nonneg _))

theorem gibbsProbability_spin_comparison {n : ℕ} (beta L : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x y : Spin n)
    (henergy : |quadraticHamiltonian W x - quadraticHamiltonian W y| ≤ L) :
    gibbsProbability beta W x ≤ Real.exp (|beta| * L) * gibbsProbability beta W y := by
  have hlog : Real.log (gibbsProbability beta W x / gibbsProbability beta W y) =
      beta * (quadraticHamiltonian W x - quadraticHamiltonian W y) := by
    rw [Real.log_div (gibbsProbability_pos beta W x).ne' (gibbsProbability_pos beta W y).ne',
      log_gibbsProbability, log_gibbsProbability]
    ring
  have hab : |beta * (quadraticHamiltonian W x - quadraticHamiltonian W y)| ≤ |beta| * L := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left henergy (abs_nonneg beta)
  have hlogbound : Real.log (gibbsProbability beta W x / gibbsProbability beta W y) ≤ |beta| * L := by
    rw [hlog]
    exact (le_abs_self _).trans hab
  have h := (Real.log_le_iff_le_exp (div_pos
    (gibbsProbability_pos beta W x) (gibbsProbability_pos beta W y))).mp hlogbound
  exact (div_le_iff₀ (gibbsProbability_pos beta W y)).mp h

theorem spinDifferenceSet_injective {n : ℕ} (x : Spin n) :
    Function.Injective (spinDifferenceSet x) := by
  intro y z h
  funext i
  have hi : (x i ≠ y i) ↔ (x i ≠ z i) := by
    simpa only [spinDifferenceSet, Finset.mem_filter, Finset.mem_univ, true_and] using
      (Finset.ext_iff.mp h i)
  cases hx : x i <;> cases hy : y i <;> cases hz : z i <;> simp_all

theorem spinHammingBall_card_le_binomial {n : ℕ} (x : Spin n) (r : ℕ) :
    (spinHammingBall x r).card ≤ ∑ k ∈ Finset.range (r + 1), n.choose k := by
  let sets := (Finset.range (r + 1)).biUnion
    (fun k => (Finset.univ : Finset (Fin n)).powersetCard k)
  have hsub : (spinHammingBall x r).image (spinDifferenceSet x) ⊆ sets := by
    intro U hU
    obtain ⟨y, hy, hyU⟩ := Finset.mem_image.mp hU
    subst U
    apply Finset.mem_biUnion.mpr
    refine ⟨hammingDist x y, ?_, ?_⟩
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le ((Finset.mem_filter.mp hy).2))
    · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩
  calc
    (spinHammingBall x r).card = ((spinHammingBall x r).image (spinDifferenceSet x)).card :=
      (Finset.card_image_of_injective _ (spinDifferenceSet_injective x)).symm
    _ ≤ sets.card := Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range (r + 1), ((Finset.univ : Finset (Fin n)).powersetCard k).card :=
      Finset.card_biUnion_le
    _ = _ := by simp

theorem spinHammingBall_card_le_pow {n : ℕ} (x : Spin n) (r : ℕ) :
    (spinHammingBall x r).card ≤ (r + 1) * (n + 1) ^ r := by
  apply (spinHammingBall_card_le_binomial x r).trans
  calc
    (∑ k ∈ Finset.range (r + 1), n.choose k) ≤
        ∑ _k ∈ Finset.range (r + 1), (n + 1) ^ r := by
      apply Finset.sum_le_sum
      intro k hk
      calc
        n.choose k ≤ n ^ k := Nat.choose_le_pow n k
        _ ≤ (n + 1) ^ k := Nat.pow_le_pow_left (Nat.le_succ n) _
        _ ≤ (n + 1) ^ r := Nat.pow_le_pow_right (by omega) (by have hk' := Finset.mem_range.mp hk; omega)
    _ = _ := by simp

theorem hammingDist_flipSpin_self {n : ℕ} (x : Spin n) (i : Fin n) :
    hammingDist x (flipSpin x i) = 1 := by
  have h := spinEuclidean_distance_sq (flipSpin x i) x
  rw [spinEuclidean_flip_distance] at h
  have hc : (hammingDist (flipSpin x i) x : ℝ) = 1 := by nlinarith
  rw [hammingDist_comm]
  exact_mod_cast hc

theorem spinDifferenceSet_flipSpin_erase {n : ℕ} (x y : Spin n) (i : Fin n)
    (hi : x i ≠ y i) :
    spinDifferenceSet (flipSpin x i) y = (spinDifferenceSet x y).erase i := by
  ext j
  by_cases hji : j = i
  · subst j
    have hflip : (!(x i)) = y i := by
      cases hx : x i <;> cases hy : y i <;> simp_all
    simp [spinDifferenceSet, hflip]
  · simp [spinDifferenceSet, flipSpin_apply_ne x i j hji, hji]

theorem hammingDist_flipSpin_decreases {n : ℕ} (x y : Spin n) (i : Fin n)
    (hi : x i ≠ y i) :
    hammingDist (flipSpin x i) y + 1 = hammingDist x y := by
  change (spinDifferenceSet (flipSpin x i) y).card + 1 = (spinDifferenceSet x y).card
  rw [spinDifferenceSet_flipSpin_erase x y i hi]
  exact Finset.card_erase_add_one (by simp [spinDifferenceSet, hi])

end SKConstants
