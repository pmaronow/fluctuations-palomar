module

public import SKConstants.FiniteGibbs

public section
noncomputable section

namespace SKConstants

/-- Flip exactly site `i` of a Boolean spin configuration. -/
@[expose] def flipSpin {n : ℕ} (x : Spin n) (i : Fin n) : Spin n :=
  Function.update x i (!(x i))

@[simp] theorem flipSpin_apply_same {n : ℕ} (x : Spin n) (i : Fin n) :
    flipSpin x i i = !(x i) := by
  simp [flipSpin]

theorem flipSpin_apply_ne {n : ℕ} (x : Spin n) (i j : Fin n) (hji : j ≠ i) :
    flipSpin x i j = x j := by
  simp [flipSpin, hji]

@[simp] theorem flipSpin_flipSpin {n : ℕ} (x : Spin n) (i : Fin n) :
    flipSpin (flipSpin x i) i = x := by
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [flipSpin_apply_ne x i j hji, flipSpin_apply_ne (flipSpin x i) i j hji]

theorem flipSpin_ne {n : ℕ} (x : Spin n) (i : Fin n) : flipSpin x i ≠ x := by
  intro h
  have hi := congrFun h i
  cases hxi : x i <;> simp [flipSpin, hxi] at hi

/-- Given that site `i` is selected, the heat-bath probability of changing its
spin. It is the Gibbs weight of the flipped state divided by the two-state
conditional partition function. -/
@[expose] def heatBathFlipRate {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) (i : Fin n) : ℝ :=
  Real.exp (beta * quadraticHamiltonian W (flipSpin x i)) /
    (Real.exp (beta * quadraticHamiltonian W x) +
      Real.exp (beta * quadraticHamiltonian W (flipSpin x i)))

theorem heatBathFlipRate_pos {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) (i : Fin n) :
    0 < heatBathFlipRate beta W x i := by
  exact div_pos (Real.exp_pos _) (add_pos (Real.exp_pos _) (Real.exp_pos _))

theorem heatBathFlipRate_lt_one {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) (i : Fin n) :
    heatBathFlipRate beta W x i < 1 := by
  unfold heatBathFlipRate
  apply (div_lt_one (add_pos (Real.exp_pos _) (Real.exp_pos _))).2
  linarith [Real.exp_pos (beta * quadraticHamiltonian W x)]

theorem heatBathFlipRate_eq_gibbs_ratio {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) (i : Fin n) :
    heatBathFlipRate beta W x i = gibbsProbability beta W (flipSpin x i) /
      (gibbsProbability beta W x + gibbsProbability beta W (flipSpin x i)) := by
  unfold heatBathFlipRate gibbsProbability
  have hZ : gibbsPartition beta W ≠ 0 := ne_of_gt (gibbsPartition_pos beta W)
  have hD : Real.exp (beta * quadraticHamiltonian W x) +
      Real.exp (beta * quadraticHamiltonian W (flipSpin x i)) ≠ 0 :=
    ne_of_gt (add_pos (Real.exp_pos _) (Real.exp_pos _))
  rw [← add_div]
  field_simp

theorem heatBathFlipRate_detailed_balance {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) (i : Fin n) :
    gibbsProbability beta W x * heatBathFlipRate beta W x i =
      gibbsProbability beta W (flipSpin x i) *
        heatBathFlipRate beta W (flipSpin x i) i := by
  simp only [heatBathFlipRate_eq_gibbs_ratio, flipSpin_flipSpin]
  rw [add_comm (gibbsProbability beta W (flipSpin x i)) (gibbsProbability beta W x)]
  ring

theorem heatBathFlipRate_add_diagonal {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ)
    (x : Spin n) (i : Fin n) :
    heatBathFlipRate beta (W + Matrix.diagonal d) x i =
      heatBathFlipRate beta W x i := by
  simp only [heatBathFlipRate_eq_gibbs_ratio, gibbsProbability_add_diagonal]

/-- The transition probabilities after selecting the single site `i`:
stay in the current configuration or flip that site according to its actual
heat-bath probability. -/
@[expose] def siteHeatBathKernel {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) (i : Fin n) (y : Spin n) : ℝ :=
  (if y = flipSpin x i then heatBathFlipRate beta W x i else 0) +
    (if y = x then 1 - heatBathFlipRate beta W x i else 0)

theorem siteHeatBathKernel_nonneg {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) (i : Fin n) (y : Spin n) :
    0 ≤ siteHeatBathKernel beta W x i y := by
  have hr := (heatBathFlipRate_pos beta W x i).le
  have hs := sub_nonneg.mpr (heatBathFlipRate_lt_one beta W x i).le
  unfold siteHeatBathKernel
  split_ifs <;> linarith

theorem siteHeatBathKernel_sum {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) (i : Fin n) :
    (∑ y : Spin n, siteHeatBathKernel beta W x i y) = 1 := by
  classical
  simp [siteHeatBathKernel, Finset.sum_add_distrib]

theorem siteHeatBathKernel_self {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) (i : Fin n) :
    siteHeatBathKernel beta W x i x = 1 - heatBathFlipRate beta W x i := by
  simp [siteHeatBathKernel, Ne.symm (flipSpin_ne x i)]

theorem siteHeatBathKernel_flip {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) (i : Fin n) :
    siteHeatBathKernel beta W x i (flipSpin x i) = heatBathFlipRate beta W x i := by
  simp [siteHeatBathKernel, flipSpin_ne]

theorem siteHeatBathKernel_detailed_balance {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x y : Spin n) (i : Fin n) :
    gibbsProbability beta W x * siteHeatBathKernel beta W x i y =
      gibbsProbability beta W y * siteHeatBathKernel beta W y i x := by
  by_cases hflip : y = flipSpin x i
  · subst y
    simpa [siteHeatBathKernel, flipSpin_ne, Ne.symm (flipSpin_ne x i)] using
      heatBathFlipRate_detailed_balance beta W x i
  · by_cases heq : y = x
    · subst y
      rfl
    · have hreverse : x ≠ flipSpin y i := by
        intro h
        apply hflip
        rw [h]
        simp
      simp [siteHeatBathKernel, hflip, heq, hreverse, Ne.symm heq]

/-- The actual one-step discrete heat-bath kernel: choose a site uniformly,
then resample its spin from the two-state conditional Gibbs law. The empty
spin space is handled by the real division convention; normalization below
explicitly assumes `n > 0`. -/
@[expose] def heatBathKernel {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x y : Spin n) : ℝ :=
  (∑ i : Fin n, siteHeatBathKernel beta W x i y) / (n : ℝ)

theorem heatBathKernel_nonneg {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x y : Spin n) :
    0 ≤ heatBathKernel beta W x y := by
  apply div_nonneg
  · exact Finset.sum_nonneg (fun i _ => siteHeatBathKernel_nonneg beta W x i y)
  · exact Nat.cast_nonneg n

theorem heatBathKernel_self_pos {n : ℕ} (hn : 0 < n) (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) :
    0 < heatBathKernel beta W x x := by
  apply div_pos _ (Nat.cast_pos.mpr hn)
  apply Finset.sum_pos
  · intro i _
    rw [siteHeatBathKernel_self]
    exact sub_pos.mpr (heatBathFlipRate_lt_one beta W x i)
  · exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem heatBathKernel_flip_pos {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) (i : Fin n) :
    0 < heatBathKernel beta W x (flipSpin x i) := by
  apply div_pos _ (Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt))
  apply (heatBathFlipRate_pos beta W x i).trans_le
  rw [← siteHeatBathKernel_flip beta W x i]
  exact Finset.single_le_sum (fun j _ =>
    siteHeatBathKernel_nonneg beta W x j (flipSpin x i)) (Finset.mem_univ i)

theorem heatBathKernel_sum {n : ℕ} (hn : 0 < n) (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) :
    (∑ y : Spin n, heatBathKernel beta W x y) = 1 := by
  classical
  unfold heatBathKernel
  rw [← Finset.sum_div, Finset.sum_comm]
  simp only [siteHeatBathKernel_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))

theorem heatBathKernel_detailed_balance {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x y : Spin n) :
    gibbsProbability beta W x * heatBathKernel beta W x y =
      gibbsProbability beta W y * heatBathKernel beta W y x := by
  unfold heatBathKernel
  rw [← mul_div_assoc, ← mul_div_assoc, Finset.mul_sum, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => siteHeatBathKernel_detailed_balance beta W x y i)

theorem heatBathKernel_gibbs_stationary {n : ℕ} (hn : 0 < n) (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (y : Spin n) :
    (∑ x : Spin n, gibbsProbability beta W x * heatBathKernel beta W x y) =
      gibbsProbability beta W y := by
  calc
    (∑ x : Spin n, gibbsProbability beta W x * heatBathKernel beta W x y) =
        ∑ x : Spin n, gibbsProbability beta W y * heatBathKernel beta W y x :=
      Finset.sum_congr rfl (fun x _ => heatBathKernel_detailed_balance beta W x y)
    _ = gibbsProbability beta W y * ∑ x : Spin n, heatBathKernel beta W y x := by
      rw [Finset.mul_sum]
    _ = gibbsProbability beta W y := by rw [heatBathKernel_sum hn]; simp

theorem heatBathKernel_add_diagonal {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (x y : Spin n) :
    heatBathKernel beta (W + Matrix.diagonal d) x y = heatBathKernel beta W x y := by
  simp only [heatBathKernel, siteHeatBathKernel, heatBathFlipRate_add_diagonal]

end SKConstants
