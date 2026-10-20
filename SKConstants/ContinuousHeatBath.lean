module

public import SKConstants.HeatBath
public import SKConstants.FiniteChainMixing
public import SKConstants.JointGibbs

public section
noncomputable section
open scoped Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

@[expose] def continuousHeatBathGenerator {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) : Matrix (Spin n) (Spin n) ℝ :=
  (n : ℝ) • finiteChainGenerator (heatBathKernel beta W)

/-- The actual transition matrix at elapsed physical time `T` for `n`
rate-one update clocks. -/
@[expose] def continuousHeatBathSemigroup {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) : Matrix (Spin n) (Spin n) ℝ :=
  finiteChainSemigroup (heatBathKernel beta W) ((n : ℝ) * T)

@[expose] def continuousHeatBathAverageMixing {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) : ℝ :=
  finiteAveragedTV (gibbsProbability beta W) (continuousHeatBathSemigroup beta W T)

theorem continuousHeatBathSemigroup_eq_exp {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) :
    continuousHeatBathSemigroup beta W T =
      NormedSpace.exp (T • continuousHeatBathGenerator beta W) := by
  unfold continuousHeatBathSemigroup continuousHeatBathGenerator finiteChainSemigroup
  rw [smul_smul, mul_comm T (n : ℝ)]

theorem heatBathKernel_stochastic {n : ℕ} (hn : 0 < n) (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) :
    heatBathKernel beta W ∈ Matrix.rowStochastic ℝ (Spin n) := by
  exact Matrix.mem_rowStochastic_iff_sum.mpr
    ⟨heatBathKernel_nonneg beta W, heatBathKernel_sum hn beta W⟩

theorem continuousHeatBathSemigroup_stochastic {n : ℕ} (hn : 0 < n) (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) (hT : 0 ≤ T) :
    continuousHeatBathSemigroup beta W T ∈ Matrix.rowStochastic ℝ (Spin n) :=
  finiteChainSemigroup_stochastic _ (heatBathKernel_stochastic hn beta W) _
    (mul_nonneg (Nat.cast_nonneg n) hT)

@[simp] theorem continuousHeatBathSemigroup_zero {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) : continuousHeatBathSemigroup beta W 0 = 1 := by
  simp [continuousHeatBathSemigroup]

theorem continuousHeatBathSemigroup_add {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (S T : ℝ) :
    continuousHeatBathSemigroup beta W (S + T) =
      continuousHeatBathSemigroup beta W S * continuousHeatBathSemigroup beta W T := by
  unfold continuousHeatBathSemigroup
  rw [mul_add, finiteChainSemigroup_add]

theorem continuousHeatBathSemigroup_detailed_balance {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) (x y : Spin n) :
    gibbsProbability beta W x * continuousHeatBathSemigroup beta W T x y =
      gibbsProbability beta W y * continuousHeatBathSemigroup beta W T y x :=
  finiteChainSemigroup_detailed_balance _ (gibbsProbability beta W)
    (heatBathKernel_detailed_balance beta W) _ x y

theorem continuousHeatBathSemigroup_stationary {n : ℕ} (hn : 0 < n) (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) (hT : 0 ≤ T) (y : Spin n) :
    (∑ x : Spin n, gibbsProbability beta W x *
      continuousHeatBathSemigroup beta W T x y) = gibbsProbability beta W y :=
  finiteChainSemigroup_stationary _ (heatBathKernel_stochastic hn beta W)
    (gibbsProbability beta W) (heatBathKernel_detailed_balance beta W) _
    (mul_nonneg (Nat.cast_nonneg n) hT) y

theorem continuousHeatBathSemigroup_add_diagonal {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (T : ℝ) :
    continuousHeatBathSemigroup beta (W + Matrix.diagonal d) T =
      continuousHeatBathSemigroup beta W T := by
  have hK : heatBathKernel beta (W + Matrix.diagonal d) = heatBathKernel beta W := by
    funext x y
    exact heatBathKernel_add_diagonal beta W d x y
  simp only [continuousHeatBathSemigroup, hK]

theorem continuousHeatBathAverageMixing_antitone {n : ℕ} (hn : 0 < n) (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) {S T : ℝ} (hST : S ≤ T) :
    continuousHeatBathAverageMixing beta W T ≤ continuousHeatBathAverageMixing beta W S := by
  apply finiteChainAverageMixing_antitone _ (heatBathKernel_stochastic hn beta W)
    (gibbsProbability beta W) (fun x => (gibbsProbability_pos beta W x).le)
    (heatBathKernel_detailed_balance beta W)
  exact mul_le_mul_of_nonneg_left hST (Nat.cast_nonneg n)

theorem continuousHeatBathAverageMixing_add_diagonal {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ) (T : ℝ) :
    continuousHeatBathAverageMixing beta (W + Matrix.diagonal d) T =
      continuousHeatBathAverageMixing beta W T := by
  have hpi : gibbsProbability beta (W + Matrix.diagonal d) = gibbsProbability beta W := by
    funext x
    exact gibbsProbability_add_diagonal beta W d x
  simp only [continuousHeatBathAverageMixing, continuousHeatBathSemigroup_add_diagonal, hpi]

@[expose] def continuousHeatBathJumpRate {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x y : Spin n) : ℝ :=
  if x = y then 0 else (n : ℝ) * heatBathKernel beta W x y

@[simp] theorem continuousHeatBathJumpRate_self {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) :
    continuousHeatBathJumpRate beta W x x = 0 := by simp [continuousHeatBathJumpRate]

theorem continuousHeatBathJumpRate_nonneg {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x y : Spin n) :
    0 ≤ continuousHeatBathJumpRate beta W x y := by
  unfold continuousHeatBathJumpRate
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (Nat.cast_nonneg n) (heatBathKernel_nonneg beta W x y)

theorem continuousHeatBathGenerator_offdiag {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x y : Spin n) (hxy : x ≠ y) :
    continuousHeatBathGenerator beta W x y = continuousHeatBathJumpRate beta W x y := by
  simp [continuousHeatBathGenerator, finiteChainGenerator, continuousHeatBathJumpRate, hxy]

theorem continuousHeatBathJumpRate_detailed_balance {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x y : Spin n) :
    gibbsProbability beta W x * continuousHeatBathJumpRate beta W x y =
      gibbsProbability beta W y * continuousHeatBathJumpRate beta W y x := by
  by_cases hxy : x = y
  · subst y
    rfl
  · simp only [continuousHeatBathJumpRate, hxy, Ne.symm hxy, ite_false]
    calc
      gibbsProbability beta W x * ((n : ℝ) * heatBathKernel beta W x y) =
          (n : ℝ) * (gibbsProbability beta W x * heatBathKernel beta W x y) := by ring
      _ = (n : ℝ) * (gibbsProbability beta W y * heatBathKernel beta W y x) := by
        rw [heatBathKernel_detailed_balance]
      _ = gibbsProbability beta W y * ((n : ℝ) * heatBathKernel beta W y x) := by ring

theorem continuousHeatBathJumpRate_sum_le {n : ℕ} (hn : 0 < n) (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) :
    (∑ y : Spin n, continuousHeatBathJumpRate beta W x y) ≤ (n : ℝ) := by
  calc
    (∑ y : Spin n, continuousHeatBathJumpRate beta W x y) ≤
        ∑ y : Spin n, (n : ℝ) * heatBathKernel beta W x y := by
      apply Finset.sum_le_sum
      intro y _
      unfold continuousHeatBathJumpRate
      split_ifs
      · exact mul_nonneg (Nat.cast_nonneg n) (heatBathKernel_nonneg beta W x y)
      · exact le_rfl
    _ = (n : ℝ) := by rw [← Finset.mul_sum, heatBathKernel_sum hn, mul_one]

theorem flipSpin_site_injective {n : ℕ} (x : Spin n) : Function.Injective (flipSpin x) := by
  intro i j h
  by_contra hij
  have hi := congrFun h i
  rw [flipSpin_apply_same, flipSpin_apply_ne x j i hij] at hi
  cases hxi : x i <;> simp [hxi] at hi

theorem continuousHeatBathJumpRate_eq_site_sum {n : ℕ} (hn : 0 < n) (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x y : Spin n) :
    continuousHeatBathJumpRate beta W x y =
      ∑ i : Fin n, if y = flipSpin x i then heatBathFlipRate beta W x i else 0 := by
  by_cases hxy : x = y
  · subst y
    simp [continuousHeatBathJumpRate, Ne.symm (flipSpin_ne x _)]
  · have hyx := Ne.symm hxy
    simp only [continuousHeatBathJumpRate, hxy, ite_false, heatBathKernel]
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
    rw [mul_div_cancel₀ _ hnR]
    apply Finset.sum_congr rfl
    intro i _
    simp [siteHeatBathKernel, hyx]

theorem continuousHeatBathJumpRate_flip {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x : Spin n) (i : Fin n) :
    continuousHeatBathJumpRate beta W x (flipSpin x i) = heatBathFlipRate beta W x i := by
  rw [continuousHeatBathJumpRate_eq_site_sum (Nat.zero_lt_of_lt i.isLt)]
  simp only [(flipSpin_site_injective x).eq_iff]
  simp

theorem continuousHeatBathTV_le_one {n : ℕ} (hn : 0 < n) (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) (hT : 0 ≤ T) (x : Spin n) :
    finiteTotalVariation (continuousHeatBathSemigroup beta W T x)
      (gibbsProbability beta W) ≤ 1 :=
  finiteTotalVariation_le_one _ _
    (fun _ => Matrix.nonneg_of_mem_rowStochastic
      (continuousHeatBathSemigroup_stochastic hn beta W T hT))
    (fun y => (gibbsProbability_pos beta W y).le)
    (Matrix.sum_row_of_mem_rowStochastic
      (continuousHeatBathSemigroup_stochastic hn beta W T hT) x)
    (gibbsProbability_sum beta W)

theorem continuousHeatBathAverageMixing_le_one {n : ℕ} (hn : 0 < n) (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) (hT : 0 ≤ T) :
    continuousHeatBathAverageMixing beta W T ≤ 1 :=
  finiteAveragedTV_le_one _ _ (fun x => (gibbsProbability_pos beta W x).le)
    (gibbsProbability_sum beta W) (continuousHeatBathSemigroup_stochastic hn beta W T hT)

theorem continuousHeatBathAverageMixing_nonneg {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (T : ℝ) :
    0 ≤ continuousHeatBathAverageMixing beta W T :=
  finiteAveragedTV_nonneg _ _ (fun x => (gibbsProbability_pos beta W x).le)

theorem continuous_heatBathFlipRate {n : ℕ} (beta : ℝ) (x : Spin n) (i : Fin n) :
    Continuous (fun W : Matrix (Fin n) (Fin n) ℝ => heatBathFlipRate beta W x i) := by
  unfold heatBathFlipRate
  apply Continuous.div
  · exact Real.continuous_exp.comp (continuous_const.mul (continuous_quadraticHamiltonian _))
  · exact (Real.continuous_exp.comp
      (continuous_const.mul (continuous_quadraticHamiltonian _))).add
      (Real.continuous_exp.comp (continuous_const.mul (continuous_quadraticHamiltonian _)))
  · intro W
    exact (add_pos (Real.exp_pos _) (Real.exp_pos _)).ne'

theorem continuous_heatBathKernel_entry {n : ℕ} (beta : ℝ) (x y : Spin n) :
    Continuous (fun W : Matrix (Fin n) (Fin n) ℝ => heatBathKernel beta W x y) := by
  unfold heatBathKernel
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  unfold siteHeatBathKernel
  split_ifs
  · exact (continuous_heatBathFlipRate beta x i).add
      (continuous_const.sub (continuous_heatBathFlipRate beta x i))
  · simpa using continuous_heatBathFlipRate beta x i
  · have hf := continuous_heatBathFlipRate beta x i
    simp only [zero_add]
    fun_prop
  · exact continuous_const

theorem continuous_continuousHeatBathSemigroup {n : ℕ} (beta T : ℝ) :
    Continuous (fun W : Matrix (Fin n) (Fin n) ℝ => continuousHeatBathSemigroup beta W T) := by
  unfold continuousHeatBathSemigroup finiteChainSemigroup finiteChainGenerator
  apply NormedSpace.exp_continuous.comp
  exact ((continuous_pi (fun x => continuous_pi (fun y =>
    continuous_heatBathKernel_entry beta x y))).sub continuous_const).const_smul ((n : ℝ) * T)

theorem continuous_continuousHeatBathTV {n : ℕ} (beta T : ℝ) (x : Spin n) :
    Continuous (fun W : Matrix (Fin n) (Fin n) ℝ =>
      finiteTotalVariation (continuousHeatBathSemigroup beta W T x) (gibbsProbability beta W)) := by
  unfold finiteTotalVariation
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro y _
  exact (((continuous_apply y).comp ((continuous_apply x).comp
    (continuous_continuousHeatBathSemigroup beta T))).sub
    (continuous_gibbsProbability beta y)).abs

theorem measurable_continuousHeatBathTV {n : ℕ} (beta T : ℝ) (x : Spin n) :
    Measurable (fun W : Matrix (Fin n) (Fin n) ℝ =>
      finiteTotalVariation (continuousHeatBathSemigroup beta W T x) (gibbsProbability beta W)) :=
  (continuous_continuousHeatBathTV beta T x).measurable

theorem continuous_continuousHeatBathAverageMixing {n : ℕ} (beta T : ℝ) :
    Continuous (fun W : Matrix (Fin n) (Fin n) ℝ => continuousHeatBathAverageMixing beta W T) := by
  unfold continuousHeatBathAverageMixing finiteAveragedTV
  exact continuous_finsetSum _ (fun x _ =>
    (continuous_gibbsProbability beta x).mul (continuous_continuousHeatBathTV beta T x))

theorem measurable_continuousHeatBathAverageMixing {n : ℕ} (beta T : ℝ) :
    Measurable (fun W : Matrix (Fin n) (Fin n) ℝ => continuousHeatBathAverageMixing beta W T) :=
  (continuous_continuousHeatBathAverageMixing beta T).measurable

theorem continuousHeatBathJumpRate_dirichlet {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (u : Spin n → ℝ) :
    (1 / 2) * (∑ x, ∑ y, gibbsProbability beta W x *
      continuousHeatBathJumpRate beta W x y * (u x - u y) ^ 2) =
        (n : ℝ) * finiteDirichletForm (gibbsProbability beta W) (heatBathKernel beta W) u := by
  have heach : ∀ x y, gibbsProbability beta W x *
      continuousHeatBathJumpRate beta W x y * (u x - u y) ^ 2 =
        (n : ℝ) * (gibbsProbability beta W x * heatBathKernel beta W x y * (u x - u y) ^ 2) := by
    intro x y
    by_cases hxy : x = y
    · subst y
      simp
    · simp only [continuousHeatBathJumpRate, hxy, ite_false]
      ring
  simp only [heach, finiteDirichletForm, ← Finset.mul_sum]
  ring

@[expose] def continuousHeatBathEdgeFlow {n : ℕ} (beta : ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (x y : Spin n) : ℝ :=
  gibbsProbability beta W x * continuousHeatBathJumpRate beta W x y

theorem continuousHeatBathAverageMixing_of_balanced_flow {n : ℕ} (hn : 0 < n)
    (beta : ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (epsilon B : ℝ) (hepsilon : 0 < epsilon) (hepsilon_third : epsilon < 1 / 3)
    (hB : 0 < B)
    (hbalanced : ∀ S : Finset (Spin n), epsilon ≤ cutMass (gibbsProbability beta W) S →
      cutMass (gibbsProbability beta W) S ≤ 1 - epsilon →
        B < cutFlow (continuousHeatBathEdgeFlow beta W) S Sᶜ)
    (T : ℝ) (hT : 0 < T) :
    continuousHeatBathAverageMixing beta W T ≤
      Real.sqrt (2 * (n : ℝ) * finiteShannonEntropy (gibbsProbability beta W)) /
        (B * Real.sqrt T) + 2 * epsilon := by
  have hq : ∀ x y, 0 ≤ continuousHeatBathEdgeFlow beta W x y :=
    fun x y => mul_nonneg (gibbsProbability_pos beta W x).le
      (continuousHeatBathJumpRate_nonneg beta W x y)
  have hsym : ∀ x y, continuousHeatBathEdgeFlow beta W x y =
      continuousHeatBathEdgeFlow beta W y x := continuousHeatBathJumpRate_detailed_balance beta W
  have hrow : ∀ x, ∑ y, continuousHeatBathEdgeFlow beta W x y ≤
      (n : ℝ) * gibbsProbability beta W x := by
    intro x
    unfold continuousHeatBathEdgeFlow
    rw [← Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left (continuousHeatBathJumpRate_sum_le hn beta W x)
      (gibbsProbability_pos beta W x).le
    simpa only [mul_comm] using h
  have henergy : ∀ u, Cheeger.dirichlet (continuousHeatBathEdgeFlow beta W) u =
      (n : ℝ) * finiteDirichletForm (gibbsProbability beta W) (heatBathKernel beta W) u :=
    continuousHeatBathJumpRate_dirichlet beta W
  exact finiteChain_mixing_of_balanced_flow (heatBathKernel beta W)
    (heatBathKernel_stochastic hn beta W) (gibbsProbability beta W)
    (gibbsProbability_pos beta W) (gibbsProbability_sum beta W)
    (heatBathKernel_detailed_balance beta W) (continuousHeatBathEdgeFlow beta W) hq hsym
    (n : ℝ) (Nat.cast_nonneg n) hrow (n : ℝ) (Nat.cast_pos.mpr hn) henergy
    epsilon B hepsilon hepsilon_third hB hbalanced T hT

theorem continuousHeatBathAverageMixing_of_balanced_flow_card {n : ℕ} (hn : 0 < n)
    (beta : ℝ) (W : Matrix (Fin n) (Fin n) ℝ)
    (epsilon B : ℝ) (hepsilon : 0 < epsilon) (hepsilon_third : epsilon < 1 / 3)
    (hB : 0 < B)
    (hbalanced : ∀ S : Finset (Spin n), epsilon ≤ cutMass (gibbsProbability beta W) S →
      cutMass (gibbsProbability beta W) S ≤ 1 - epsilon →
        B < cutFlow (continuousHeatBathEdgeFlow beta W) S Sᶜ)
    (T : ℝ) (hT : 0 < T) :
    continuousHeatBathAverageMixing beta W T ≤
      (n : ℝ) * Real.sqrt (2 * Real.log 2) / (B * Real.sqrt T) + 2 * epsilon := by
  have h := continuousHeatBathAverageMixing_of_balanced_flow hn beta W epsilon B
    hepsilon hepsilon_third hB hbalanced T hT
  have hH := gibbsShannonEntropy_le beta W
  have hnum : Real.sqrt (2 * (n : ℝ) * finiteShannonEntropy (gibbsProbability beta W)) ≤
      (n : ℝ) * Real.sqrt (2 * Real.log 2) := by
    calc
      Real.sqrt (2 * (n : ℝ) * finiteShannonEntropy (gibbsProbability beta W)) ≤
          Real.sqrt (2 * (n : ℝ) * ((n : ℝ) * Real.log 2)) := by
        apply Real.sqrt_le_sqrt
        exact mul_le_mul_of_nonneg_left hH (by positivity)
      _ = (n : ℝ) * Real.sqrt (2 * Real.log 2) := by
        have heq : 2 * (n : ℝ) * ((n : ℝ) * Real.log 2) = (n : ℝ) ^ 2 * (2 * Real.log 2) := by ring
        rw [heq, Real.sqrt_mul (sq_nonneg (n : ℝ)), Real.sqrt_sq (Nat.cast_nonneg n)]
  exact h.trans (add_le_add (div_le_div_of_nonneg_right hnum (by positivity)) le_rfl)

theorem continuousHeatBathEdgeFlow_cut_site_sum {n : ℕ} (hn : 0 < n)
    (beta : ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Spin n)) :
    cutFlow (continuousHeatBathEdgeFlow beta W) S Sᶜ =
      ∑ x ∈ S, ∑ i : Fin n, if flipSpin x i ∉ S then
        gibbsProbability beta W x * heatBathFlipRate beta W x i else 0 := by
  unfold cutFlow continuousHeatBathEdgeFlow
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [continuousHeatBathJumpRate_eq_site_sum hn, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_ite, mul_zero]
  simp

end SKConstants
