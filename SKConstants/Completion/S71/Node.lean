module

public import SKConstants.Completion.Blueprint5a.Statements
public import SKConstants.Completion.S71.CommonRefinement

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.S71
open SKConstantsOAI.ZeroTemperatureSK Blueprint4 Blueprint5a

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def partitionPotentialSum (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0)
    (N : ℕ) (u : Bool × Ω) : ℝ :=
  ∑ i ∈ Finset.range N, actualParisiFullSusceptibilityExpected W β (t i) *
    (LJ.actualRowPotential W β (t (i + 1)) u - LJ.actualRowPotential W β (t i) u)

theorem measurable_partitionPotentialSum (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (N : ℕ) : Measurable (partitionPotentialSum W β t N) := by
  apply Finset.measurable_fun_sum
  intro i _
  exact ((LJ.measurable_actualRowPotential W β _).sub
    (LJ.measurable_actualRowPotential W β _)).const_mul _

theorem partitionPotentialSum_bound (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (N : ℕ) (u : Bool × Ω) :
    |partitionPotentialSum W β t N u| ≤ 6 := by
  have hh := SJ3.weightedIncrements_bound (actualParisiFullSusceptibilityExpected W β)
    (fun s => LJ.actualRowPotential W β s.toNNReal u) (fun i => (t i : ℝ)) N 2 1
    (by norm_num) (by norm_num)
    (fun i _ => ⟨actualParisiFullSusceptibilityExpected_nonneg W β _,
      LBase.actual_susceptibility_le_one W β _⟩)
    (fun i _ => LBase.actual_susceptibility_antitone W β hβ (NNReal.coe_nonneg _)
      (NNReal.coe_nonneg _) (NNReal.coe_le_coe.mpr (ht (Nat.le_succ i))))
    (fun i _ => SJ3.actualRowPotential_bound W β _ u)
  simpa only [partitionPotentialSum, Real.toNNReal_coe,
    show (3 : ℝ) * 2 * 1 = 6 by norm_num] using hh

theorem partitionPotentialSum_memLp (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (N : ℕ) :
    MemLp (partitionPotentialSum W β t N) 2 ((scalarHiddenPriorBool 0).prod W.law) := by
  let := W.isProbability
  exact (memLp_const (6 : ℝ)).mono'
    (measurable_partitionPotentialSum W β t N).aestronglyMeasurable
    (ae_of_all _ (fun u => by simpa only [Real.norm_eq_abs] using
      partitionPotentialSum_bound W β hβ t ht N u))

theorem partitionPotentialSum_tendsto_ae (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (t : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ)
    (ht : ∀ l, Monotone (t l)) (ht0 : ∀ l, t l 0 = 0) (htV : ∀ l, t l (N l) = V)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hwidth : ∀ l i, i < N l → (t l (i + 1) : ℝ) - t l i ≤ ε l) :
    ∀ᵐ u ∂(scalarHiddenPriorBool 0).prod W.law,
      Tendsto (fun l => partitionPotentialSum W β (t l) (N l) u) atTop
        (𝓝 (SJ3.potentialIntegral W β hβ V u)) := by
  filter_upwards [SJ3.actualRowPotential_continuous_ae W β] with u hu
  have hh := scalarStieltjes_left_sums_tendsto (SJ3.negativeSusceptibility W β hβ)
    (fun s => LJ.actualRowPotential W β s.toNNReal u) hu V V.coe_nonneg
    (fun l i => (t l i : ℝ)) N ε
    (fun l => by rw [ht0 l]; rfl)
    (fun l => by rw [htV l])
    (fun l i hi => ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.mpr
      ((ht l hi).trans_eq (htV l))⟩)
    (fun l i _ => NNReal.coe_le_coe.mpr (ht l (Nat.le_succ i))) hwidth hε
  have he : (fun l => ∑ i ∈ Finset.range (N l), SJ3.negativeSusceptibility W β hβ
      (t l i) * (LJ.actualRowPotential W β ((t l (i + 1) : ℝ).toNNReal) u -
        LJ.actualRowPotential W β ((t l i : ℝ).toNNReal) u)) =
      fun l => -partitionPotentialSum W β (t l) (N l) u := by
    funext l
    simp only [partitionPotentialSum, SJ3.negativeSusceptibility_nnreal,
      Real.toNNReal_coe, neg_mul, Finset.sum_neg_distrib]
  rw [he] at hh
  simpa only [SJ3.potentialIntegral, SJ3.negativeSusceptibility_nnreal,
    SJ3.negativeSusceptibility_zero, NNReal.coe_zero, Real.toNNReal_coe,
    Real.toNNReal_zero, neg_sub, neg_add_rev, neg_neg, neg_mul, sub_neg_eq_add,
    sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hh.neg

theorem partitionPotentialSum_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (V : ℝ≥0) (t : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ)
    (ht : ∀ l, Monotone (t l)) (ht0 : ∀ l, t l 0 = 0) (htV : ∀ l, t l (N l) = V)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hwidth : ∀ l i, i < N l → (t l (i + 1) : ℝ) - t l i ≤ ε l) :
    (∀ l, Integrable (fun u => (partitionPotentialSum W β (t l) (N l) u -
      SJ3.potentialIntegral W β hβ V u) ^ 2) ((scalarHiddenPriorBool 0).prod W.law)) ∧
    Tendsto (fun l => ∫ u, (partitionPotentialSum W β (t l) (N l) u -
      SJ3.potentialIntegral W β hβ V u) ^ 2 ∂(scalarHiddenPriorBool 0).prod W.law)
      atTop (𝓝 0) := by
  let := W.isProbability
  refine ⟨fun l => ((partitionPotentialSum_memLp W β hβ (t l) (ht l) (N l)).sub
    (SJ3.potentialIntegral_memLp W β hβ V)).integrable_sq, ?_⟩
  have hh := tendsto_integral_of_dominated_convergence (μ := (scalarHiddenPriorBool 0).prod W.law)
    (f := fun _ : Bool × Ω => (0 : ℝ))
    (F := fun l u => (partitionPotentialSum W β (t l) (N l) u -
      SJ3.potentialIntegral W β hβ V u) ^ 2) (bound := fun _ => (144 : ℝ))
    (fun l => by simpa only [Pi.sub_apply] using
      (((measurable_partitionPotentialSum W β (t l) (N l)).sub
        (SJ3.measurable_potentialIntegral W β hβ V)).pow_const 2).aestronglyMeasurable)
    (integrable_const _) (fun l => ae_of_all _ (fun u => ?_)) ?_
  · simpa only [integral_zero] using hh
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have ha := (abs_sub _ _).trans (add_le_add
      (partitionPotentialSum_bound W β hβ (t l) (ht l) (N l) u)
      (SJ3.potentialIntegral_bound W β hβ V u))
    nlinarith [sq_abs (partitionPotentialSum W β (t l) (N l) u -
      SJ3.potentialIntegral W β hβ V u),
      abs_nonneg (partitionPotentialSum W β (t l) (N l) u -
        SJ3.potentialIntegral W β hβ V u)]
  · filter_upwards [partitionPotentialSum_tendsto_ae W β hβ V t N ht ht0 htV ε hε hwidth]
      with u hu
    simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using
      (hu.sub_const (SJ3.potentialIntegral W β hβ V u)).pow 2

def flatGrid (δ : ℝ≥0) (l k : ℕ) : ℝ≥0 :=
  LJ3.growingLagDyadicTime δ l (k / 2 ^ l) (k % 2 ^ l)

theorem flatGrid_mul (δ : ℝ≥0) (l j : ℕ) :
    flatGrid δ l (j * 2 ^ l) = growingQueryTime δ j := by
  simp [flatGrid, LJ3.growingLagDyadicTime_zero]

theorem flatGrid_cell (δ : ℝ≥0) (l j i : ℕ) (hi : i ≤ 2 ^ l) :
    flatGrid δ l (j * 2 ^ l + i) = LJ3.growingLagDyadicTime δ l j i := by
  by_cases he : i = 2 ^ l
  · subst i
    rw [show j * 2 ^ l + 2 ^ l = (j + 1) * 2 ^ l by ring,
      flatGrid_mul, LJ3.growingLagDyadicTime_end]
  · have hil : i < 2 ^ l := lt_of_le_of_ne hi he
    simp [flatGrid, Nat.mul_comm j (2 ^ l), Nat.mul_add_div (by positivity : 0 < 2 ^ l),
      Nat.div_eq_of_lt hil, Nat.mod_eq_of_lt hil]

theorem flatGrid_succ (δ : ℝ≥0) (l k : ℕ) :
    flatGrid δ l (k + 1) =
      LJ3.growingLagDyadicTime δ l (k / 2 ^ l) (k % 2 ^ l + 1) := by
  have hp : 0 < 2 ^ l := by positivity
  have he : k / 2 ^ l * 2 ^ l + (k % 2 ^ l + 1) = k + 1 := by
    have hh := Nat.div_add_mod k (2 ^ l)
    rw [Nat.mul_comm (2 ^ l)] at hh
    omega
  rw [← he]
  exact flatGrid_cell δ l _ _ (Nat.succ_le_of_lt (Nat.mod_lt k hp))

theorem flatGrid_monotone (δ : ℝ≥0) (l : ℕ) : Monotone (flatGrid δ l) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [flatGrid_succ]
  exact LJ3.growingLagDyadicTime_monotone δ l _ (Nat.le_succ _)

theorem flatGrid_zero (δ : ℝ≥0) (l : ℕ) : flatGrid δ l 0 = 0 := by
  simpa only [Nat.zero_mul, growingQueryTime_zero] using flatGrid_mul δ l 0

theorem flatGrid_end (δ : ℝ≥0) (K l : ℕ) :
    flatGrid δ l ((K + 1) * 2 ^ l) = growingQueryTime δ (K + 1) :=
  flatGrid_mul δ l (K + 1)

theorem flatGrid_width (δ : ℝ≥0) (K l i : ℕ)
    (hsmall : ∀ j < K + 1, growingQueryDuration δ j ≤ 1)
    (hi : i < (K + 1) * 2 ^ l) :
    (flatGrid δ l (i + 1) : ℝ) - flatGrid δ l i ≤ brownianDyadicWidth 1 l := by
  have hp : 0 < 2 ^ l := by positivity
  have hj : i / 2 ^ l < K + 1 := (Nat.div_lt_iff_lt_mul hp).mpr hi
  rw [flatGrid_succ]
  change (LJ3.growingLagDyadicTime δ l (i / 2 ^ l) (i % 2 ^ l + 1) : ℝ) -
    LJ3.growingLagDyadicTime δ l (i / 2 ^ l) (i % 2 ^ l) ≤ _
  simp only [LJ3.growingLagDyadicTime, scalarBrownianDyadicTime, NNReal.coe_add,
    NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat,
    Nat.cast_add, Nat.cast_one, brownianDyadicWidth, NNReal.coe_one]
  have hs : (growingQueryDuration δ (i / 2 ^ l) : ℝ) ≤ 1 := by exact_mod_cast hsmall _ hj
  have he : (growingQueryTime δ (i / 2 ^ l) : ℝ) +
      (growingQueryDuration δ (i / 2 ^ l) : ℝ) * ((i % 2 ^ l : ℕ) + 1) / (2 : ℝ) ^ l -
      ((growingQueryTime δ (i / 2 ^ l) : ℝ) +
        (growingQueryDuration δ (i / 2 ^ l) : ℝ) * (i % 2 ^ l : ℕ) / (2 : ℝ) ^ l) =
      (growingQueryDuration δ (i / 2 ^ l) : ℝ) / (2 : ℝ) ^ l := by ring
  rw [he]
  exact div_le_div_of_nonneg_right hs (by positivity)

theorem sum_range_blocks (F : ℕ → ℝ) (J N : ℕ) :
    (∑ k ∈ Finset.range (J * N), F k) =
      ∑ j ∈ Finset.range J, ∑ i ∈ Finset.range N, F (j * N + i) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem partitionPotentialSum_flat_eq (W : BrownianSystem Ω) (β : ℝ)
    (δ : ℝ≥0) (K l : ℕ) (u : Bool × Ω) :
    partitionPotentialSum W β (flatGrid δ l) ((K + 1) * 2 ^ l) u =
      ∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (2 ^ l),
        actualParisiFullSusceptibilityExpected W β (refinedGrid δ l j i) *
          (LJ.actualRowPotential W β (refinedGrid δ l j (i + 1)) u -
            LJ.actualRowPotential W β (refinedGrid δ l j i) u) := by
  rw [partitionPotentialSum, sum_range_blocks]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i hi
  have hil := Finset.mem_range.mp hi
  rw [flatGrid_cell δ l j i hil.le,
    show j * 2 ^ l + i + 1 = j * 2 ^ l + (i + 1) by omega,
    flatGrid_cell δ l j (i + 1) hil]

theorem refinedPotential_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (K : ℕ) (hsmall : ∀ j < K + 1, growingQueryDuration δ j ≤ 1) :
    (∀ l, Integrable (fun u =>
      (partitionPotentialSum W β (flatGrid δ l) ((K + 1) * 2 ^ l) u -
        SJ3.potentialIntegral W β hβ (growingQueryTime δ (K + 1)) u) ^ 2)
      ((scalarHiddenPriorBool 0).prod W.law)) ∧
    Tendsto (fun l => ∫ u,
      (partitionPotentialSum W β (flatGrid δ l) ((K + 1) * 2 ^ l) u -
        SJ3.potentialIntegral W β hβ (growingQueryTime δ (K + 1)) u) ^ 2
        ∂(scalarHiddenPriorBool 0).prod W.law) atTop (𝓝 0) := by
  exact partitionPotentialSum_tendsto_L2 W β hβ _ _ _ (flatGrid_monotone δ)
    (flatGrid_zero δ) (flatGrid_end δ K) (brownianDyadicWidth 1)
    (brownianDyadicWidth_tendsto 1) (fun l i hi => flatGrid_width δ K l i hsmall hi)

def partitionQuerySum (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (N : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  ∑ i ∈ Finset.range N,
    Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β (t i)) *
      (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β (t i) u.1.2) *
      ((actualParisiQueryBrownianSystem W Z β hβ).B (t (i + 1)) (u.1.2, u.2) -
        (actualParisiQueryBrownianSystem W Z β hβ).B (t i) (u.1.2, u.2))

theorem partitionQuerySum_eq_actualNoise (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (N : ℕ) :
    partitionQuerySum W Z β hβ t N = LM4b.actualNoise W Z β hβ t
      (fun i => Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β (t i))) N := by
  funext u
  rw [LM4b.actualNoise, predictableGaussianSum_eq_range_sum]
  rfl

theorem measurable_partitionQuerySum (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (N : ℕ) :
    Measurable (partitionQuerySum W Z β hβ t N) := by
  rw [partitionQuerySum_eq_actualNoise]
  exact LM4b.measurable_actualNoise W Z β hβ t _ N

theorem partitionQuerySum_memLp (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t) (N : ℕ) :
    MemLp (partitionQuerySum W Z β hβ t N) 2 (LM4.actualRowBaseLaw W Z) := by
  exact Query.partitionQuery_memLp W Z β hβ t ht N

def partitionJointSum (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (N : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  β * partitionPotentialSum W β t N u.1 + partitionQuerySum W Z β hβ t N u

theorem partitionJointSum_memLp (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t) (N : ℕ) :
    MemLp (partitionJointSum W Z β hβ t N) 2 (LM4.actualRowBaseLaw W Z) := by
  let := Z.isProbability
  exact (((partitionPotentialSum_memLp W β hβ t ht N).comp_fst Z.law).const_mul β).add
    (partitionQuerySum_memLp W Z β hβ t ht N)

theorem partitionQuerySum_tendsto_L2 (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (t : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ)
    (ht : ∀ l, Monotone (t l)) (ht0 : ∀ l, t l 0 = 0) (htV : ∀ l, t l (N l) = V)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hwidth : ∀ l i, i < N l → (t l (i + 1) : ℝ) - t l i ≤ ε l)
    (Q : (Bool × Ω) × A → ℝ) (hQ : SJ3.IsQueryRowIntegral W Z β hβ V Q) :
    (∀ l, Integrable (fun u => (partitionQuerySum W Z β hβ (t l) (N l) u - Q u) ^ 2)
      (LM4.actualRowBaseLaw W Z)) ∧
    Tendsto (fun l => ∫ u, (partitionQuerySum W Z β hβ (t l) (N l) u - Q u) ^ 2
      ∂LM4.actualRowBaseLaw W Z) atTop (𝓝 0) := by
  let := W.isProbability
  let := Z.isProbability
  have hS (l : ℕ) := partitionQuerySum_memLp W Z β hβ (t l) (ht l) (N l)
  have hD (l : ℕ) : MemLp (SJ3.queryRowLeftSum W Z β hβ V l) 2 (LM4.actualRowBaseLaw W Z) :=
    Query.queryRowLeftSum_memLp W Z β hβ V l
  have hcomp : Tendsto (fun l => ∫ u, (partitionQuerySum W Z β hβ (t l) (N l) u -
      SJ3.queryRowLeftSum W Z β hβ V l u) ^ 2 ∂LM4.actualRowBaseLaw W Z) atTop (𝓝 0) := by
    exact Query.partitionQuery_comparison_tendsto W Z β hβ V t
      (fun l => (brownianDyadicGrid V).time l) N (fun l => 2 ^ l) ht
      (brownianDyadicGrid V).monotone (fun _ => by positivity) ht0
      (brownianDyadicGrid V).zero htV (fun l => by simp [brownianDyadicGrid]) ε
      (brownianDyadicWidth V) hε (brownianDyadicWidth_tendsto V) hwidth
      (fun l i _ => brownianDyadicGrid_width_le V l i)
  refine ⟨fun l => ((hS l).sub hQ.2.1).integrable_sq, ?_⟩
  have hh := SJ3.meanSquare_linearCombination
    (fun l => (hS l).sub (hD l)) hD (memLp_const (0 : ℝ) : MemLp (fun _ => (0 : ℝ)) 2
      (LM4.actualRowBaseLaw W Z)) hQ.2.1
    (by simpa only [Pi.sub_apply, sub_zero] using hcomp) hQ.2.2.2 1 1
  simpa only [Pi.sub_apply, one_mul, sub_add_cancel, zero_add] using hh

theorem partitionJointSum_tendsto_L2 (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (t : ℕ → ℕ → ℝ≥0) (N : ℕ → ℕ)
    (ht : ∀ l, Monotone (t l)) (ht0 : ∀ l, t l 0 = 0) (htV : ∀ l, t l (N l) = V)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hwidth : ∀ l i, i < N l → (t l (i + 1) : ℝ) - t l i ≤ ε l)
    (Zv : (Bool × Ω) × A → ℝ) (hZv : IsJointRowIntegral W Z β hβ V Zv) :
    (∀ l, Integrable (fun u => (partitionJointSum W Z β hβ (t l) (N l) u - Zv u) ^ 2)
      (LM4.actualRowBaseLaw W Z)) ∧
    Tendsto (fun l => ∫ u, (partitionJointSum W Z β hβ (t l) (N l) u - Zv u) ^ 2
      ∂LM4.actualRowBaseLaw W Z) atTop (𝓝 0) := by
  let := W.isProbability
  let := Z.isProbability
  let P := fun u : (Bool × Ω) × A => SJ3.potentialIntegral W β hβ V u.1
  let Q := fun u : (Bool × Ω) × A => Zv u - β * P u
  have hP : MemLp P 2 (LM4.actualRowBaseLaw W Z) :=
    (SJ3.potentialIntegral_memLp W β hβ V).comp_fst Z.law
  have hQ : SJ3.IsQueryRowIntegral W Z β hβ V Q := SJ3.queryRowIntegral_of_joint W Z β hβ V hZv
  have hPs (l : ℕ) : MemLp (fun u : (Bool × Ω) × A =>
      partitionPotentialSum W β (t l) (N l) u.1) 2 (LM4.actualRowBaseLaw W Z) :=
    (partitionPotentialSum_memLp W β hβ (t l) (ht l) (N l)).comp_fst Z.law
  have hQs (l : ℕ) := partitionQuerySum_memLp W Z β hβ (t l) (ht l) (N l)
  have hPlim : Tendsto (fun l => ∫ u : (Bool × Ω) × A,
      (partitionPotentialSum W β (t l) (N l) u.1 - P u) ^ 2 ∂LM4.actualRowBaseLaw W Z)
      atTop (𝓝 0) := by
    have hh := (partitionPotentialSum_tendsto_L2 W β hβ V t N ht ht0 htV ε hε hwidth).2
    have he (l : ℕ) :
        (∫ u : (Bool × Ω) × A, (partitionPotentialSum W β (t l) (N l) u.1 - P u) ^ 2
          ∂LM4.actualRowBaseLaw W Z) =
          ∫ u, (partitionPotentialSum W β (t l) (N l) u - SJ3.potentialIntegral W β hβ V u) ^ 2
            ∂(scalarHiddenPriorBool 0).prod W.law := by
      simpa only [P, LM4.actualRowBaseLaw, probReal_univ, one_smul] using
        integral_fun_fst (μ := (scalarHiddenPriorBool 0).prod W.law) (ν := Z.law)
          (fun u => (partitionPotentialSum W β (t l) (N l) u - SJ3.potentialIntegral W β hβ V u) ^ 2)
    simp_rw [he]
    exact hh
  have hQlim := (partitionQuerySum_tendsto_L2 W Z β hβ V t N ht ht0 htV ε hε hwidth Q hQ).2
  refine ⟨fun l => ((partitionJointSum_memLp W Z β hβ (t l) (ht l) (N l)).sub hZv.2.1).integrable_sq, ?_⟩
  have hh := SJ3.meanSquare_linearCombination hPs hQs hP hQ.2.1 hPlim hQlim β 1
  have he (u : (Bool × Ω) × A) : β * P u + Q u = Zv u := by dsimp [Q]; ring
  simpa only [one_mul, he, partitionJointSum] using hh

theorem partitionQuerySum_flat_eq (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K l : ℕ) (u : (Bool × Ω) × A) :
    partitionQuerySum W Z β hβ (flatGrid δ l) ((K + 1) * 2 ^ l) u =
      ∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (2 ^ l),
        Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β (refinedGrid δ l j i)) *
          (scalarHiddenSign u.1.1 - actualParisiFullPosteriorMean W β (refinedGrid δ l j i) u.1.2) *
          ((actualParisiQueryBrownianSystem W Z β hβ).B (refinedGrid δ l j (i + 1)) (u.1.2, u.2) -
            (actualParisiQueryBrownianSystem W Z β hβ).B (refinedGrid δ l j i) (u.1.2, u.2)) := by
  rw [partitionQuerySum, sum_range_blocks]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i hi
  have hil := Finset.mem_range.mp hi
  rw [flatGrid_cell δ l j i hil.le,
    show j * 2 ^ l + i + 1 = j * 2 ^ l + (i + 1) by omega,
    flatGrid_cell δ l j (i + 1) hil]

theorem refinedResidual_sub_growingResidual (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K l : ℕ)
    (Zv : (Bool × Ω) × A → ℝ) (u : (Bool × Ω) × A) :
    refinedResidual W Z β hβ δ K l u - growingResidual W Z β hβ δ K Zv u =
      partitionJointSum W Z β hβ (flatGrid δ l) ((K + 1) * 2 ^ l) u - Zv u := by
  unfold refinedResidual LJ.actualRefinedResidual growingResidual partitionJointSum
  rw [partitionPotentialSum_flat_eq, partitionQuerySum_flat_eq]
  unfold LJ.refinedContinuumRow
  simp only [LJ.actualRowPotential, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc,
    mesh, refinedGrid]
  ring

theorem refinedResidualLimit_holds : Blueprint5a.RefinedResidualLimitStatement := by
  intro Ω A _ _ W Z β hβ δ K hmesh Zv hZv
  have hsmall : ∀ j < K + 1, growingQueryDuration δ j ≤ 1 := fun j hj => hmesh.2.2.1 j (by omega)
  obtain ⟨hi, hlim⟩ := partitionJointSum_tendsto_L2 W Z β hβ
    (growingQueryTime δ (K + 1)) (flatGrid δ) (fun l => (K + 1) * 2 ^ l)
    (flatGrid_monotone δ) (flatGrid_zero δ) (flatGrid_end δ K)
    (brownianDyadicWidth 1) (brownianDyadicWidth_tendsto 1)
    (fun l i hi => flatGrid_width δ K l i hsmall hi) Zv hZv
  simp_rw [refinedResidual_sub_growingResidual]
  refine ⟨fun l => SJ7.integrable_actualQuerySpinLaw W Z β _ (hi l), ?_⟩
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun l => SJ7.integral_nonneg_actualQuerySpinLaw_le_two W Z β _ (hi l) (fun _ => sq_nonneg _))
  simpa using hlim.const_mul 2

end SKConstants.Completion.S71
