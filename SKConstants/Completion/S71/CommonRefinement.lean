module

public import SKConstants.Completion.S71.QueryIsometry

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.S71.Mesh

def clampCell (t : ℕ → ℝ≥0) (i : ℕ) (x : ℝ≥0) : ℝ≥0 :=
  max (t i) (min (t (i + 1)) x)

theorem clampCell_zero (t : ℕ → ℝ≥0) (i : ℕ) : clampCell t i 0 = t i := by
  simp [clampCell]

theorem clampCell_end (t : ℕ → ℝ≥0) (ht : Monotone t) (i : ℕ)
    (V : ℝ≥0) (hV : t (i + 1) ≤ V) : clampCell t i V = t (i + 1) := by
  simp only [clampCell, min_eq_left hV, max_eq_right (ht (Nat.le_succ i))]

theorem clampCell_le (t : ℕ → ℝ≥0) (ht : Monotone t) (i : ℕ) (x : ℝ≥0) :
    clampCell t i x ≤ t (i + 1) :=
  max_le (ht (Nat.le_succ i)) (min_le_left _ _)

theorem clampCell_mono (t : ℕ → ℝ≥0) (i : ℕ) : Monotone (clampCell t i) := by
  intro x y hxy
  exact max_le_max_left _ (min_le_min_left _ hxy)

theorem clampCell_increment (B : ℝ≥0 → ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (i : ℕ) (x : ℝ≥0) :
    B (clampCell t i x) - B (t i) = B (min (t (i + 1)) x) - B (min (t i) x) := by
  by_cases hx : x ≤ t i
  · have hxn := hx.trans (ht (Nat.le_succ i))
    simp [clampCell, min_eq_right hx, min_eq_right hxn, max_eq_left hx]
  · have hix : t i ≤ x := le_of_not_ge hx
    simp only [clampCell, max_eq_right (le_min (ht (Nat.le_succ i)) hix), min_eq_left hix]

def commonGrid (t s : ℕ → ℝ≥0) (N M : ℕ) (V : ℝ≥0) (k : ℕ) : ℝ≥0 :=
  if k < N * M then clampCell t (k / M) (s (k % M)) else V

theorem commonGrid_mul (t s : ℕ → ℝ≥0) (N M : ℕ) (V : ℝ≥0)
    (hM : 0 < M) (hs0 : s 0 = 0) (htN : t N = V) (i : ℕ) (hi : i ≤ N) :
    commonGrid t s N M V (i * M) = t i := by
  by_cases hiN : i < N
  · rw [commonGrid, ite_eq_left (Nat.mul_lt_mul_of_pos_right hiN hM)]
    simp only [Nat.mul_div_cancel _ hM, Nat.mul_mod_left, hs0, clampCell_zero]
  · have he : i = N := by omega
    subst i
    simp [commonGrid, htN]

theorem commonGrid_cell (t s : ℕ → ℝ≥0) (N M : ℕ) (V : ℝ≥0)
    (ht : Monotone t) (hM : 0 < M) (hs0 : s 0 = 0) (htN : t N = V) (hsM : s M = V)
    (i j : ℕ) (hi : i < N) (hj : j ≤ M) :
    commonGrid t s N M V (i * M + j) = clampCell t i (s j) := by
  by_cases hjM : j = M
  · subst j
    rw [show i * M + M = (i + 1) * M by ring,
      commonGrid_mul t s N M V hM hs0 htN (i + 1) hi, hsM,
      clampCell_end t ht i V ((ht hi).trans_eq htN)]
  · have hjl : j < M := by omega
    have hlt : i * M + j < N * M := by
      have hh := Nat.mul_le_mul_right M hi
      rw [Nat.succ_mul] at hh
      omega
    rw [commonGrid, ite_eq_left hlt]
    simp only [Nat.mul_comm i M, Nat.mul_add_div hM, Nat.div_eq_of_lt hjl,
      Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hjl]

theorem commonGrid_monotone (t s : ℕ → ℝ≥0) (N M : ℕ) (V : ℝ≥0)
    (ht : Monotone t) (hs : Monotone s) (hM : 0 < M)
    (hs0 : s 0 = 0) (htN : t N = V) (hsM : s M = V) :
    Monotone (commonGrid t s N M V) := by
  apply monotone_nat_of_le_succ
  intro k
  by_cases hk : k < N * M
  · have hi : k / M < N := (Nat.div_lt_iff_lt_mul hM).mpr hk
    have hj : k % M < M := Nat.mod_lt k hM
    have he : k / M * M + k % M = k := by
      simpa only [Nat.mul_comm M] using Nat.div_add_mod k M
    have he' : k / M * M + (k % M + 1) = k + 1 := by omega
    have hc0 : commonGrid t s N M V k = clampCell t (k / M) (s (k % M)) := by
      simpa only [he] using commonGrid_cell t s N M V ht hM hs0 htN hsM
        (k / M) (k % M) hi hj.le
    have hc1 : commonGrid t s N M V (k + 1) = clampCell t (k / M) (s (k % M + 1)) := by
      simpa only [he'] using commonGrid_cell t s N M V ht hM hs0 htN hsM
        (k / M) (k % M + 1) hi hj
    rw [hc0, hc1]
    exact clampCell_mono t _ (hs (Nat.le_succ _))
  · simp only [commonGrid, ite_eq_right hk, ite_eq_right (show ¬k + 1 < N * M by omega), le_refl]

theorem commonGrid_zero (t s : ℕ → ℝ≥0) (N M : ℕ) (V : ℝ≥0)
    (hM : 0 < M) (hs0 : s 0 = 0) (ht0 : t 0 = 0) (htN : t N = V) :
    commonGrid t s N M V 0 = 0 := by
  simpa only [Nat.zero_mul, ht0] using commonGrid_mul t s N M V hM hs0 htN 0 (Nat.zero_le N)

theorem commonGrid_end (t s : ℕ → ℝ≥0) (N M : ℕ) (V : ℝ≥0) :
    commonGrid t s N M V (N * M) = V := by simp [commonGrid]

def commonLeft (t : ℕ → ℝ≥0) (N M : ℕ) (V : ℝ≥0) (k : ℕ) : ℝ≥0 :=
  if k < N * M then t (k / M) else V

def commonOther (t s : ℕ → ℝ≥0) (N M : ℕ) (V : ℝ≥0) (k : ℕ) : ℝ≥0 :=
  if k < N * M then min (s (k % M)) (t (k / M + 1)) else V

theorem commonLeft_le (t s : ℕ → ℝ≥0) (N M : ℕ) (V : ℝ≥0) (k : ℕ) :
    commonLeft t N M V k ≤ commonGrid t s N M V k := by
  unfold commonLeft commonGrid
  split_ifs <;> simp only [clampCell, le_max_left, le_refl]

theorem commonOther_le (t s : ℕ → ℝ≥0) (N M : ℕ) (V : ℝ≥0) (k : ℕ) :
    commonOther t s N M V k ≤ commonGrid t s N M V k := by
  unfold commonOther commonGrid
  split_ifs
  · simpa only [clampCell, min_comm] using le_max_right (t (k / M)) (min (t (k / M + 1)) (s (k % M)))
  · exact le_rfl

theorem sum_range_blocks (F : ℕ → ℝ) (J N : ℕ) :
    (∑ k ∈ Finset.range (J * N), F k) =
      ∑ j ∈ Finset.range J, ∑ i ∈ Finset.range N, F (j * N + i) := by
  induction J with
  | zero => simp
  | succ J ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

def partitionSum (H B : ℝ≥0 → ℝ) (t : ℕ → ℝ≥0) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, H (t i) * (B (t (i + 1)) - B (t i))

theorem sum_clampCell_increment (B : ℝ≥0 → ℝ) (t : ℕ → ℝ≥0)
    (ht : Monotone t) (N : ℕ) (ht0 : t 0 = 0) (x : ℝ≥0) (hx : x ≤ t N) :
    (∑ i ∈ Finset.range N, (B (clampCell t i x) - B (t i))) = B x - B 0 := by
  simp_rw [clampCell_increment B t ht]
  rw [Finset.sum_range_sub (fun i => B (min (t i) x)) N]
  simp only [min_eq_right hx, ht0, zero_le, min_eq_left]

theorem partitionSum_difference (H B : ℝ≥0 → ℝ) (t s : ℕ → ℝ≥0)
    (N M : ℕ) (V : ℝ≥0) (ht : Monotone t) (hs : Monotone s) (hM : 0 < M)
    (ht0 : t 0 = 0) (hs0 : s 0 = 0) (htN : t N = V) (hsM : s M = V) :
    partitionSum H B t N - partitionSum H B s M =
      ∑ k ∈ Finset.range (N * M),
        (H (commonLeft t N M V k) - H (commonOther t s N M V k)) *
          (B (commonGrid t s N M V (k + 1)) - B (commonGrid t s N M V k)) := by
  let D := fun i j => B (clampCell t i (s (j + 1))) - B (clampCell t i (s j))
  have hfirst (i : ℕ) (hi : i < N) :
      (∑ j ∈ Finset.range M, H (t i) * D i j) =
        H (t i) * (B (t (i + 1)) - B (t i)) := by
    rw [← Finset.mul_sum, Finset.sum_range_sub (fun j => B (clampCell t i (s j))) M,
      hs0, hsM, clampCell_zero, clampCell_end t ht i V ((ht hi).trans_eq htN)]
  have hsecond (j : ℕ) (hj : j < M) :
      (∑ i ∈ Finset.range N, H (min (s j) (t (i + 1))) * D i j) =
        H (s j) * (B (s (j + 1)) - B (s j)) := by
    have he (i : ℕ) (hi : i ∈ Finset.range N) :
        H (min (s j) (t (i + 1))) * D i j = H (s j) * D i j := by
      by_cases hh : s j ≤ t (i + 1)
      · rw [min_eq_left hh]
      · have hh' : t (i + 1) ≤ s j := le_of_not_ge hh
        have hh'' := hh'.trans (hs (Nat.le_succ j))
        simp only [D, clampCell_end t ht i (s j) hh',
          clampCell_end t ht i (s (j + 1)) hh'', sub_self, mul_zero]
    rw [Finset.sum_congr rfl he, ← Finset.mul_sum]
    congr 1
    have hp := sum_clampCell_increment B t ht N ht0 (s (j + 1))
      ((hs hj).trans_eq (hsM.trans htN.symm))
    have hq := sum_clampCell_increment B t ht N ht0 (s j)
      ((hs hj.le).trans_eq (hsM.trans htN.symm))
    have hsplit : (∑ i ∈ Finset.range N, D i j) =
        (∑ i ∈ Finset.range N, (B (clampCell t i (s (j + 1))) - B (t i))) -
          ∑ i ∈ Finset.range N, (B (clampCell t i (s j)) - B (t i)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [D]
      ring
    rw [hsplit, hp, hq]
    ring
  have hdouble : partitionSum H B t N - partitionSum H B s M =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
        (H (t i) - H (min (s j) (t (i + 1)))) * D i j := by
    simp_rw [sub_mul, Finset.sum_sub_distrib]
    rw [Finset.sum_congr rfl (fun i hi => hfirst i (Finset.mem_range.mp hi)),
      Finset.sum_comm (s := Finset.range N),
      Finset.sum_congr rfl (fun j hj => hsecond j (Finset.mem_range.mp hj))]
    rfl
  rw [hdouble, sum_range_blocks]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hil := Finset.mem_range.mp hi
  have hjl := Finset.mem_range.mp hj
  have hk : i * M + j < N * M := by
    have hh := Nat.mul_le_mul_right M hil
    rw [Nat.succ_mul] at hh
    omega
  have hquot : (i * M + j) / M = i := by
    rw [Nat.mul_comm i M, Nat.mul_add_div hM, Nat.div_eq_of_lt hjl, Nat.add_zero]
  have hmod : (i * M + j) % M = j := by simp [Nat.add_mod, Nat.mod_eq_of_lt hjl]
  simp only [commonLeft, commonOther, ite_eq_left hk, hquot, hmod]
  rw [commonGrid_cell t s N M V ht hM hs0 htN hsM i j hil hjl.le,
    show i * M + j + 1 = i * M + (j + 1) by omega,
    commonGrid_cell t s N M V ht hM hs0 htN hsM i (j + 1) hil hjl]

theorem commonGrid_succ_cell (t s : ℕ → ℝ≥0) (N M : ℕ) (V : ℝ≥0)
    (ht : Monotone t) (hM : 0 < M) (hs0 : s 0 = 0) (htN : t N = V) (hsM : s M = V)
    (k : ℕ) (hk : k < N * M) :
    commonGrid t s N M V (k + 1) = clampCell t (k / M) (s (k % M + 1)) := by
  have hi : k / M < N := (Nat.div_lt_iff_lt_mul hM).mpr hk
  have hj : k % M < M := Nat.mod_lt k hM
  have he : k / M * M + (k % M + 1) = k + 1 := by
    have hh := Nat.div_add_mod k M
    rw [Nat.mul_comm M] at hh
    omega
  simpa only [he] using commonGrid_cell t s N M V ht hM hs0 htN hsM
    (k / M) (k % M + 1) hi hj

theorem commonTimes_le_horizon (t s : ℕ → ℝ≥0) (N M : ℕ) (V : ℝ≥0)
    (ht : Monotone t) (hM : 0 < M) (htN : t N = V) (k : ℕ) (hk : k < N * M) :
    commonLeft t N M V k ≤ V ∧ commonOther t s N M V k ≤ V := by
  have hi : k / M < N := (Nat.div_lt_iff_lt_mul hM).mpr hk
  simp only [commonLeft, commonOther, ite_eq_left hk]
  exact ⟨(ht hi.le).trans_eq htN, (min_le_right _ _).trans ((ht hi).trans_eq htN)⟩

theorem commonActive_close (t s : ℕ → ℝ≥0) (N M : ℕ) (V : ℝ≥0)
    (ht : Monotone t) (hs : Monotone s) (hM : 0 < M)
    (hs0 : s 0 = 0) (htN : t N = V) (hsM : s M = V)
    (η : ℝ) (htw : ∀ i < N, (t (i + 1) : ℝ) - t i < η)
    (hsw : ∀ j < M, (s (j + 1) : ℝ) - s j < η)
    (k : ℕ) (hk : k < N * M)
    (hactive : commonGrid t s N M V k < commonGrid t s N M V (k + 1)) :
    |(commonLeft t N M V k : ℝ) - commonOther t s N M V k| < η := by
  have hi : k / M < N := (Nat.div_lt_iff_lt_mul hM).mpr hk
  have hj : k % M < M := Nat.mod_lt k hM
  rw [commonGrid_succ_cell t s N M V ht hM hs0 htN hsM k hk] at hactive
  simp only [commonGrid, ite_eq_left hk] at hactive
  have hbefore : s (k % M) < t (k / M + 1) := by
    by_contra hn
    have ha : t (k / M + 1) ≤ s (k % M) := le_of_not_gt hn
    have hb := ha.trans (hs (Nat.le_succ _))
    rw [clampCell_end t ht _ _ ha, clampCell_end t ht _ _ hb] at hactive
    exact (lt_irrefl _ hactive)
  have hafter : t (k / M) < s (k % M + 1) := by
    by_contra hn
    have ha : s (k % M + 1) ≤ t (k / M) := le_of_not_gt hn
    have hb := (hs (Nat.le_succ _)).trans ha
    have hca : clampCell t (k / M) (s (k % M + 1)) = t (k / M) := by
      exact max_eq_left ((min_le_right _ _).trans ha)
    have hcb : clampCell t (k / M) (s (k % M)) = t (k / M) := by
      exact max_eq_left ((min_le_right _ _).trans hb)
    rw [hca, hcb] at hactive
    exact (lt_irrefl _ hactive)
  simp only [commonLeft, commonOther, ite_eq_left hk, min_eq_left hbefore.le]
  have ha : (s (k % M) : ℝ) ≤ t (k / M + 1) := NNReal.coe_le_coe.mpr hbefore.le
  have hb : (t (k / M) : ℝ) ≤ s (k % M + 1) := NNReal.coe_le_coe.mpr hafter.le
  exact abs_lt.mpr ⟨by linarith [htw _ hi], by linarith [hsw _ hj]⟩

end SKConstants.Completion.S71.Mesh

namespace SKConstants.Completion.S71.Query
open SKConstantsOAI.ZeroTemperatureSK Mesh
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
local instance comparison_W_probability (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability
local instance comparison_Z_probability (Z : BrownianSystem A) : IsProbabilityMeasure Z.law := Z.isProbability

def partitionQuery (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (N : ℕ) (u : (Bool × Ω) × A) : ℝ :=
  partitionSum (fun v => queryCoefficient W β v u)
    (fun v => (actualParisiQueryBrownianSystem W Z β hβ).B v (u.1.2, u.2)) t N

theorem partitionQuery_memLp (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : Monotone t) (N : ℕ) :
    MemLp (partitionQuery W Z β hβ t N) 2 (LM4.actualRowBaseLaw W Z) := by
  unfold partitionQuery partitionSum
  apply memLp_finsetSum
  intro j _
  have hd : MemLp (LM4b.actualNoiseIncrement W Z β hβ t j) 2 (LM4.actualRowBaseLaw W Z) :=
    (LM4b.actualNoiseIncrement_hasLaw W Z β hβ t ht j).memLp (memLp_id_gaussianReal 2)
  apply hd.of_le_mul (c := 2)
    ((measurable_queryCoefficient W β _).aestronglyMeasurable.mul hd.aestronglyMeasurable)
  apply ae_of_all
  intro u
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right (queryCoefficient_bound W β _ u) (norm_nonneg _)

theorem partitionQuery_difference_isometry (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t s : ℕ → ℝ≥0) (N M : ℕ) (V : ℝ≥0)
    (ht : Monotone t) (hs : Monotone s) (hM : 0 < M)
    (ht0 : t 0 = 0) (hs0 : s 0 = 0) (htN : t N = V) (hsM : s M = V) :
    (∫ u, (partitionQuery W Z β hβ t N u - partitionQuery W Z β hβ s M u) ^ 2
      ∂LM4.actualRowBaseLaw W Z) =
      ∑ k : Fin (N * M), (brownianMeshVariance (commonGrid t s N M V) k : ℝ) *
        ∫ u, (queryCoefficient W β (commonLeft t N M V k) u -
          queryCoefficient W β (commonOther t s N M V k) u) ^ 2 ∂LM4.actualRowBaseLaw W Z := by
  have he (u : (Bool × Ω) × A) :
      partitionQuery W Z β hβ t N u - partitionQuery W Z β hβ s M u =
        predictableGaussianSum (LM4b.actualNoiseIncrement W Z β hβ (commonGrid t s N M V))
          (fun k u => queryCoefficient W β (commonLeft t N M V k) u -
            queryCoefficient W β (commonOther t s N M V k) u) (N * M) u := by
    rw [predictableGaussianSum_eq_range_sum]
    exact partitionSum_difference _ _ t s N M V ht hs hM ht0 hs0 htN hsM
  simp_rw [he]
  exact queryDifference_isometry W Z β hβ _ _ _
    (commonGrid_monotone t s N M V ht hs hM hs0 htN hsM)
    (commonLeft_le t s N M V) (commonOther_le t s N M V) (N * M)

theorem partitionQuery_comparison_tendsto (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (V : ℝ≥0) (t s : ℕ → ℕ → ℝ≥0) (N M : ℕ → ℕ)
    (ht : ∀ l, Monotone (t l)) (hs : ∀ l, Monotone (s l)) (hM : ∀ l, 0 < M l)
    (ht0 : ∀ l, t l 0 = 0) (hs0 : ∀ l, s l 0 = 0)
    (htN : ∀ l, t l (N l) = V) (hsM : ∀ l, s l (M l) = V)
    (εt εs : ℕ → ℝ) (hεt : Tendsto εt atTop (𝓝 0)) (hεs : Tendsto εs atTop (𝓝 0))
    (htw : ∀ l i, i < N l → (t l (i + 1) : ℝ) - t l i ≤ εt l)
    (hsw : ∀ l j, j < M l → (s l (j + 1) : ℝ) - s l j ≤ εs l) :
    Tendsto (fun l => ∫ u, (partitionQuery W Z β hβ (t l) (N l) u -
      partitionQuery W Z β hβ (s l) (M l) u) ^ 2 ∂LM4.actualRowBaseLaw W Z) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hV : 0 < (V : ℝ) + 1 := by positivity
  obtain ⟨η, hη, hsmall⟩ := expected_sq_difference_uniform_small_of_bounded
    (LM4.actualRowBaseLaw W Z) (queryCoefficient W β)
    (fun v => (measurable_queryCoefficient W β v).aestronglyMeasurable)
    (queryCoefficient_continuous_ae W Z β) 2 (queryCoefficient_bound W β) V
    (ε / ((V : ℝ) + 1)) (div_pos hε hV)
  obtain ⟨L, hL⟩ := eventually_atTop.mp
    ((hεt.eventually (eventually_lt_nhds hη)).and (hεs.eventually (eventually_lt_nhds hη)))
  refine ⟨L, fun l hl => ?_⟩
  let c := commonGrid (t l) (s l) (N l) (M l) V
  have hcm : Monotone c := commonGrid_monotone _ _ _ _ _ (ht l) (hs l) (hM l)
    (hs0 l) (htN l) (hsM l)
  have henergy (k : Fin (N l * M l)) :
      (brownianMeshVariance c k : ℝ) *
        (∫ u, (queryCoefficient W β (commonLeft (t l) (N l) (M l) V k) u -
          queryCoefficient W β (commonOther (t l) (s l) (N l) (M l) V k) u) ^ 2
          ∂LM4.actualRowBaseLaw W Z) ≤
        (brownianMeshVariance c k : ℝ) * (ε / ((V : ℝ) + 1)) := by
    by_cases hz : (brownianMeshVariance c k : ℝ) = 0
    · simp only [hz, zero_mul, le_refl]
    · apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
      have hactive : c k < c (k + 1) := by
        by_contra hn
        have he : c (k + 1) = c k := le_antisymm (le_of_not_gt hn) (hcm (Nat.le_succ _))
        exact hz (by simp only [brownianMeshVariance, he, tsub_self, NNReal.coe_zero])
      obtain ⟨ha, hb⟩ := commonTimes_le_horizon (t l) (s l) (N l) (M l) V (ht l)
        (hM l) (htN l) k k.isLt
      exact (hsmall _ ha _ hb (commonActive_close (t l) (s l) (N l) (M l) V
        (ht l) (hs l) (hM l) (hs0 l) (htN l) (hsM l) η
        (fun i hi => (htw l i hi).trans_lt (hL l hl).1)
        (fun j hj => (hsw l j hj).trans_lt (hL l hl).2) k k.isLt hactive)).le
  have hsum : (∑ k : Fin (N l * M l), (brownianMeshVariance c k : ℝ)) = V := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (brownianMeshVariance c k : ℝ))]
    simp_rw [brownianMeshVariance, NNReal.coe_sub (hcm (Nat.le_succ _))]
    rw [Finset.sum_range_sub (fun k => (c k : ℝ))]
    change (commonGrid _ _ _ _ _ _ : ℝ) - commonGrid _ _ _ _ _ _ = _
    rw [commonGrid_end, commonGrid_zero _ _ _ _ _ (hM l) (hs0 l) (ht0 l) (htN l)]
    simp only [NNReal.coe_zero, sub_zero]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
  rw [partitionQuery_difference_isometry W Z β hβ (t l) (s l) (N l) (M l) V
    (ht l) (hs l) (hM l) (ht0 l) (hs0 l) (htN l) (hsM l)]
  calc
    _ ≤ ∑ k : Fin (N l * M l), (brownianMeshVariance c k : ℝ) *
        (ε / ((V : ℝ) + 1)) := Finset.sum_le_sum (fun k _ => henergy k)
    _ = (V : ℝ) * (ε / ((V : ℝ) + 1)) := by rw [← Finset.sum_mul, hsum]
    _ < ε := by rw [← mul_div_assoc]; exact (div_lt_iff₀ hV).mpr (by nlinarith)

end SKConstants.Completion.S71.Query
