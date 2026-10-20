module

public import SKConstants.ScalarOrthogonalWeightedBrownian
public import SKConstants.ScalarStieltjesRiemann

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.S33aA

def bvTransform (f : StieltjesFunction ℝ) (X : ℝ → ℝ) (t : ℝ) : ℝ :=
  f t * X t - ∫ s in (0 : ℝ)..t, X s ∂f.measure

def bvIncrementError (f : StieltjesFunction ℝ) (X : ℝ → ℝ) (a b : ℝ) : ℝ :=
  bvTransform f X b - bvTransform f X a - f a * (X b - X a)

theorem bvIncrementError_eq (f : StieltjesFunction ℝ) (X : ℝ → ℝ)
    (hX : Continuous X) (a b : ℝ) :
    bvIncrementError f X a b = X b * (f b - f a) - ∫ s in a..b, X s ∂f.measure := by
  have hi (c d : ℝ) : IntervalIntegrable X f.measure c d :=
    (hX.continuousOn.integrableOn_compact isCompact_uIcc).intervalIntegrable
  have he := intervalIntegral.integral_add_adjacent_intervals (hi 0 a) (hi a b)
  unfold bvIncrementError bvTransform
  rw [← he]
  ring

theorem bvIncrementError_abs_le (f : StieltjesFunction ℝ) (X : ℝ → ℝ)
    (hX : Continuous X) {a b ε : ℝ} (hab : a ≤ b)
    (hε : ∀ s ∈ Icc a b, |X b - X s| ≤ ε) :
    |bvIncrementError f X a b| ≤ ε * (f b - f a) := by
  rw [bvIncrementError_eq f X hX]
  exact scalarStieltjes_interval_error_bound f X hX hab hε

def rotatedQuery (f g : StieltjesFunction ℝ) (X N : ℝ → ℝ) (t : ℝ) : ℝ :=
  -bvTransform f X t + bvTransform g N t

def rotatedAux (f g : StieltjesFunction ℝ) (X N : ℝ → ℝ) (t : ℝ) : ℝ :=
  bvTransform g X t + bvTransform f N t

theorem rotation_increment_error_eq (f g : StieltjesFunction ℝ) (X N : ℝ → ℝ)
    (a b : ℝ) (hunit : (f a) ^ 2 + (g a) ^ 2 = 1) :
    -f a * (rotatedQuery f g X N b - rotatedQuery f g X N a) +
      g a * (rotatedAux f g X N b - rotatedAux f g X N a) - (X b - X a) =
    -f a * (-bvIncrementError f X a b + bvIncrementError g N a b) +
      g a * (bvIncrementError g X a b + bvIncrementError f N a b) := by
  have he : ((f a) ^ 2 + (g a) ^ 2 - 1) * (X b - X a) = 0 := by rw [hunit]; ring
  dsimp only [rotatedQuery, rotatedAux, bvIncrementError] at *
  linear_combination he

theorem rotation_increment_error_abs_le (f g : StieltjesFunction ℝ) (X N : ℝ → ℝ)
    (hX : Continuous X) (hN : Continuous N) {a b ε : ℝ} (hab : a ≤ b) (_hε0 : 0 ≤ ε)
    (hunit : (f a) ^ 2 + (g a) ^ 2 = 1) (hf : |f a| ≤ 1) (hg : |g a| ≤ 1)
    (hεX : ∀ s ∈ Icc a b, |X b - X s| ≤ ε)
    (hεN : ∀ s ∈ Icc a b, |N b - N s| ≤ ε) :
    |-f a * (rotatedQuery f g X N b - rotatedQuery f g X N a) +
      g a * (rotatedAux f g X N b - rotatedAux f g X N a) - (X b - X a)| ≤
        2 * ε * (f b - f a + (g b - g a)) := by
  rw [rotation_increment_error_eq f g X N a b hunit]
  have hEfX := bvIncrementError_abs_le f X hX hab hεX
  have hEgN := bvIncrementError_abs_le g N hN hab hεN
  have hEgX := bvIncrementError_abs_le g X hX hab hεX
  have hEfN := bvIncrementError_abs_le f N hN hab hεN
  have hvf : 0 ≤ f b - f a := sub_nonneg.mpr (f.mono hab)
  have hvg : 0 ≤ g b - g a := sub_nonneg.mpr (g.mono hab)
  calc
    _ ≤ |f a| * (|bvIncrementError f X a b| + |bvIncrementError g N a b|) +
        |g a| * (|bvIncrementError g X a b| + |bvIncrementError f N a b|) := by
      calc
        _ ≤ |-f a * (-bvIncrementError f X a b + bvIncrementError g N a b)| +
            |g a * (bvIncrementError g X a b + bvIncrementError f N a b)| := abs_add_le _ _
        _ ≤ _ := by
          simp only [abs_mul, abs_neg]
          gcongr
          · simpa only [abs_neg] using abs_add_le (-bvIncrementError f X a b) (bvIncrementError g N a b)
          · exact abs_add_le _ _
    _ ≤ 1 * (ε * (f b - f a) + ε * (g b - g a)) +
        1 * (ε * (g b - g a) + ε * (f b - f a)) := by
      exact add_le_add
        (mul_le_mul hf (add_le_add hEfX hEgN) (by positivity) zero_le_one)
        (mul_le_mul hg (add_le_add hEgX hEfN) (by positivity) zero_le_one)
    _ = _ := by ring

def rotationLeftSumError (f g : StieltjesFunction ℝ) (X N : ℝ → ℝ)
    (c : ℕ → ℝ) (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, c k *
    (-f (a k) * (rotatedQuery f g X N (a (k + 1)) - rotatedQuery f g X N (a k)) +
      g (a k) * (rotatedAux f g X N (a (k + 1)) - rotatedAux f g X N (a k)) -
      (X (a (k + 1)) - X (a k)))

theorem rotationLeftSumError_abs_le (f g : StieltjesFunction ℝ) (X N : ℝ → ℝ)
    (hX : Continuous X) (hN : Continuous N) (c : ℕ → ℝ) (a : ℕ → ℝ) (m : ℕ)
    (C ε : ℝ) (hC : 0 ≤ C) (hε0 : 0 ≤ ε)
    (ha : ∀ k < m, a k ≤ a (k + 1))
    (hc : ∀ k < m, |c k| ≤ C)
    (hunit : ∀ k < m, (f (a k)) ^ 2 + (g (a k)) ^ 2 = 1)
    (hf : ∀ k < m, |f (a k)| ≤ 1) (hg : ∀ k < m, |g (a k)| ≤ 1)
    (hεX : ∀ k < m, ∀ s ∈ Icc (a k) (a (k + 1)), |X (a (k + 1)) - X s| ≤ ε)
    (hεN : ∀ k < m, ∀ s ∈ Icc (a k) (a (k + 1)), |N (a (k + 1)) - N s| ≤ ε) :
    |rotationLeftSumError f g X N c a m| ≤
      2 * C * ε * (f (a m) - f (a 0) + (g (a m) - g (a 0))) := by
  unfold rotationLeftSumError
  calc
    _ ≤ ∑ k ∈ Finset.range m, |c k| *
        |-f (a k) * (rotatedQuery f g X N (a (k + 1)) - rotatedQuery f g X N (a k)) +
          g (a k) * (rotatedAux f g X N (a (k + 1)) - rotatedAux f g X N (a k)) -
          (X (a (k + 1)) - X (a k))| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun k => c k *
          (-f (a k) * (rotatedQuery f g X N (a (k + 1)) - rotatedQuery f g X N (a k)) +
            g (a k) * (rotatedAux f g X N (a (k + 1)) - rotatedAux f g X N (a k)) -
            (X (a (k + 1)) - X (a k)))) (Finset.range m)
    _ ≤ ∑ k ∈ Finset.range m, C * (2 * ε *
        (f (a (k + 1)) - f (a k) + (g (a (k + 1)) - g (a k)))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_range.mp hk
      exact mul_le_mul (hc k hk')
        (rotation_increment_error_abs_le f g X N hX hN (ha k hk') hε0
          (hunit k hk') (hf k hk') (hg k hk') (hεX k hk') (hεN k hk'))
        (abs_nonneg _) hC
    _ = 2 * C * ε * ∑ k ∈ Finset.range m,
        ((f (a (k + 1)) + g (a (k + 1))) - (f (a k) + g (a k))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      rw [Finset.sum_range_sub (fun k => f (a k) + g (a k)) m]
      ring

theorem rotationLeftSumError_tendsto (f g : StieltjesFunction ℝ) (X N : ℝ → ℝ)
    (hX : Continuous X) (hN : Continuous N) (S T : ℝ) (hST : S ≤ T)
    (a : ℕ → ℕ → ℝ) (m : ℕ → ℕ) (δ : ℕ → ℝ) (c : ℕ → ℕ → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (ha0 : ∀ l, a l 0 = S) (haT : ∀ l, a l (m l) = T)
    (ha : ∀ l k, k ≤ m l → a l k ∈ Icc S T)
    (hmono : ∀ l k, k < m l → a l k ≤ a l (k + 1))
    (hmesh : ∀ l k, k < m l → a l (k + 1) - a l k ≤ δ l)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hc : ∀ l k, k < m l → |c l k| ≤ C)
    (hunit : ∀ t ∈ Icc S T, (f t) ^ 2 + (g t) ^ 2 = 1)
    (hf : ∀ t ∈ Icc S T, |f t| ≤ 1) (hg : ∀ t ∈ Icc S T, |g t| ≤ 1) :
    Tendsto (fun l => rotationLeftSumError f g X N (c l) (a l) (m l)) atTop (𝓝 0) := by
  let V := f T - f S + (g T - g S)
  have hV : 0 ≤ V := add_nonneg (sub_nonneg.mpr (f.mono hST)) (sub_nonneg.mpr (g.mono hST))
  let K := 2 * C * V
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  let η := ε / (K + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨dX, hdX, hUX⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hX.continuousOn) η hη
  obtain ⟨dN, hdN, hUN⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hN.continuousOn) η hη
  obtain ⟨L, hL⟩ := eventually_atTop.mp (hδ.eventually (eventually_lt_nhds (lt_min hdX hdN)))
  refine ⟨L, fun l hl => ?_⟩
  have hsmall (k : ℕ) (hk : k < m l) (s : ℝ) (hs : s ∈ Icc (a l k) (a l (k + 1))) :
      |X (a l (k + 1)) - X s| ≤ η ∧ |N (a l (k + 1)) - N s| ≤ η := by
    have hb := ha l (k + 1) hk
    have hsST : s ∈ Icc S T := ⟨(ha l k hk.le).1.trans hs.1, hs.2.trans hb.2⟩
    have hdist : dist (a l (k + 1)) s < min dX dN := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.2)]
      exact (sub_le_sub_left hs.1 _).trans_lt ((hmesh l k hk).trans_lt (hL l hl))
    constructor
    · exact (show |X (a l (k + 1)) - X s| < η by
        simpa only [Real.dist_eq] using hUX _ hb _ hsST (hdist.trans_le (min_le_left _ _))).le
    · exact (show |N (a l (k + 1)) - N s| < η by
        simpa only [Real.dist_eq] using hUN _ hb _ hsST (hdist.trans_le (min_le_right _ _))).le
  have hb := rotationLeftSumError_abs_le f g X N hX hN (c l) (a l) (m l) C η hC hη.le
    (hmono l) (hc l)
    (fun k hk => hunit _ (ha l k hk.le)) (fun k hk => hf _ (ha l k hk.le))
    (fun k hk => hg _ (ha l k hk.le))
    (fun k hk s hs => (hsmall k hk s hs).1) (fun k hk s hs => (hsmall k hk s hs).2)
  rw [ha0 l, haT l] at hb
  have hηK : η * K < ε := by
    dsimp only [η]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by linarith : 0 < K + 1)).mpr
    nlinarith
  rw [Real.dist_eq, sub_zero]
  exact hb.trans_lt (by convert hηK using 1; dsimp only [K, V]; ring)

end SKConstants.Completion.S33aA
