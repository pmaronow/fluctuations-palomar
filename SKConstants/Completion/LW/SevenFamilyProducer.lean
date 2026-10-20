module

public import SKConstants.Completion.LW.ActualCrossSpinMGF

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal InnerProductSpace

namespace SKConstants.Completion.LW
open SKConstantsOAI.ZeroTemperatureSK Concentration
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

theorem localMGF_into_weighted_budget {μ : Measure Ω} {X : Ω → ℝ}
    {B R : ℝ} (hB : 1 ≤ B) (hR : 1 ≤ R) (r : ℕ)
    (H : LocalQuadraticMGF X μ (productMGFVariance R) (productMGFRadius R)) :
    LocalQuadraticMGF X μ (weightedProducerVariance B R r) (weightedProducerRadius B R r) := by
  have hD : 1 ≤ B*(r+1 : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) r]
  apply localMGF_mono H
  · unfold weightedProducerVariance
    exact le_mul_of_one_le_left (productMGFParameters_pos hR).1.le (by nlinarith)
  · unfold weightedProducerRadius
    exact div_le_self (productMGFParameters_pos hR).2.le hD

theorem actualSevenRowMGF_of_weight_bound
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) (r : ℕ) (hV : t (2^r+1) ≤ V)
    {B R : ℝ} (hB : 1 ≤ B) (hR : 1 ≤ R)
    (hProxy : (actualParisiPosteriorRowMGFProxy W β V : ℝ) ≤ R)
    (hWeight : ∀ j : Fin (2^r),
      |queryWeight W β t (2^r) j / posteriorWeight W β t (2^r) j| ≤ B) :
    ActualSevenRowMGFStatement W Z β hβ t V r
      (weightedProducerVariance B R r) (weightedProducerRadius B R r) := by
  have hB0 : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hV0 : t (2^r) ≤ V := (ht.monotone (Nat.le_succ _)).trans hV
  intro i a ha
  cases i with
  | inl j =>
    fin_cases j
    · have H := localMGF_into_weighted_budget hB hR r
        (actual_spin_row_localMGF W Z β hβ t ht (2^r) V hV a ha hR hProxy false)
      simpa [sevenRow, sevenDuration, normalizedRow] using H
    · have H := localMGF_into_weighted_budget hB hR r
        (actual_spin_row_localMGF W Z β hβ t ht (2^r) V hV a ha hR hProxy true)
      simpa [sevenRow, sevenDuration, normalizedRow] using H
  | inr p =>
    rcases p with ⟨j,I⟩
    have hd : 0 < ∑ j ∈ dyadicIntervalSets r I, previousDuration t j :=
      Finset.sum_pos (fun j _ => sub_pos.mpr
        (NNReal.coe_lt_coe.mpr (ht (Nat.lt_succ_self _)))) (dyadicIntervalSets_nonempty r I)
    have hs j : |posteriorWeight W β t (2^r) j / posteriorWeight W β t (2^r) j| ≤ B := by
      have hj : posteriorWeight W β t (2^r) j ≠ 0 :=
        (NNReal.coe_pos.mpr (actualParisiPosteriorIntervalScale_pos W β hβ
          (t j) (t (j+1)) (ht (Nat.lt_succ_self _)))).ne'
      simpa only [div_self hj, abs_one] using hB
    have hHalf (w : EuclideanSpace ℝ (Fin (2^r)))
        (hw : ∀ j, |w j / posteriorWeight W β t (2^r) j| ≤ B) (tr : Bool) :=
      actual_halfUpper_duration_localMGF W Z β hβ t ht V r hV0 a w ha
        (dyadicIntervalSets r I) hB0 hR hProxy hw hd tr
    have hCross (tr : Bool) := localMGF_into_weighted_budget hB hR r
      (actual_cross_row_duration_localMGF W Z β hβ t ht V r hV0 a ha I hR hProxy tr)
    fin_cases j
    · have H := hHalf (posteriorWeight W β t (2^r)) hs false
      convert H using 1
      funext u
      simp [sevenRow, sevenDuration, normalizedRow, nodeDuration,
        real_inner_smul_left, inner_smul_right, real_inner_comm, div_eq_mul_inv, mul_comm]
    · have H := hHalf (posteriorWeight W β t (2^r)) hs true
      convert H using 1
      funext u
      simp [sevenRow, sevenDuration, normalizedRow, nodeDuration,
        real_inner_smul_left, inner_smul_right, real_inner_comm, div_eq_mul_inv, mul_comm]
    · have H := hHalf (queryWeight W β t (2^r)) hWeight false
      convert H using 1
      funext u
      simp [sevenRow, sevenDuration, normalizedRow, nodeDuration,
        real_inner_smul_left, inner_smul_right, real_inner_comm, div_eq_mul_inv, mul_comm]
    · have H := hCross false
      convert H using 1
      funext u
      simp [sevenRow, sevenDuration, normalizedRow,
        real_inner_smul_left, inner_smul_right, real_inner_comm, div_eq_mul_inv, mul_comm]
    · have H := hCross true
      convert H using 1
      funext u
      simp [sevenRow, sevenDuration, normalizedRow,
        real_inner_smul_left, inner_smul_right, real_inner_comm, div_eq_mul_inv, mul_comm]

theorem actualSevenRowMGF_of_adjacent_ratio
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) (r : ℕ) (hV : t (2^r+1) ≤ V)
    {B R : ℝ} (hB : 1 ≤ B) (hR : 1 ≤ R)
    (hProxy : (actualParisiPosteriorRowMGFProxy W β V : ℝ) ≤ R)
    (hRatio : ∀ j : Fin (2^r), previousDuration t (j+1)/previousDuration t j ≤ B^2) :
    ActualSevenRowMGFStatement W Z β hβ t V r
      (weightedProducerVariance B R r) (weightedProducerRadius B R r) := by
  apply actualSevenRowMGF_of_weight_bound W Z β hβ t ht V r hV hB hR hProxy
  intro j
  have hs : 0 ≤ posteriorWeight W β t (2^r) j := NNReal.coe_nonneg _
  have H := queryWeight_div_posteriorWeight_le W β hβ t ht (2^r) j (hRatio j)
  simpa only [abs_div, abs_of_nonneg hs, Real.sqrt_sq (by linarith : 0 ≤ B)] using H

theorem actual_seven_duration_tail_of_adjacent_ratio
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (V : ℝ≥0) (r : ℕ) (hV : t (2^r+1) ≤ V)
    {B R : ℝ} (hB : 1 ≤ B) (hR : 1 ≤ R)
    (hProxy : (actualParisiPosteriorRowMGFProxy W β V : ℝ) ≤ R)
    (hRatio : ∀ j : Fin (2^r), previousDuration t (j+1)/previousDuration t j ≤ B^2)
    {n : ℕ} (hn : 0 < n) {η : ℝ} (hη : 0 < η) :
    (linkedScalarRowsLaw W Z β V n).real
      {ω | 4*η^2*(2+5*(r+1 : ℝ)*∑ j : Fin (2^r), previousDuration t j) <
        ∑ i : SevenIndex r, ‖rowAverage (sevenRow W Z β hβ t V r i) ω‖^2} ≤
      2*(10*(2 : ℝ)^r-3)*(5 : ℝ)^(2^r)*Real.exp (-(n : ℝ)*
        min (η^2/(4*weightedProducerVariance B R r))
          (weightedProducerRadius B R r*η/2)) := by
  have hp := weightedProducerParameters_pos (lt_of_lt_of_le (by norm_num) hB) hR r
  exact actual_seven_duration_total_tail W Z β hβ t ht V r hn hp.1 hp.2 hη
    (actualSevenRowMGF_of_adjacent_ratio W Z β hβ t ht V r hV hB hR hProxy hRatio)

end SKConstants.Completion.LW
