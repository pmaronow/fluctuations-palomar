module

public import SKConstants.ParisiCDFHigherJets

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

theorem dyadicScalar_uniform_derivative_bounds_lower_time {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) {β : ℝ} (hβ : β ≠ 0)
    {τ : ℝ} (hτ : 0 < τ) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : ℝ) (t : ℝ≥0), τ ≤ (t : ℝ) → ∀ n x,
      |iteratedDeriv (m + 2) (dyadicScalar β α n s t scalarSpinTerminal) x| ≤ C := by
  let δ := β ^ 2 * τ / 2
  have hδ : 0 < δ := by dsimp [δ]; exact div_pos (mul_pos (sq_pos_of_ne_zero hβ) hτ) (by norm_num)
  obtain ⟨C, hC, hbound⟩ := finiteGradient_uniform_smoothing (m + 1) 1 (by norm_num) δ hδ
  refine ⟨C, hC, ?_⟩
  intro s t ht n x
  let c := dyadicCDFCoefficient α n s t
  let h := Real.toNNReal (β ^ 2) * dyadicCDFMesh n t
  have hh : ((2 ^ n : ℕ) : ℝ) * h = β ^ 2 * (t : ℝ) := by
    simp only [h, dyadicCDFMesh, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_pow,
      NNReal.coe_ofNat, Real.coe_toNNReal _ (sq_nonneg β), Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  have hhor : (0 : ℝ) + δ ≤ ((2 ^ n : ℕ) : ℝ) * h := by
    rw [hh]
    dsimp [δ]
    nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg β), mul_pos (sq_pos_of_ne_zero hβ) hτ]
  have HH := hbound (softAbs 1) (regularDatum_softAbs (by norm_num : (1 : ℝ) ≠ 0))
    (softAbs_lipschitz (by norm_num : (1 : ℝ) ≠ 0)) c h (2 ^ n) 0 0 le_rfl hhor
    (fun r _ => finiteCoeff_le_one (dyadicCDFCoefficient_le_one hα n s t) h (2 ^ n) 0 r)
    (m + 1) le_rfl 0 ⟨le_rfl, le_rfl⟩ x
  rw [dyadicScalar_eq_finiteValue_zero hα β n s t]
  simpa only [iteratedDeriv_succ'] using HH

theorem scalarCDFValue_uniform_strip_derivative_bounds {α : ℝ → ℝ}
    (hα : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hmono : Monotone α)
    {β : ℝ} (hβ : β ≠ 0) {T : ℝ} (hT : T < 1) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Icc (0 : ℝ) T, ∀ x,
      |iteratedDeriv (m + 2) (scalarCDFValue β α r (Real.toNNReal (1 - r))) x| ≤ C := by
  obtain ⟨C, hC, hb⟩ := dyadicScalar_uniform_derivative_bounds_lower_time hα hβ
    (show 0 < 1 - T by linarith) m
  refine ⟨C, hC, ?_⟩
  intro r hr x
  have hr1 : r < 1 := hr.2.trans_lt hT
  have ht0 : 0 < (Real.toNNReal (1 - r) : ℝ) := by
    rw [Real.coe_toNNReal _ (by linarith)]
    linarith
  have ht1 : Real.toNNReal (1 - r) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith [hr.1]
  have htτ : 1 - T ≤ (Real.toNNReal (1 - r) : ℝ) := by
    rw [Real.coe_toNNReal _ (by linarith)]
    linarith [hr.2]
  exact iteratedDeriv_limit_bound (m + 2)
    ((scalarCDFValue_contDiff_and_higher_derivative_limit hα hmono hβ r _ ht0 ht1).2 (m + 2))
    (fun n x => hb r _ htτ n x) x

end SKConstants.ParisiFullSupport
