module

public import SKConstants.Completion.LGram.IIDEvent
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SKConstants.Completion.LGram
open SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem squareVarianceScale_three_le {K : ℝ} (hK : 1 ≤ K) :
    Concentration.squareVarianceScale K 3 ≤
      K * (3 + 2 * Real.exp 1 + 4 * Real.log (2 * Real.exp 1 * K)) := by
  have hK0 : 0 ≤ K := by linarith
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have harg : 1 ≤ 2 * Real.exp 1 * K := by nlinarith
  have hlog : 0 ≤ Real.log (2 * Real.exp 1 * K) := Real.log_nonneg harg
  have hquot : 0 < 2 * Real.exp 1 * K / 3 := by positivity
  have hl : max 0 (Real.log (2 * Real.exp 1 * K / 3)) ≤ Real.log (2 * Real.exp 1 * K) := by
    apply max_le hlog
    apply Real.log_le_log hquot
    nlinarith
  unfold Concentration.squareVarianceScale Concentration.squareVarianceCutoff
  apply max_le
  · nlinarith [mul_nonneg hK0 hlog]
  · apply max_le
    · nlinarith [mul_nonneg hK0 hlog]
    · have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 4*K by positivity)
      nlinarith

theorem gramTailBudget_eq_exponential (N d : ℕ) (K η : ℝ)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    gramTailBudget N d K η = 2 * Real.exp
      ((d:ℝ)*Real.log 9 - (N:ℝ)*η^2 / (768 * Concentration.squareVarianceScale K 3)) := by
  rw [gramTailBudget_eq_quadratic N d K η hη hη1]
  have h9 : (9:ℝ)^d = Real.exp ((d:ℝ)*Real.log 9) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [h9, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem mixedRowMGFProxy_global_bound {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ≥0,
      (actualParisiFullMixedRowMGFProxy W β H:ℝ) ≤
        C * Real.exp ((H:ℝ)/2) * Real.sqrt (1+(H:ℝ)) := by
  obtain ⟨C, hC, hB⟩ := actualParisiPosteriorRowMGFProxy_global_bound W β hβ
  refine ⟨4*C+8, by positivity, ?_⟩
  intro H
  have he : 1 ≤ Real.exp ((H:ℝ)/2) := Real.one_le_exp_iff.mpr (by positivity)
  have hs : 1 ≤ Real.sqrt (1+(H:ℝ)) := Real.one_le_sqrt.mpr (by linarith [H.coe_nonneg])
  have hprod : 1 ≤ Real.exp ((H:ℝ)/2)*Real.sqrt (1+(H:ℝ)) := by nlinarith
  have h := hB H
  simp only [actualParisiFullMixedRowMGFProxy, NNReal.coe_add, NNReal.coe_mul,
    NNReal.coe_ofNat]
  nlinarith

theorem gramTailBudget_power (N d : ℕ) (hN : 0 < N) (K γ : ℝ) (hγ : 0 ≤ γ) :
    gramTailBudget N d K ((N:ℝ)^(-γ)) = 2 * Real.exp
      ((d:ℝ)*Real.log 9 - (N:ℝ)^(1-2*γ) / (768 * Concentration.squareVarianceScale K 3)) := by
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hn1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hη : 0 < (N:ℝ)^(-γ) := Real.rpow_pos_of_pos hn _
  have hη1 : (N:ℝ)^(-γ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
  rw [gramTailBudget_eq_exponential N d K _ hη.le hη1]
  have hp : (N:ℝ)*((N:ℝ)^(-γ))^2 = (N:ℝ)^(1-2*γ) := by
    calc
      _ = (N:ℝ)^(1:ℝ) * (N:ℝ)^((-γ)*2) := by
        rw [Real.rpow_one, Real.rpow_mul hn.le, Real.rpow_two]
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  rw [hp]

end SKConstants.Completion.LGram
