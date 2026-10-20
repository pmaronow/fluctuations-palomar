module

public import SKConstants.Completion.LQ.ActualGrowingQuadrature
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped NNReal BigOperators

namespace SKConstants.Completion.LJ
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

def growingLagCellScale (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (j : ℕ) : ℝ :=
  (growingQueryDuration δ j : ℝ) *
    Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β (growingQueryTime δ j))

theorem growingLagCellScale_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (j : ℕ) :
    growingLagCellScale W β δ j ≤
      Real.sqrt (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)) * (δ : ℝ) := by
  have hr := (actualParisiFullSusceptibilitySquareExpected_bounds W β (growingQueryTime δ j)).1
  have hc := LQ.mesh_profile_square_le (actualParisiFullSusceptibilitySquareExpected W β)
    (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)) δ j
      (LQ.actual_square_profile_tail W β hβ _ (LQ.meshTime_nonneg δ j))
  have hs : (growingLagCellScale W β δ j) ^ 2 ≤
      (Real.sqrt (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)) * (δ : ℝ)) ^ 2 := by
    rw [growingLagCellScale, mul_pow, Real.sq_sqrt hr, mul_pow,
      Real.sq_sqrt (Real.exp_pos _).le]
    simpa only [LQ.meshTime, LQ.meshDuration, mul_comm] using hc
  have hp : 0 ≤ growingLagCellScale W β δ j := by unfold growingLagCellScale; positivity
  nlinarith [mul_nonneg (Real.sqrt_nonneg
    (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2))) δ.coe_nonneg]

theorem growingLagCellScale_square_sum_le (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ)
    (hsmall : ∀ j < K + 1, growingQueryDuration δ j ≤ 1) :
    (∑ j ∈ Finset.range (K + 1), (growingLagCellScale W β δ j) ^ 2) ≤
      8 * Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * (δ : ℝ) := by
  have hcount := growingQuery_finite_count_bound δ hδ (K + 1) hsmall
  have hcell (j : ℕ) : (growingLagCellScale W β δ j) ^ 2 ≤
      Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * (δ : ℝ) ^ 2 := by
    have hr := (actualParisiFullSusceptibilitySquareExpected_bounds W β (growingQueryTime δ j)).1
    have hc := LQ.mesh_profile_square_le (actualParisiFullSusceptibilitySquareExpected W β)
      (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2)) δ j
        (LQ.actual_square_profile_tail W β hβ _ (LQ.meshTime_nonneg δ j))
    rw [growingLagCellScale, mul_pow, Real.sq_sqrt hr]
    simpa only [LQ.meshTime, LQ.meshDuration, mul_comm] using hc
  calc
    _ ≤ ∑ _j ∈ Finset.range (K + 1),
        Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * (δ : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun j _ => hcell j)
    _ = (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * (δ : ℝ)) *
        (((K + 1 : ℕ) : ℝ) * (δ : ℝ)) := by simp; ring
    _ ≤ (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ) / 2) * (δ : ℝ)) * 8 :=
      mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = _ := by ring

end SKConstants.Completion.LJ
