module

public import SKConstants.Completion.SJ7.MeanLeftSums
public import SKConstants.Completion.LJ.RefinedResidual

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory Set
open scoped NNReal BigOperators

namespace SKConstants.Completion.SJ7
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

theorem residualCoarseA_integral_mean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (ht0 : t 0 = 0) (K : ℕ) :
    (∑ j ∈ Finset.range (K + 1), ∫ v in (t j : ℝ)..(t (j + 1) : ℝ),
      (β * actualParisiFullSusceptibilityExpected W β v - LJ.residualCoarseA W β t K j) *
        actualParisiFullSusceptibilitySquareExpected W β v) =
      actualParisiEnergyReference W β (t (K + 1)) - LJ.gridEnergy W β t K := by
  let p := actualParisiFullSusceptibilityExpected W β
  let r := actualParisiFullSusceptibilitySquareExpected W β
  let a := LJ.residualCoarseA W β t K
  have hr := continuous_actualParisiFullSusceptibilitySquareExpected W β
  have hp := continuous_actualParisiFullSusceptibilityExpected W β
  have hcell (j : ℕ) : (∫ v in (t j : ℝ)..(t (j + 1) : ℝ), (β * p v - a j) * r v) =
      β * (∫ v in (t j : ℝ)..(t (j + 1) : ℝ), p v * r v) -
        a j * ∫ v in (t j : ℝ)..(t (j + 1) : ℝ), r v := by
    calc
      _ = ∫ v in (t j : ℝ)..(t (j + 1) : ℝ), β * (p v * r v) - a j * r v := by
        apply intervalIntegral.integral_congr
        intro v _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (f := fun v => β * (p v * r v))
          (g := fun v => a j * r v) (((hp.mul hr).intervalIntegrable _ _).const_mul β)
          ((hr.intervalIntegrable _ _).const_mul (a j)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hcoef : (∑ j ∈ Finset.range (K + 1), a j *
      ∫ v in (t j : ℝ)..(t (j + 1) : ℝ), r v) = LJ.gridEnergy W β t K := by
    rw [Finset.sum_range_succ]
    have hz : a K = 0 := by simp [a, LJ.residualCoarseA]
    rw [hz, zero_mul, add_zero]
    unfold LJ.gridEnergy
    rw [Fin.sum_univ_eq_sum_range (fun j => LJ.gridPosteriorScale W β t j * LJ.gridQueryMean W β t j)]
    apply Finset.sum_congr rfl
    intro j hj
    have hlt := Finset.mem_range.mp hj
    change LJ.residualCoarseA W β t K j *
      (∫ v in (t j : ℝ)..(t (j + 1) : ℝ), actualParisiFullSusceptibilitySquareExpected W β v) = _
    rw [LJ.residualCoarseA, ite_eq_left hlt,
      actualParisiFullSusceptibilitySquareExpected_interval W β hβ _ _ (ht.monotone (Nat.le_succ j))]
    have hs := actualParisiPosteriorIntervalScale_sq W β hβ (t j) (t (j + 1)) (ht (Nat.lt_succ_self j))
    have hne : LJ.gridPosteriorScale W β t j ≠ 0 :=
      (NNReal.coe_pos.mpr (actualParisiPosteriorIntervalScale_pos W β hβ _ _ (ht (Nat.lt_succ_self j)))).ne'
    change (LJ.gridQueryMean W β t j / LJ.gridPosteriorScale W β t j) * _ = _
    change (LJ.gridPosteriorScale W β t j) ^ 2 = _ at hs
    rw [← hs]
    field_simp [hne]
  change (∑ j ∈ Finset.range (K + 1), ∫ v in (t j : ℝ)..(t (j + 1) : ℝ),
    (β * p v - a j) * r v) = _
  simp_rw [hcell]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hcoef,
    intervalIntegral.sum_integral_adjacent_intervals (f := fun v => p v * r v)
      (fun _ _ => (hp.mul hr).intervalIntegrable _ _), ht0, NNReal.coe_zero,
    ← energyReference_eq_beta_pr W β hβ (t (K + 1))]

theorem residualCoarseB_integral_mean (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht0 : t 0 = 0) (K : ℕ) :
    (∑ j ∈ Finset.range (K + 1), ∫ v in (t j : ℝ)..(t (j + 1) : ℝ),
      (Real.sqrt (actualParisiFullSusceptibilitySquareExpected W β v) - LJ.residualCoarseB W β t j) *
        actualParisiQueryRho W β v * actualParisiFullSusceptibilityExpected W β v) =
      actualParisiEnergyReference W β (t (K + 1)) - LJ.gridEnergy W β t K := by
  let p := actualParisiFullSusceptibilityExpected W β
  let r := actualParisiFullSusceptibilitySquareExpected W β
  let ρ := actualParisiQueryRho W β
  let b := LJ.residualCoarseB W β t
  have hp := continuous_actualParisiFullSusceptibilityExpected W β
  have hr := continuous_actualParisiFullSusceptibilitySquareExpected W β
  have hρ := continuous_actualParisiQueryRho W β
  have hcell (j : ℕ) : (∫ v in (t j : ℝ)..(t (j + 1) : ℝ), (Real.sqrt (r v) - b j) * ρ v * p v) =
      (∫ v in (t j : ℝ)..(t (j + 1) : ℝ), Real.sqrt (r v) * p v * ρ v) -
        b j * ∫ v in (t j : ℝ)..(t (j + 1) : ℝ), p v * ρ v := by
    calc
      _ = ∫ v in (t j : ℝ)..(t (j + 1) : ℝ), Real.sqrt (r v) * p v * ρ v - b j * (p v * ρ v) := by
        apply intervalIntegral.integral_congr
        intro v _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (f := fun v => Real.sqrt (r v) * p v * ρ v)
          (g := fun v => b j * (p v * ρ v))
          (((hr.sqrt.mul hp).mul hρ).intervalIntegrable _ _)
          (((hp.mul hρ).intervalIntegrable _ _).const_mul (b j)), intervalIntegral.integral_const_mul]
  have hcoef : (∑ j ∈ Finset.range (K + 1), b j *
      ∫ v in (t j : ℝ)..(t (j + 1) : ℝ), p v * ρ v) = LJ.gridEnergy W β t K := by
    rw [Finset.sum_range_succ']
    have hz : b 0 = 0 := by simp [b, LJ.residualCoarseB]
    rw [hz, zero_mul, add_zero]
    unfold LJ.gridEnergy
    rw [Fin.sum_univ_eq_sum_range (fun j => LJ.gridPosteriorScale W β t j * LJ.gridQueryMean W β t j)]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [b, LJ.residualCoarseB, LJ.gridQueryMean, LQ.actualParisiQueryIntervalSpinMean, p, ρ]
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
    ring
  change (∑ j ∈ Finset.range (K + 1), ∫ v in (t j : ℝ)..(t (j + 1) : ℝ),
    (Real.sqrt (r v) - b j) * ρ v * p v) = _
  simp_rw [hcell]
  rw [Finset.sum_sub_distrib, hcoef,
    intervalIntegral.sum_integral_adjacent_intervals (f := fun v => Real.sqrt (r v) * p v * ρ v)
      (fun _ _ => (((hr.sqrt.mul hp).mul hρ).intervalIntegrable _ _)), ht0, NNReal.coe_zero]
  rfl

end SKConstants.Completion.SJ7
