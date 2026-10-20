module

public import SKBarriers2.Corner.FrozenCoef9

@[expose] public section

noncomputable section
open scoped BigOperators Matrix ContDiff Topology NNReal
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic SKOptimized.Overshoot
namespace SKBarriers2.Corner

def frozenUnitMass : Fin 12 → ℝ :=
  ![1 / 3, 1 / 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def frozenUnitDirection (β k : ℝ) : Fin 12 → Vec3 :=
  ![β • commonVector (1 / 2) k,
    (β * Real.sqrt (1 / 2)) • sharedVector (1 / 2) k,
    (β * Real.sqrt (1 / 2)) • rampVector (1 / 2) k,
    (β * Real.sqrt (1 / 2)) • rampVector (1 / 2) k,
    (β * Real.sqrt (1 / 2)) • postXVector (1 / 2) k,
    (β * Real.sqrt (1 / 2)) • postYVector (1 / 2) k,
    (β * (k * Real.sqrt (4 * varianceCoefficient (1 / 2)))) • rampVector (1 / 2) 0,
    (β * (k * Real.sqrt (4 * varianceCoefficient (1 / 2)))) •
      ((1 / Real.sqrt 2) • sharedVector (1 / 2) 0),
    (β * (k * Real.sqrt (4 * varianceCoefficient (1 / 2)))) • ((1 / 2 : ℝ) • contrast),
    (β * Real.sqrt (2 - OW.repairLength (1 / 2) k)) • Pi.single 0 1,
    (β * Real.sqrt (2 - OW.repairLength (1 / 2) k)) • Pi.single 1 1,
    (β * Real.sqrt (2 - OW.repairLength (1 / 2) k)) • Pi.single 2 1]

theorem frozenSchedule_eq_labelled (β a h k : ℝ) (hh : 0 ≤ h) :
    frozenSchedule β a (1 / 2) h k =
      (List.finRange 12).map (fun j => (a * frozenUnitMass j, Real.sqrt h • frozenUnitDirection β k j)) := by
  rw [← List.ofFn_eq_map]
  have hhalf : (1 : ℝ) - (2 : ℝ)⁻¹ = (2 : ℝ)⁻¹ := by norm_num
  simp [frozenSchedule, frozenCommon, frozenShared, frozenInner, frozenUnitMass,
    frozenUnitDirection, List.ofFn_succ, Real.sqrt_mul hh, smul_smul, hhalf,
    div_eq_mul_inv, mul_left_comm, mul_comm]

end SKBarriers2.Corner
