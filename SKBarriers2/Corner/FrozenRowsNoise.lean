module

public import SKBarriers2.Corner.FrozenRowsNoiseCore
public import SKBarriers2.Corner.FrozenDirections
public import SKBarriers2.Corner.FrozenCoefficientRegularity

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open MeasureTheory ProbabilityTheory Set Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

theorem frozenUnitDirection_contDiffAt_k (β : ℝ) {k : ℝ}
    (hk : |k| < 3 / 5) (j : Fin 12) :
    ContDiffAt ℝ ∞ (fun t => frozenUnitDirection β t j) k := by
  have hr : 0 < 2 - OW.repairLength (1 / 2) k := by
    have hsq : k ^ 2 < (3 / 5 : ℝ) ^ 2 := by
      have H := mul_pos (sub_pos.mpr hk) (by positivity : 0 < (3 / 5 : ℝ) + |k|)
      nlinarith [sq_abs k]
    norm_num [OW.repairLength, varianceCoefficient, tentWeight, rampWeight]
    nlinarith
  have hroot : ContDiffAt ℝ ∞
      (fun t : ℝ => Real.sqrt (2 - OW.repairLength (1 / 2) t)) k := by
    have H : ContDiffAt ℝ ∞ (fun t : ℝ => 2 - OW.repairLength (1 / 2) t) k := by
      unfold OW.repairLength
      fun_prop
    exact H.sqrt (ne_of_gt hr)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases j <;> fin_cases i <;>
    dsimp [frozenUnitDirection, Matrix.vecCons, Fin.cons, Fin.cases, Fin.induction,
      Fin.induction.go, commonVector, sharedVector, rampVector, postXVector,
      postYVector, contrast] <;> fun_prop

end SKBarriers2.Corner
