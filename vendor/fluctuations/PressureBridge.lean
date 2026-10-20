module

public import SKFluctuationsOAI.Probability.SKFluctuations.Spin

@[expose] public section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

noncomputable section

open MeasureTheory ProbabilityTheory Filter

def laplaceScale (m : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(1 : ℝ) / 6 + 5 * m)

theorem laplaceScale_pos (m : ℝ) {n : ℕ} (hn : 0 < n) :
    0 < laplaceScale m n := by
  unfold laplaceScale
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

def quenchedPressure (beta : ℝ) (n : ℕ) : ℝ :=
  meanFreeEnergy beta n / (n : ℝ) - beta ^ 2 / 4

def positiveMassPressure (beta s : ℝ) (n : ℕ) : ℝ :=
  Real.log (mgf (completedFreeEnergy beta n) (completedLaw beta n) s) /
    ((n : ℝ) * s) - beta ^ 2 / 4

theorem completedCenteredLogLaplace_eq_log_mgf (beta s : ℝ) (n : ℕ) :
    completedCenteredLogLaplace beta s n =
      Real.log (mgf (completedFreeEnergy beta n) (completedLaw beta n) s) -
        s * meanFreeEnergy beta n := by
  have hfactor : completedLaplaceTransform beta s n =
      Real.exp (-s * meanFreeEnergy beta n) *
        mgf (completedFreeEnergy beta n) (completedLaw beta n) s := by
    simp_rw [completedLaplaceTransform, mul_sub, Real.exp_sub]
    rw [integral_div]
    simp only [mgf, Real.exp_neg, neg_mul, div_eq_mul_inv, mul_comm]
  have hmgf : 0 < mgf (completedFreeEnergy beta n) (completedLaw beta n) s :=
    mgf_pos (integrable_exp_completedFreeEnergy beta s n)
  unfold completedCenteredLogLaplace
  rw [hfactor, Real.log_mul (Real.exp_pos _).ne' hmgf.ne', Real.log_exp]
  ring

theorem completedCenteredLogLaplace_eq_pressure_gap (beta s : ℝ) {n : ℕ}
    (hn : 0 < n) (hs : s ≠ 0) :
    completedCenteredLogLaplace beta s n =
      ((n : ℝ) * s) *
        (positiveMassPressure beta s n - quenchedPressure beta n) := by
  rw [completedCenteredLogLaplace_eq_log_mgf]
  unfold positiveMassPressure quenchedPressure
  have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  field_simp [hnR, hs]
  ring

def pressureIncrement (beta m : ℝ) (n : ℕ) : ℝ :=
  positiveMassPressure beta (laplaceScale m n) n - quenchedPressure beta n

theorem completedCenteredLogLaplace_eq_pressureIncrement (beta m : ℝ) {n : ℕ}
    (hn : 0 < n) :
    completedCenteredLogLaplace beta (laplaceScale m n) n =
      ((n : ℝ) * laplaceScale m n) * pressureIncrement beta m n := by
  exact completedCenteredLogLaplace_eq_pressure_gap beta (laplaceScale m n)
    hn (laplaceScale_pos m hn).ne'

theorem pressureIncrement_nonneg (beta m : ℝ) {n : ℕ} (hn : 0 < n) :
    0 ≤ pressureIncrement beta m n := by
  have hK : 0 ≤ completedCenteredLogLaplace beta (laplaceScale m n) n := by
    rw [completedCenteredLogLaplace_eq]
    exact add_nonneg (centeredLogLaplace_nonneg _ _ _) (by positivity)
  rw [completedCenteredLogLaplace_eq_pressureIncrement beta m hn] at hK
  exact nonneg_of_mul_nonneg_right hK
    (mul_pos (Nat.cast_pos.mpr hn) (laplaceScale_pos m hn))

end

end OAI.SKFluctuations.LaplaceWindowFormalization
