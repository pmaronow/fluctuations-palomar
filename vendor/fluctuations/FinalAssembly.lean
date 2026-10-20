module

public import PressureBridge
public import LowerLedger
public import UpperPowerLedger

@[expose] public section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

noncomputable section

open Filter
open PositiveLaplaceAssembly

theorem positiveLaplaceWindow_of_manuscript_pressure_estimates
    (lowerComparison :
      ∀ beta : ℝ, 1 < beta → ∀ m : ℝ, 0 < m → m < 1 / 300 →
        ∃ a b : ℝ, 0 < a ∧ ∀ᶠ n : ℕ in atTop,
          a * lowerEpsilon n * (lowerScale m n) ^ 3 -
            b * (n : ℝ) ^ (20 * lowerDelta m) * lowerError m n ≤
              pressureIncrement beta m n)
    (upperComparison :
      ∀ beta : ℝ, 1 < beta → ∀ m : ℝ, 0 < m → m < 1 / 300 →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
          pressureIncrement beta m n ≤ C * upperPressureLedger m n) :
    PositiveLaplaceWindow := by
  intro beta hbeta m hm hmmax
  obtain ⟨a, b, ha, hlower⟩ := lowerComparison beta hbeta m hm hmmax
  obtain ⟨C, hC, hupper⟩ := upperComparison beta hbeta m hm hmmax
  have hidentity : ∀ᶠ n : ℕ in atTop,
      completedCenteredLogLaplace beta (laplaceScale m n) n =
        (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 6 + 5 * m) *
          pressureIncrement beta m n := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact completedCenteredLogLaplace_eq_pressureIncrement beta m hn
  obtain ⟨C', hC', hupper'⟩ := eventually_upper_of_pressure_ledger
    (fun n => completedCenteredLogLaplace beta (laplaceScale m n) n)
    (pressureIncrement beta m) hm hC hidentity hupper
  have hlower' := lower_pressure_scaled_eventually
    (pressureIncrement beta m) b hm ha hlower
  have hboth : ∀ᶠ n : ℕ in atTop,
      (a / 2) * (n : ℝ) ^ (20 * m) ≤
        completedCenteredLogLaplace beta (laplaceScale m n) n ∧
      completedCenteredLogLaplace beta (laplaceScale m n) n ≤
        C' * (n : ℝ) ^ (100 * m) := by
    filter_upwards [hlower', hupper', eventually_gt_atTop (0 : ℕ)]
      with n hnlow hnupper hn
    refine ⟨?_, hnupper⟩
    rw [completedCenteredLogLaplace_eq_pressureIncrement beta m hn]
    exact hnlow
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hboth
  exact ⟨a / 2, C', by positivity, hC', n₀, hn₀⟩

end

end OAI.SKFluctuations.LaplaceWindowFormalization
