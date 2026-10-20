module

public import ComparisonNativeActualLowerPressureComparison
public import ComparisonNativeActualInitialUpperComparison
public import ActualUpperWallIteration
public import FinalAssembly
public import SKFluctuationsOAI.Probability.SKFluctuations.EventuallyNatPos

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter PositiveLaplaceAssembly
open scoped Topology

def ActualRemainingHighWallInputs : Prop :=
  ∀ beta : ℝ,1 < beta → ∀ m : ℝ,0 < m → m < 1/300 →
    ∃Cw : ℝ,1 ≤ Cw ∧ ∀ᶠn : ℕ in atTop,
      ∀hp : ConcreteHighWallGeometry m n,
        ∀epsilon∈Ioo (0:ℝ) (beta^2),upperInitialEpsilon m n ≤ epsilon →
          concreteHighWallPhysicalInputs (beta^2) Cw m n hp epsilon

theorem actual_upperComparison_of_remaining_high_wall_inputs
    (Hwall : ActualRemainingHighWallInputs)
    (beta : ℝ) (hbeta : 1 < beta) (m : ℝ) (hm : 0 < m) (hmmax : m < 1/300) :
    ∃C : ℝ,0 ≤ C ∧ ∀ᶠn : ℕ in atTop,
      pressureIncrement beta m n ≤ C*upperPressureLedger m n := by
  obtain ⟨Ci,hCi,Hinitial⟩:=exists_actual_initial_upper_comparison_real_beta beta hbeta hm hmmax
  obtain ⟨Cw,hCw,Hhigh⟩:=Hwall beta hbeta m hm hmmax
  obtain ⟨C,hC,HC⟩:=actual_upperPressureLedger_of_comparison_and_wall_mean
    hbeta hCi hCw hm hmmax Hinitial Hhigh
  exact ⟨C,hC.le,HC⟩

theorem positiveLaplaceWindow_of_remaining_actual_high_wall_inputs
    (Hwall : ActualRemainingHighWallInputs) : PositiveLaplaceWindow := by
  exact positiveLaplaceWindow_of_manuscript_pressure_estimates actual_lowerComparison
    (actual_upperComparison_of_remaining_high_wall_inputs Hwall)

theorem mainFluctuationStatement_of_remaining_actual_high_wall_inputs
    (Hwall : ActualRemainingHighWallInputs) : MainFluctuationStatement := by
  exact main_of_positiveLaplaceWindow
    (positiveLaplaceWindow_of_remaining_actual_high_wall_inputs Hwall)

end OAI.SKFluctuations.LaplaceWindowFormalization
