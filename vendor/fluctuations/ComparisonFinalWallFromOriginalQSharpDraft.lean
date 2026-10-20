module

public import ComparisonConcretePositiveWallMeanFromPhysicalBranchesDraft
public import ComparisonActualRemainingWallAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter PositiveLaplaceAssembly
open scoped Topology NNReal
set_option autoImplicit false

def ActualRemainingOriginalQSharpCost : Prop :=
  ∀ beta : ℝ, 1 < beta →
    ∀ m : ℝ, 0 < m → m < 1 / 300 →
      ∀ᶠ n : ℕ in atTop,
        ∀ hp : ActualConcreteHighWallNumeric m n,
        ∀ epsilon : ℝ, ∀ hepsilon : epsilon ∈ Ioo (0 : ℝ) (beta^2),
        ∀ heps0 : upperInitialEpsilon m n ≤ epsilon,
          concreteSharpCostAtNumeric (beta^2) m n hp epsilon hepsilon heps0

theorem actual_remaining_high_wall_inputs_of_original_q_sharp_cost
    (Hsharp : ActualRemainingOriginalQSharpCost) :
    ActualRemainingHighWallInputs := by
  intro beta hbeta m hm hmmax
  have hbeta0 : 0 < beta := zero_lt_one.trans hbeta
  let betaNN : ℝ≥0 := ⟨beta, hbeta0.le⟩
  have hbetaNN : 0 < betaNN := by
    change (0 : ℝ) < beta
    exact hbeta0
  have hTemp : 1 < (betaNN : ℝ)^2 := by
    change 1 < beta^2
    nlinarith [sq_nonneg (beta - 1)]
  exact exists_concrete_high_wall_inputs_from_original_sharp_and_physical_branches
    hbetaNN hTemp hm hmmax (Hsharp beta hbeta m hm hmmax)

theorem main_fluctuation_statement_of_original_q_sharp_cost
    (Hsharp : ActualRemainingOriginalQSharpCost) :
    MainFluctuationStatement := by
  exact mainFluctuationStatement_of_remaining_actual_high_wall_inputs
    (actual_remaining_high_wall_inputs_of_original_q_sharp_cost Hsharp)

end OAI.SKFluctuations.LaplaceWindowFormalization
