module

public import ComparisonSignedCavitySecondLowInitialEntrySource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

theorem actual_general_second_low_unobserved_class_eq_entry_four
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (hU : U ≤ as.length)
    (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot) (j : Fin 8) :
    nativeSecondLowClassLedger n q U b h K T hU P a z j false=
      nativeSecondLowEntryFourAverage T U (nativeSecondLowFirstMiddleIsFirst j)
        (nativeSecondLowUnobservedWord n q U b h K hU P a z j) := by
  rw [native_second_low_unobserved_class_eq_entry_ledger]
  unfold nativeSecondLowUnobservedEntryLedger nativeSecondLowEntryFourAverage nativeSecondLowBudgetEntryRows
  cases nativeSecondLowFirstMiddleIsFirst j <;> rfl

end OAI.SKFluctuations.Cavity
