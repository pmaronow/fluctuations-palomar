module

public import ComparisonSignedCavityActualFourGaRestorationRate

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open Cavity MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
variable {S : Type} {as : List PositiveMass}

theorem actual_initial_four_seed_high_fork_free
    (i star U : ℕ) (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length) (a : ℝ)
    (f : ℕ→ℝ) (hlo : ∀j,j < U → f j=0) :
    (nativeActualInitialState (S:=S) as i star a (hi.trans (hs.le.trans hU))).tree.forkCost f=0 :=
  nativeActualInitialState_high_forkCost_zero as i star U hi hs (hi.trans (hs.le.trans hU)) a f hlo

theorem actual_projected_constant_four_seed_high_fork_free
    (i star U : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (f : ℕ→ℝ) (hlo : ∀j,j < U → f j=0) :
    ((nativeActualConstantState (S:=S) as i star).projection (hs.le.trans hU)).tree.forkCost f=0 := by
  change (nativeFreshAtSlot (single (S:=S) as) 0 (singleSlot as) star).tree.forkCost f=0
  rw [nativeFreshAtSlot_high_forkCost _ _ _ hs f hlo,single_forkCost]

end OAI.SKFluctuations.Hierarchy.ClockTree
