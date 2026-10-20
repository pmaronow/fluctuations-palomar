module

public import ComparisonActualGeneralConstantJointFourIteration

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped NNReal

theorem actual_general_constant_frozen_correction_index_congr
    {n : ℕ} (bf hf : ℝ→ℝ≥0) (as : List PositiveMass)
    {star star' U : ℕ} (hs : star < U) (hs' : star' < U) (hU : U ≤ as.length)
    (Hstar : star=star') (W : ℝ) :
    actualGeneralConstantSourceFrozenCorrection (n:=n) bf hf as star U hs hU W=
      actualGeneralConstantSourceFrozenCorrection (n:=n) bf hf as star' U hs' hU W := by
  cases Hstar
  rfl

end OAI.SKFluctuations.Cavity
