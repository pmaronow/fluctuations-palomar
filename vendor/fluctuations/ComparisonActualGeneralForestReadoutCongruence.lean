module

public import ComparisonActualGeneralFourFirstHighIteration
public import ComparisonActualGeneralConstantJointFourReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped NNReal BigOperators

 theorem actual_general_constant_forest_other_readout_congr
    {n : ℕ} (bf hf : ℝ→ℝ≥0) {as bs : List PositiveMass}
    {star star' U : ℕ} (hs : star < U) (hs' : star' < U)
    (hU : U ≤ as.length) (hU' : U ≤ bs.length)
    (Hab : as=bs) (Hstar : star=star') (W : ℝ) (level : ℕ) :
    actualGeneralFourOtherSourceErrorSum bf hf U W
      (actualGeneralFourCenteredForest (n:=n) bf hf hs hU W level
        (actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU))=
    actualGeneralFourOtherSourceErrorSum bf hf U W
      (actualGeneralFourCenteredForest (n:=n) bf hf hs' hU' W level
        (actualGeneralConstantSourceChildren (n:=n) bf hf bs star' U hs' hU')) := by
  cases Hab
  cases Hstar
  rfl

 theorem actual_general_initial_forest_other_readout_congr
    {n : ℕ} (bf hf : ℝ→ℝ≥0) {as bs : List PositiveMass}
    {i i' star star' U : ℕ} (hi : i ≤ star) (hi' : i' ≤ star')
    (hs : star < U) (hs' : star' < U) (hU : U ≤ as.length) (hU' : U ≤ bs.length)
    (Hab : as=bs) (Hi : i=i') (Hstar : star=star') (W seedMass : ℝ) (level : ℕ) :
    actualGeneralFourOtherSourceErrorSum bf hf U W
      (actualGeneralFourCenteredForest (n:=n) bf hf hs hU W level
        [nativeActualInitialState (S:=Spin n×Bool) as i star seedMass (hi.trans (hs.le.trans hU))])=
    actualGeneralFourOtherSourceErrorSum bf hf U W
      (actualGeneralFourCenteredForest (n:=n) bf hf hs' hU' W level
        [nativeActualInitialState (S:=Spin n×Bool) bs i' star' seedMass (hi'.trans (hs'.le.trans hU'))]) := by
  cases Hab
  cases Hi
  cases Hstar
  rfl

end OAI.SKFluctuations.Cavity
