module

public import ComparisonActualGeneralTargetRawRestorationReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped NNReal

 theorem actual_general_target_raw_fresh_B0_eq_sole_root_joint_ledger
    {n : ℕ} (bf hf : ℝ→ℝ≥0) (as : List PositiveMass) (i U : ℕ) :
    actualGeneralTargetRawFreshB0Part (n:=n) bf hf as i U=
      let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
      let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
      let K:=fun j=>h j+b j*orderedPathS (n+1) bf hf (partitionPoint 0 as j)
      let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
      let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
      nativeSecondLowJointLedger n q U b h K g.tree (fun _=>1) [g.embed (singleSlot as),g.mark]/2 := rfl

end OAI.SKFluctuations.Cavity
