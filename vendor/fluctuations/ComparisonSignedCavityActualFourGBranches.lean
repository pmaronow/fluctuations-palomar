module

public import ComparisonSignedCavityActualOriginalClockResponse

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 10000000

def nativeActualOriginalFourGBranches : NativeActualWeightedBranches :=
  [(0,[.projection]),(1,[.highRow]),(2,[.retarget,.projection]),(3,[.retarget,.highRow])]

def nativeActualOriginalFourGCenteredBranches : NativeActualWeightedBranches :=
  nativeActualOriginalFourGBranches.map (fun b=>(b.1,b.2++[.center]))

theorem nativeActualOriginalFourGCenteredBranches_eq :
    nativeActualOriginalFourGCenteredBranches=
      [(0,[.projection,.center]),(1,[.highRow,.center]),
        (2,[.retarget,.projection,.center]),(3,[.retarget,.highRow,.center])] := rfl

def nativeOriginalClockFourGBranchBeta
    {n : ℕ} {as : List PositiveMass} {i star : ℕ} (U : ℕ) (K b : ℕ→ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) (tag : ℕ) : ℝ :=
  if tag<2 then -nativeOriginalClockGBranchBeta U K b st tag
  else nativeOriginalClockGBranchBeta U K b st (tag-2)/2

theorem nativeActualOriginalFourGBranches_length :
    ∀b∈nativeActualOriginalFourGBranches,b.2.length≤2 := by
  simp [nativeActualOriginalFourGBranches]

theorem nativeActualOriginalFourGBranches_marked :
    ∀b∈nativeActualOriginalFourGBranches,nativeActualExpansionMarkedCount b.2=1 := by
  simp [nativeActualOriginalFourGBranches,nativeActualExpansionMarkedCount,
    NativeActualExpansionOp.markedIncrement]

theorem nativeActualOriginalFourGCenteredBranches_length :
    ∀b∈nativeActualOriginalFourGCenteredBranches,b.2.length≤3 := by
  simp [nativeActualOriginalFourGCenteredBranches_eq]

theorem nativeActualOriginalFourGCenteredBranches_marked :
    ∀b∈nativeActualOriginalFourGCenteredBranches,nativeActualExpansionMarkedCount b.2=1 := by
  simp [nativeActualOriginalFourGCenteredBranches_eq,nativeActualExpansionMarkedCount,
    NativeActualExpansionOp.markedIncrement]

end OAI.SKFluctuations.Cavity
