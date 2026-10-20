module

public import ComparisonSignedCavityActualFrozenGResourcePairing
public import ComparisonSignedCavityActualOriginalClockResponse

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
def actualGeneralClockHighGAtom {n : ℕ} 
    (bf hf : ℝ→ℝ≥0) (K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (U : ℕ) (a c e f : T.Slot) : T.Assignment→ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  nativeOriginalHighGAtom T U K b
    (nativePhysicalResourceCenter n bf hf as) a c e f

def NativeOriginalGMarkedWord.physicalClockAtom {n : ℕ} 
    (bf hf : ℝ→ℝ≥0) (K : ℕ→ℝ)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (g : NativeOriginalGMarkedWord T) (U : ℕ) (a : T.Slot) : g.tree.Assignment→ℝ :=
  actualGeneralClockHighGAtom bf hf K g.tree U
    (g.z.embed (g.r.embed (g.p.embed a))) (g.z.embed (g.r.embed g.p.mark))
    (g.z.embed g.r.mark) g.z.mark

end OAI.SKFluctuations.Cavity
