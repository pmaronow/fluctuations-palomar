module

public import ComparisonActualGeneralResourceTransientLowReadout
public import ComparisonSignedCavityActualCenteredResourceJointLowRestorationReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

def actualGeneralOriginalCenteredResourceTransientLowPart
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (a z : T.Slot) (part : NativeTransientLowErrorPart) (l t : ℝ) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  nativeTransientCenteredLowErrorPart n q i star U b h K T Pc (sitePair T a z) 0 part l t

theorem actual_general_original_centered_resource_transient_LOW_eq_two_resources
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    (a z : T.Slot) (part : NativeTransientLowErrorPart) (l t : ℝ) :
    actualGeneralOriginalCenteredResourceTransientLowPart bf hf U P a z part l t=
      actualGeneralResourceTransientLowPart bf hf U P a z part l t+
      actualGeneralResourceTransientLowPart bf hf U P.freeze a z part l t := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_resource_original_centered_rest_eq_two_resources (U:=U) q b h K C T P ho
  dsimp only at Hread
  rw [HQ] at Hread
  unfold actualGeneralOriginalCenteredResourceTransientLowPart actualGeneralResourceTransientLowPart
  dsimp only
  rw [Hread,actual_nativeTransientCenteredLowErrorPart_add_test]

end OAI.SKFluctuations.Cavity
