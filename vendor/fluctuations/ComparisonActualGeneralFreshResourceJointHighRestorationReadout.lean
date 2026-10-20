module

public import ComparisonActualGeneralCenteredResourceJointHighRestorationReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

def actualGeneralOriginalFreshResourceJointHighRestoration
    {n : ℕ} (kind : NativeJointHighRestorationKind) (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  nativeJointHighRestorationSource kind n q U b h K C g.tree
    (fun σ=>Pc (g.restRestrict σ)) (g.embed P.live.test.target) g.mark

theorem actual_general_original_fresh_resource_joint_HIGH_restoration_eq_centered_retarget
    {n : ℕ} (kind : NativeJointHighRestorationKind) (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as) :
    let g:=nativeFreshAtSlot T 0 P.live.test.target star
    actualGeneralOriginalFreshResourceJointHighRestoration kind bf hf U P=
      actualGeneralOriginalCenteredResourceJointHighRestoration kind bf hf U (P.retarget 0)
        (g.embed P.live.test.target) g.mark := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_centered_resource_fresh_rest_readout (U:=U) q b h K C T P ho
  dsimp only at Hread
  rw [HQ] at Hread
  unfold actualGeneralOriginalFreshResourceJointHighRestoration actualGeneralOriginalCenteredResourceJointHighRestoration
  dsimp only
  rw [Hread]

end OAI.SKFluctuations.Cavity
