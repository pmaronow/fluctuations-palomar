module

public import ComparisonSignedCavityActualResourceLowTaylorReadout
public import ComparisonSignedCavityActualCenteredResourceFreshRestReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000

theorem native_actual_resource_original_centered_rest_eq_two_resources
    {n : ℕ} {as : List PositiveMass} {i star U : ℕ}
    (q : ℕ→RestCoordinate n→ℝ) (b h K C : ℕ→ℝ)
    (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T)
    (ho : MassOrdered 0 as) :
    let qfull:=cutFullVariance n q U 1 1 b h K
    nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)=
      fun σ=>nativeActualResourceRestValue P 0 qfull 0 C σ+
        nativeActualResourceRestValue P.freeze 0 qfull 0 C σ := by
  let qfull:=cutFullVariance n q U 1 1 b h K
  dsimp only
  funext σ
  let τ:=T.cavityAssignment.symm (σ,assignmentOfSlots T.cavityRight (fun _=>false))
  have ht : (T.cavityAssignment τ).1=σ:=by dsimp only [τ];rw [Equiv.apply_symm_apply]
  have HT:=congrFun (native_actual_resource_original_centered_readout P 0 qfull 0 C q U b h K) τ
  have HP:=native_actual_resource_rest_value_eq_full P 0 qfull 0 C τ
  have HF:=native_actual_resource_rest_value_eq_full P.freeze 0 qfull 0 C τ
  rw [ht] at HT HP HF
  rw [HP,HF,P.freeze_value (fullWeight_pos n) (fullFeature n) ho]
  simpa only [qfull,sub_eq_add_neg] using HT

def nativeActualOriginalCenteredResourceThirdLowPart
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (a z : T.Slot) (l t : ℝ) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  nativeActualCenteredThirdLowPart n q U b h K T Pc a z l t

theorem native_actual_original_centered_resource_third_LOW_eq_two_resources
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    (a z : T.Slot) (l t : ℝ) :
    nativeActualOriginalCenteredResourceThirdLowPart M U P a z l t=
      nativeActualResourceThirdLowPart M U P a z l t+
      nativeActualResourceThirdLowPart M U P.freeze a z l t := by
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  have Hread:=native_actual_resource_original_centered_rest_eq_two_resources (U:=U) q b h K C T P ho
  dsimp only at Hread
  rw [HQ] at Hread
  unfold nativeActualOriginalCenteredResourceThirdLowPart nativeActualResourceThirdLowPart
  dsimp only
  rw [Hread,actual_nativeActualCenteredThirdLowPart_add_test]

end OAI.SKFluctuations.Cavity
