module

public import ComparisonSignedCavityActualResourceJointLowRestorationReadout
public import ComparisonSignedCavityJointLowRestorationAdditivity
public import ComparisonSignedCavityActualCenteredResourceLowTaylorReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

def nativeActualOriginalCenteredResourceJointLowRestoration
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (a z : T.Slot) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let C:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  nativeCenteredLowGammaLowRestoration n q U b h K C T Pc a z

theorem native_actual_original_centered_resource_joint_LOW_restoration_eq_two_resources
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as) (hU : U ≤ as.length)
    (a z : T.Slot) :
    nativeActualOriginalCenteredResourceJointLowRestoration M U P a z=
      nativeActualResourceJointLowRestoration M U P a z+
      nativeActualResourceJointLowRestoration M U P.freeze a z := by
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
  unfold nativeActualOriginalCenteredResourceJointLowRestoration nativeActualResourceJointLowRestoration
  dsimp only
  rw [Hread]
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from M.inherited_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from M.inherited_hf_monotone hu hv huv) as ho
  have HK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have HKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  exact native_centered_low_gamma_low_restoration_add n q U b h K C T ho _ _ a z
    (by intro j x;cases x <;> exact NNReal.coe_nonneg _)
    (by intro x;cases x <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) HK hbm hhm HKm hU

end OAI.SKFluctuations.Cavity
