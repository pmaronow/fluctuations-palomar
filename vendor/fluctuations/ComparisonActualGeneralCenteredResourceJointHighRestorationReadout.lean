module

public import ComparisonActualGeneralResourceJointHighRestorationReadout
public import ComparisonSignedCavityActualCenteredResourceLowTaylorReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

def actualGeneralOriginalCenteredResourceJointHighRestoration
    {n : ℕ} (kind : NativeJointHighRestorationKind) (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (a z : T.Slot) : ℝ :=
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let qfull:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Pc:=nativeOriginalCenteredRestTest n q U b h K T (nativeActualResourceRestValue P 0 qfull 0 C)
  nativeJointHighRestorationSource kind n q U b h K C T Pc a z

theorem actual_general_original_centered_resource_joint_HIGH_restoration_eq_two_resources
    {n : ℕ} (kind : NativeJointHighRestorationKind) (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (U : ℕ) (P : NativeResourceTerm i star T) (ho : MassOrdered 0 as)
    (a z : T.Slot) :
    actualGeneralOriginalCenteredResourceJointHighRestoration kind bf hf U P a z=
      actualGeneralResourceJointHighRestoration kind bf hf U P a z+
      actualGeneralResourceJointHighRestoration kind bf hf U P.freeze a z := by
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
  unfold actualGeneralOriginalCenteredResourceJointHighRestoration actualGeneralResourceJointHighRestoration
  dsimp only
  rw [Hread]
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (bf u:ℝ) ≤ bf v from hbf hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (hf u:ℝ) ≤ hf v from hhf hu hv huv) as ho
  have HK:=native_continuum_mixed_clock_nonneg n bf hf hbf hhf as ho
  have HKm:=native_continuum_mixed_clock_monotone n bf hf hbf hhf as ho
  simpa only [one_mul] using native_joint_HIGH_restoration_source_test_linear kind n q U b h K C T ho
    (nativeActualResourceRestValue P 0 (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 C)
    (nativeActualResourceRestValue P.freeze 0 (finitePhysicalCavitySquareVariance n U as b h 1 1) 0 C) a z 1 1
    (by intro j x;cases x <;> exact NNReal.coe_nonneg _)
    (by intro x;cases x <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) HK hbm hhm HKm

end OAI.SKFluctuations.Cavity
