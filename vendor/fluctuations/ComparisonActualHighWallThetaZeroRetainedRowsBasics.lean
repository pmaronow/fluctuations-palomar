module

public import ComparisonActualHighWallThetaZeroCapFamily
public import ComparisonActualHighWallRetainedUnitGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000
attribute [local instance] Classical.propDecidable

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
variable {Q:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

def Potential.retainedRows (P:Q.Potential) {ι:Type*}
    (c:ι→ShiftedCapInterval Q P) (Dcuts:Finset ℝ) (ag zg:ℝ)
    (as:List PositiveMass):
    Finset (Fin ((sampleClockSteps Q.shiftedNativeModel.q 0 as).length+1)):=
  Finset.univ.filter (fun i=>i.val<as.length ∧
    NativeSelectedMask.rowSelected (fun t=>(c t).left) (fun t=>(c t).right) P.H
      Q.shiftedNativeModel.R (partitionPoint 0 as) Dcuts i.val ∧
    0<pathMassDifferences (sampleClockSteps Q.shiftedNativeModel.q 0 as) 0 i ∧
    Q.data.s≤partitionPoint 0 as i.val ∧
    ag≤Q.shiftedNativeModel.R (partitionPoint 0 as i.val) ∧
    Q.shiftedNativeModel.R (partitionPoint 0 as (i.val+1))≤zg)

theorem Potential.retainedRows_mem (P:Q.Potential) {ι:Type*}
    (c:ι→ShiftedCapInterval Q P) (Dcuts:Finset ℝ) (ag zg:ℝ)
    (as:List PositiveMass)
    (i:Fin ((sampleClockSteps Q.shiftedNativeModel.q 0 as).length+1)):
    i∈P.retainedRows c Dcuts ag zg as ↔ i.val<as.length ∧
    NativeSelectedMask.rowSelected (fun t=>(c t).left) (fun t=>(c t).right) P.H
      Q.shiftedNativeModel.R (partitionPoint 0 as) Dcuts i.val ∧
    0<pathMassDifferences (sampleClockSteps Q.shiftedNativeModel.q 0 as) 0 i ∧
    Q.data.s≤partitionPoint 0 as i.val ∧
    ag≤Q.shiftedNativeModel.R (partitionPoint 0 as i.val) ∧
    Q.shiftedNativeModel.R (partitionPoint 0 as (i.val+1))≤zg:=by
  simp only [retainedRows,Finset.mem_filter,Finset.mem_univ,true_and]

theorem Potential.capFamily_wholeUnit (P:Q.Potential)
    (F:Finset (ordConnectedSection P.negativeSet)) (t:F) {r:ℝ}
    (hr:r∈Ioo (P.capFamily F t).left (P.capFamily F t).right):
    wholeUnit P.negativeSet r=Ioo (P.capFamily F t).left (P.capFamily F t).right:=by
  have HH:=wholeCap_component_endpoints P.negativeSet_open P.negativeSet_subset
    (ordConnectedSection_subset t.val.property)
  have hcomp:r∈ordConnectedComponent P.negativeSet t.val.val:=by
    exact HH.2.2.2.2.1.symm ▸ hr
  have hrU:=ordConnectedComponent_subset hcomp
  unfold wholeUnit
  rw [ite_eq_left hrU,←ordConnectedComponent_eq hcomp]
  exact HH.2.2.2.2.1

def Potential.retainedSupport (P:Q.Potential) {ι:Type*}
    (c:ι→ShiftedCapInterval Q P) (ag zg:ℝ):Set ℝ:=
  Ioo ag zg∩NativeSelectedMask.fixedSupport
    (fun t=>(c t).left) (fun t=>(c t).right) P.H

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
