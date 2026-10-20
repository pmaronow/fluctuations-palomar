module

public import ComparisonActualHighWallThetaZeroSelectedBinsGeometry
public import ComparisonActualHighWallThetaZeroSelectedRowsGeometryPositiveOrigin

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem Potential.retainedBins_geometry_positive_origin (P : Q.Potential) {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval Q P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ}
    (hag : Q.data.rmin ≤ ag) (hzg : zg ≤ 1) (bins : ℕ)
    (w : ℕ→ℝ) (hw : ∀j,0<w j) :
    let m:=Q.shiftedNativeModel
    let Js:=fun j b=>P.retainedBin c Dcuts ag zg (as j) bins (w j) b
    let p:=fun j i=>m.R (partitionPoint 0 (as j) i)
    let F:=P.retainedSupport c ag zg
    ∃l u : Fin bins→Icc (0:ℝ) 1,∃φ : ℕ→ℕ,StrictMono φ ∧ ∀b,
      ∀ᵐr∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠj in atTop,
        (r∈NativeSelectedMask.finiteSupport (p (φ j)) (Js (φ j) b) ↔
          r∈F∩Ioo (l b).val (u b).val) := by
  dsimp only
  let m:=Q.shiftedNativeModel
  let A:=fun j=>P.retainedRows c Dcuts ag zg (as j)
  let Js:=fun j b=>P.retainedBin c Dcuts ag zg (as j) bins (w j) b
  let p:=fun j i=>m.R (partitionPoint 0 (as j) i)
  let F:=P.retainedSupport c ag zg
  have hinterval j b : ∃l u : Icc (0:ℝ) 1,
      NativeSelectedMask.finiteSupport (p j) (Js j b)=
        NativeSelectedMask.finiteSupport (p j) (A j)∩Ioc l.val u.val := by
    have hrowEq : m.rowRadius (as j)=fun i=>p j i.val := by
      funext i
      unfold ShiftedNativeBandModel.rowRadius
      rw [physicalCutMass_sampleClockSteps m.q 0 (as j) i.val
        (by simpa only [sampleClockSteps_length] using Nat.le_of_lt_succ i.isLt)]
    apply NativeSelectedMask.native_bin_physical_interval (p j)
      (fun i k hik=>m.R_monotone (partitionPoint_mono (as j) (ho j) hik))
      (fun i=>⟨Q.data.hrbounds.1.le.trans (m.R_bounds _).1,(m.R_bounds _).2⟩)
      _ (A j) _ (physicalProfile_monotone_on_rows (n+1) _
        (sampleClockSteps_ordered m.q (as j) (ho j)) (m.q 0))
      ((firstWholeUnitCell_monotone P.negativeSet (m.rowRadius (as j))
        (m.rowRadius_monotone (as j) (ho j))).monotoneOn _) (hw j) b
  obtain ⟨l,u,φ,hφ,hmem⟩:=NativeSelectedMask.finite_bin_limits
    (fun j=>NativeSelectedMask.finiteSupport (p j) (A j))
    (fun j b=>NativeSelectedMask.finiteSupport (p j) (Js j b)) F
    (P.retainedSupport_measurable c hag hzg)
    (fun j b=>NativeSelectedMask.finiteSupport_measurable _ _) hinterval
    (P.retainedRows_support_ae_positive_origin c Dcuts as mesh ho he hmesh hm0 hlim hag hzg)
  exact ⟨l,u,φ,hφ,fun b=>(hmem b).1⟩
end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
