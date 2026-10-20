module

public import ComparisonActualHighWallThetaZeroSelectedCapLabels
public import ComparisonActualHighWallThetaZeroSelectedRowsGeometryPositiveOrigin

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem Potential.retainedCapRepresentative_eventually_positive_origin (P : Q.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval Q P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ}
    (hag : Q.data.rmin ≤ ag) (hzg : zg ≤ 1) (t : ι)
    (hintersect : max ag (c t).left < min zg (c t).right)
    (hinterior : ∀d∈Dcuts,d∉Ioo (c t).left (c t).right) :
    ∀ᶠj in atTop,
      let rep:=P.retainedCapRepresentative c Dcuts ag zg (as j) t
      rep∈P.retainedRows c Dcuts ag zg (as j) ∧
        Q.shiftedNativeModel.rowRadius (as j) rep∈Ioo (c t).left (c t).right := by
  let r:=(max ag (c t).left+min zg (c t).right)/2
  have hrband : r∈Ioo ag zg:=by
    dsimp only [r]
    constructor
    · linarith [le_max_left ag (c t).left, hintersect]
    · linarith [min_le_left zg (c t).right, hintersect]
  have hr : r∈Ioo (c t).left (c t).right:=by
    dsimp only [r]
    constructor
    · linarith [le_max_right ag (c t).left, hintersect]
    · linarith [min_le_right zg (c t).right, hintersect]
  have hrD : r∉Dcuts:=fun hd=>hinterior r hd hr
  let m:=Q.shiftedNativeModel
  let p:=fun j i=>m.R (partitionPoint 0 (as j) i)
  obtain ⟨_,_,_,hdiam,ht⟩:=P.retained_grid as mesh ho he hmesh hm0 hlim
  filter_upwards [P.retainedRows_cell_eventually_positive_origin c Dcuts as mesh ho he hmesh hm0 hlim hag hzg
    hrband hrD (Or.inl ⟨t,hr⟩),
    NativeSelectedMask.cells_eventually_subset_open p _ _ hdiam ht
      (Ioo (c t).left (c t).right) isOpen_Ioo hr] with j hj hcj
  obtain ⟨i,hi,hil,hri⟩:=hj
  apply P.retainedCapRepresentative_mem c Dcuts ag zg (as j) t
  refine ⟨i,Finset.mem_filter.mpr ⟨hi,?_⟩⟩
  unfold ShiftedNativeBandModel.rowRadius
  rw [physicalCutMass_sampleClockSteps m.q 0 (as j) i.val hil.le]
  exact hcj i.val hil hri (left_mem_Icc.mpr (hri.1.le.trans hri.2))

theorem Potential.retainedBin_cap_support_eventually_positive_origin (P : Q.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval Q P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ}
    (hag : Q.data.rmin ≤ ag) (hzg : zg ≤ 1)
    (bins : ℕ) (hbins : 0<bins) (w : ℕ→ℝ)
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (labels : ι→Fin bins)
    (hlabels : ∀j t,P.retainedCapLabel c Dcuts ag zg (as j) bins hbins (w j) t=labels t)
    (t : ι) (b : Fin bins) {r : ℝ} (hr : r∈Ioo (c t).left (c t).right)
    (hrband : r∈Ioo ag zg) (hrD : r∉Dcuts) :
    let m:=Q.shiftedNativeModel
    ∀ᶠj in atTop,(r∈NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 (as j) i))
      (P.retainedBin c Dcuts ag zg (as j) bins (w j) b) ↔ labels t=b) := by
  dsimp only
  let m:=Q.shiftedNativeModel
  let p:=fun j i=>m.R (partitionPoint 0 (as j) i)
  obtain ⟨_,_,_,hdiam,ht⟩:=P.retained_grid as mesh ho he hmesh hm0 hlim
  have HC:=P.retainedRows_cell_eventually_positive_origin c Dcuts as mesh ho he hmesh hm0 hlim hag hzg
    hrband hrD (Or.inl ⟨t,hr⟩)
  filter_upwards [HC,NativeSelectedMask.cells_eventually_subset_open p _ _ hdiam ht
    (Ioo (c t).left (c t).right) isOpen_Ioo hr] with j hj hcj
  obtain ⟨i,hi,hil,hri⟩:=hj
  have hit : m.rowRadius (as j) i∈Ioo (c t).left (c t).right:=by
    unfold ShiftedNativeBandModel.rowRadius
    rw [physicalCutMass_sampleClockSteps m.q 0 (as j) i.val hil.le]
    exact hcj i.val hil hri (left_mem_Icc.mpr (hri.1.le.trans hri.2))
  rw [finiteSupport_mem_iff_of_original_cell (p j)
    (fun i k hik=>m.R_monotone (partitionPoint_mono (as j) (ho j) hik)) _ i hri,
    P.retainedBin_cap_label_iff c Dcuts ag zg (as j) bins hbins (w j) hwhole t b i hi hit,hlabels j t]
end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
