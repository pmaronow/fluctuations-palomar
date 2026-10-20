module

public import ComparisonActualHighWallSelectedCapEndpoints
public import ComparisonActualHighWallThetaZeroSelectedCapLabels
public import ComparisonActualHighWallThetaZeroRetainedBinBasics

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option autoImplicit false
set_option maxHeartbeats 24000000
attribute [local instance] Classical.propDecidable
private theorem cap_extrema_tendsto {left right : ℝ} (hlt : left<right)
    (low high error : ℕ→ℝ) (herror : Tendsto error atTop (𝓝 0))
    (hbound : ∀ᶠj in atTop,left ≤ low j ∧ high j ≤ right)
    (hcover : ∀r∈Ioo left right,∀ᶠj in atTop,low j ≤ r ∧ r-error j ≤ high j) :
    Tendsto low atTop (𝓝 left) ∧ Tendsto high atTop (𝓝 right) := by
  constructor
  · apply Metric.tendsto_nhds.mpr
    intro epsilon hepsilon
    let z:=left+min (epsilon/2) ((right-left)/2)
    have hz : z∈Ioo left right := by
      have hm:=lt_min (half_pos hepsilon) (half_pos (sub_pos.mpr hlt))
      have hb:=min_le_right (epsilon/2) ((right-left)/2)
      dsimp only [z]
      constructor <;> linarith
    filter_upwards [hbound,hcover z hz] with j hj hc
    rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hj.1)]
    have hm:=min_le_left (epsilon/2) ((right-left)/2)
    dsimp only [z] at hc
    linarith
  · apply Metric.tendsto_nhds.mpr
    intro epsilon hepsilon
    let z:=right-min (epsilon/2) ((right-left)/2)
    have hz : z∈Ioo left right := by
      have hm:=lt_min (half_pos hepsilon) (half_pos (sub_pos.mpr hlt))
      have hb:=min_le_right (epsilon/2) ((right-left)/2)
      dsimp only [z]
      constructor <;> linarith
    have hsmall : ∀ᶠj in atTop,error j<epsilon/2:=herror.eventually (gt_mem_nhds (half_pos hepsilon))
    filter_upwards [hbound,hcover z hz,hsmall] with j hj hc he
    rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hj.2)]
    have hm:=min_le_left (epsilon/2) ((right-left)/2)
    dsimp only [z] at hc
    linarith

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {W : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

def Potential.retainedCapRows (P : W.Potential) {ι : Type*} (c : ι→ShiftedCapInterval W P)
    (Dcuts : Finset ℝ) (ag zg : ℝ) (as : List PositiveMass) (bins : ℕ) (w : ℝ)
    (t : ι) (b : Fin bins) : Finset (Fin ((sampleClockSteps W.shiftedNativeModel.q 0 as).length+1)) :=
  (P.retainedBin c Dcuts ag zg as bins w b).filter
    (fun i=>W.shiftedNativeModel.rowRadius as i∈Ioo (c t).left (c t).right)

def Potential.retainedCapFirst (P : W.Potential) {ι : Type*} (c : ι→ShiftedCapInterval W P)
    (Dcuts : Finset ℝ) (ag zg : ℝ) (as : List PositiveMass) (bins : ℕ) (w : ℝ)
    (t : ι) (b : Fin bins) : Fin ((sampleClockSteps W.shiftedNativeModel.q 0 as).length+1) :=
  let F:=P.retainedCapRows c Dcuts ag zg as bins w t b
  if hF:F.Nonempty then F.min' hF else 0

def Potential.retainedCapLast (P : W.Potential) {ι : Type*} (c : ι→ShiftedCapInterval W P)
    (Dcuts : Finset ℝ) (ag zg : ℝ) (as : List PositiveMass) (bins : ℕ) (w : ℝ)
    (t : ι) (b : Fin bins) : Fin ((sampleClockSteps W.shiftedNativeModel.q 0 as).length+1) :=
  let F:=P.retainedCapRows c Dcuts ag zg as bins w t b
  if hF:F.Nonempty then F.max' hF else 0

theorem Potential.retainedCapFirst_mem (P : W.Potential) {ι : Type*} (c : ι→ShiftedCapInterval W P)
    (Dcuts : Finset ℝ) (ag zg : ℝ) (as : List PositiveMass) (bins : ℕ) (w : ℝ)
    (t : ι) (b : Fin bins) (hn : (P.retainedCapRows c Dcuts ag zg as bins w t b).Nonempty) :
    P.retainedCapFirst c Dcuts ag zg as bins w t b∈P.retainedCapRows c Dcuts ag zg as bins w t b := by
  unfold retainedCapFirst
  rw [dite_eq_left hn]
  exact Finset.min'_mem _ hn

theorem Potential.retainedCapLast_mem (P : W.Potential) {ι : Type*} (c : ι→ShiftedCapInterval W P)
    (Dcuts : Finset ℝ) (ag zg : ℝ) (as : List PositiveMass) (bins : ℕ) (w : ℝ)
    (t : ι) (b : Fin bins) (hn : (P.retainedCapRows c Dcuts ag zg as bins w t b).Nonempty) :
    P.retainedCapLast c Dcuts ag zg as bins w t b∈P.retainedCapRows c Dcuts ag zg as bins w t b := by
  unfold retainedCapLast
  rw [dite_eq_left hn]
  exact Finset.max'_mem _ hn

theorem Potential.retainedCapFirst_le (P : W.Potential) {ι : Type*} (c : ι→ShiftedCapInterval W P)
    (Dcuts : Finset ℝ) (ag zg : ℝ) (as : List PositiveMass) (bins : ℕ) (w : ℝ)
    (t : ι) (b : Fin bins) (i : Fin ((sampleClockSteps W.shiftedNativeModel.q 0 as).length+1))
    (hi:i∈P.retainedCapRows c Dcuts ag zg as bins w t b) :
    P.retainedCapFirst c Dcuts ag zg as bins w t b ≤ i := by
  unfold retainedCapFirst
  rw [dite_eq_left (show (P.retainedCapRows c Dcuts ag zg as bins w t b).Nonempty from ⟨i,hi⟩)]
  exact Finset.min'_le _ i hi

theorem Potential.le_retainedCapLast (P : W.Potential) {ι : Type*} (c : ι→ShiftedCapInterval W P)
    (Dcuts : Finset ℝ) (ag zg : ℝ) (as : List PositiveMass) (bins : ℕ) (w : ℝ)
    (t : ι) (b : Fin bins) (i : Fin ((sampleClockSteps W.shiftedNativeModel.q 0 as).length+1))
    (hi:i∈P.retainedCapRows c Dcuts ag zg as bins w t b) :
    i ≤ P.retainedCapLast c Dcuts ag zg as bins w t b := by
  unfold retainedCapLast
  rw [dite_eq_left (show (P.retainedCapRows c Dcuts ag zg as bins w t b).Nonempty from ⟨i,hi⟩)]
  exact Finset.le_max' _ i hi

theorem Potential.retainedCapRows_cell_eventually (P : W.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval W P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ} (hag : W.data.rmin<ag) (hzg : zg ≤ 1)
    (bins : ℕ) (hbins : 0<bins) (w : ℕ→ℝ)
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (t : ι) (b : Fin bins) (hlabel : ∀j,P.retainedCapLabel c Dcuts ag zg (as j) bins hbins (w j) t=b)
    (hat : ag ≤ (c t).left) (hzt : (c t).right ≤ zg)
    {r : ℝ} (hr : r∈Ioo (c t).left (c t).right) (hrD : r∉Dcuts) :
    let m:=W.shiftedNativeModel
    ∀ᶠj in atTop,∃i : Fin ((sampleClockSteps m.q 0 (as j)).length+1),
      i∈P.retainedCapRows c Dcuts ag zg (as j) bins (w j) t b ∧ i.val<(as j).length ∧
      r∈Ioc (m.R (partitionPoint 0 (as j) i.val)) (m.R (partitionPoint 0 (as j) (i.val+1))) := by
  dsimp only
  let m:=W.shiftedNativeModel
  let p:=fun j i=>m.R (partitionPoint 0 (as j) i)
  obtain ⟨_,_,_,hdiam,ht⟩:=P.retained_grid as mesh ho he hmesh hm0 hlim
  filter_upwards [P.retainedRows_cell_eventually c Dcuts as mesh ho he hmesh hm0 hlim hag hzg
    ⟨hat.trans_lt hr.1,hr.2.trans_le hzt⟩ hrD (Or.inl ⟨t,hr⟩),
    NativeSelectedMask.cells_eventually_subset_open p _ _ hdiam ht
      (Ioo (c t).left (c t).right) isOpen_Ioo hr] with j hj hcj
  obtain ⟨i,hi,hil,hri⟩:=hj
  have hit : m.rowRadius (as j) i∈Ioo (c t).left (c t).right := by
    rw [m.rowRadius_eq_partitionPoint]
    exact hcj i.val hil hri (left_mem_Icc.mpr (hri.1.le.trans hri.2))
  have hib : i∈P.retainedBin c Dcuts ag zg (as j) bins (w j) b := by
    rw [P.retainedBin_cap_label_iff c Dcuts ag zg (as j) bins hbins (w j) hwhole t b i hi hit,hlabel j]
  exact ⟨i,Finset.mem_filter.mpr ⟨hib,hit⟩,hil,hri⟩

theorem Potential.retainedCapRows_eventually_nonempty (P : W.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval W P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ} (hag : W.data.rmin<ag) (hzg : zg ≤ 1)
    (bins : ℕ) (hbins : 0<bins) (w : ℕ→ℝ)
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (t : ι) (b : Fin bins) (hlabel : ∀j,P.retainedCapLabel c Dcuts ag zg (as j) bins hbins (w j) t=b)
    (hat : ag ≤ (c t).left) (hzt : (c t).right ≤ zg)
    (hinterior : ∀d∈Dcuts,d∉Ioo (c t).left (c t).right) :
    ∀ᶠj in atTop,(P.retainedCapRows c Dcuts ag zg (as j) bins (w j) t b).Nonempty := by
  let r:=((c t).left+(c t).right)/2
  have hr : r∈Ioo (c t).left (c t).right:=by
    constructor <;> dsimp only [r] <;> linarith [(c t).hlt]
  filter_upwards [P.retainedCapRows_cell_eventually c Dcuts as mesh ho he hmesh hm0 hlim
    hag hzg bins hbins w hwhole t b hlabel hat hzt hr (fun hd=>hinterior r hd hr)] with j hj
  obtain ⟨i,hi,_,_⟩:=hj
  exact ⟨i,hi⟩

theorem Potential.retainedCap_radius_endpoints_tendsto (P : W.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval W P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ} (hag : W.data.rmin<ag) (hzg : zg ≤ 1)
    (bins : ℕ) (hbins : 0<bins) (w : ℕ→ℝ)
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (t : ι) (b : Fin bins) (hlabel : ∀j,P.retainedCapLabel c Dcuts ag zg (as j) bins hbins (w j) t=b)
    (hat : ag ≤ (c t).left) (hzt : (c t).right ≤ zg)
    (hinterior : ∀d∈Dcuts,d∉Ioo (c t).left (c t).right) :
    let m:=W.shiftedNativeModel
    let p:=fun j=>P.retainedCapFirst c Dcuts ag zg (as j) bins (w j) t b
    let q:=fun j=>P.retainedCapLast c Dcuts ag zg (as j) bins (w j) t b
    Tendsto (fun j=>m.R (partitionPoint 0 (as j) (p j).val)) atTop (𝓝 (c t).left) ∧
    Tendsto (fun j=>m.R (partitionPoint 0 (as j) ((q j).val+1))) atTop (𝓝 (c t).right) := by
  dsimp only
  let m:=W.shiftedNativeModel
  let p:=fun j=>P.retainedCapFirst c Dcuts ag zg (as j) bins (w j) t b
  let q:=fun j=>P.retainedCapLast c Dcuts ag zg (as j) bins (w j) t b
  let low:=fun j=>m.R (partitionPoint 0 (as j) (p j).val)
  let high:=fun j=>m.R (partitionPoint 0 (as j) (q j).val)
  have hn:=P.retainedCapRows_eventually_nonempty c Dcuts as mesh ho he hmesh hm0 hlim
    hag hzg bins hbins w hwhole t b hlabel hat hzt hinterior
  obtain ⟨_,_,_,hdiam,ht⟩:=P.retained_grid as mesh ho he hmesh hm0 hlim
  have hbound : ∀ᶠj in atTop,(c t).left ≤ low j ∧ high j ≤ (c t).right := by
    filter_upwards [hn] with j hj
    have hp:=Finset.mem_filter.mp (P.retainedCapFirst_mem c Dcuts ag zg (as j) bins (w j) t b hj)
    have hq:=Finset.mem_filter.mp (P.retainedCapLast_mem c Dcuts ag zg (as j) bins (w j) t b hj)
    rw [m.rowRadius_eq_partitionPoint] at hp hq
    exact ⟨hp.2.1.le,hq.2.2.le⟩
  have hcover : ∀r∈Ioo (c t).left (c t).right,∀ᶠj in atTop,
      low j ≤ r ∧ r-mesh j/m.c ≤ high j := by
    intro r hr
    filter_upwards [P.retainedCapRows_cell_eventually c Dcuts as mesh ho he hmesh hm0 hlim
      hag hzg bins hbins w hwhole t b hlabel hat hzt hr (fun hd=>hinterior r hd hr)] with j hj
    obtain ⟨i,hi,hil,hri⟩:=hj
    have hp:=m.R_monotone (partitionPoint_mono (as j) (ho j)
      (P.retainedCapFirst_le c Dcuts ag zg (as j) bins (w j) t b i hi))
    have hq:=m.R_monotone (partitionPoint_mono (as j) (ho j)
      (P.le_retainedCapLast c Dcuts ag zg (as j) bins (w j) t b i hi))
    have hd:=hdiam j i.val hil
    exact ⟨hp.trans hri.1.le,by dsimp only [high];linarith [hri.2]⟩
  obtain ⟨hl,hr⟩:=cap_extrema_tendsto (c t).hlt low high _ ht hbound hcover
  refine ⟨hl,?_⟩
  have hdiff : Tendsto (fun j=>m.R (partitionPoint 0 (as j) ((q j).val+1))-high j) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ ht
    · apply Eventually.of_forall
      intro j
      exact sub_nonneg.mpr (m.R_monotone (partitionPoint_mono (as j) (ho j) (Nat.le_succ _)))
    · filter_upwards [hn] with j hj
      have hq:=(Finset.mem_filter.mp (P.retainedCapLast_mem c Dcuts ag zg (as j) bins (w j) t b hj)).1
      have hrow:=(P.retainedRows_mem c Dcuts ag zg (as j) (q j)).mp
        (P.retainedBin_subset c Dcuts ag zg (as j) bins (w j) b hq)
      exact hdiam j (q j).val hrow.1
  simpa only [sub_add_cancel,zero_add] using hdiff.add hr

theorem Potential.retainedCap_unit_geometry (P : W.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval W P) (Dcuts : Finset ℝ) (ag zg : ℝ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (bins : ℕ) (w : ℝ)
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (t : ι) (b : Fin bins) (hn : (P.retainedCapRows c Dcuts ag zg as bins w t b).Nonempty) :
    let J:=P.retainedBin c Dcuts ag zg as bins w b
    let C:=P.retainedBinCoordinates c Dcuts ag zg as ho bins w b
    let p:=P.retainedCapFirst c Dcuts ag zg as bins w t b
    let q:=P.retainedCapLast c Dcuts ag zg as bins w t b
    p∈J ∧ q∈J ∧ C.unit p=C.unit q ∧
      (∀i∈J,C.unit i=C.unit p→p ≤ i) ∧ (∀i∈J,C.unit i=C.unit q→i ≤ q) := by
  dsimp only
  let C:=P.retainedBinCoordinates c Dcuts ag zg as ho bins w b
  let p:=P.retainedCapFirst c Dcuts ag zg as bins w t b
  let q:=P.retainedCapLast c Dcuts ag zg as bins w t b
  have hp:=Finset.mem_filter.mp (P.retainedCapFirst_mem c Dcuts ag zg as bins w t b hn)
  have hq:=Finset.mem_filter.mp (P.retainedCapLast_mem c Dcuts ag zg as bins w t b hn)
  refine ⟨hp.1,hq.1,(C.classes p hp.1 q hq.1).mpr
    ((hwhole t _ hp.2).trans (hwhole t _ hq.2).symm),?_,?_⟩
  · intro i hi hui
    have hU:=(C.classes i hi p hp.1).mp hui
    rw [hwhole t _ hp.2] at hU
    have hit : W.shiftedNativeModel.rowRadius as i∈Ioo (c t).left (c t).right:=
      hU ▸ self_mem_wholeUnit P.negativeSet (W.shiftedNativeModel.rowRadius as i)
    exact P.retainedCapFirst_le c Dcuts ag zg as bins w t b i (Finset.mem_filter.mpr ⟨hi,hit⟩)
  · intro i hi hui
    have hU:=(C.classes i hi q hq.1).mp hui
    rw [hwhole t _ hq.2] at hU
    have hit : W.shiftedNativeModel.rowRadius as i∈Ioo (c t).left (c t).right:=
      hU ▸ self_mem_wholeUnit P.negativeSet (W.shiftedNativeModel.rowRadius as i)
    exact P.le_retainedCapLast c Dcuts ag zg as bins w t b i (Finset.mem_filter.mpr ⟨hi,hit⟩)

theorem Potential.retainedCap_unit_class_iff (P : W.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval W P) (Dcuts : Finset ℝ) (ag zg : ℝ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (bins : ℕ) (w : ℝ)
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (t : ι) (b : Fin bins) (hn : (P.retainedCapRows c Dcuts ag zg as bins w t b).Nonempty)
    (i : Fin ((sampleClockSteps W.shiftedNativeModel.q 0 as).length+1))
    (hi:i∈P.retainedBin c Dcuts ag zg as bins w b) :
    let C:=P.retainedBinCoordinates c Dcuts ag zg as ho bins w b
    C.unit i=C.unit (P.retainedCapFirst c Dcuts ag zg as bins w t b) ↔
      W.shiftedNativeModel.rowRadius as i∈Ioo (c t).left (c t).right := by
  dsimp only
  let C:=P.retainedBinCoordinates c Dcuts ag zg as ho bins w b
  let p:=P.retainedCapFirst c Dcuts ag zg as bins w t b
  have hp:=Finset.mem_filter.mp (P.retainedCapFirst_mem c Dcuts ag zg as bins w t b hn)
  rw [C.classes i hi p hp.1,hwhole t _ hp.2]
  constructor
  · intro h
    exact h ▸ self_mem_wholeUnit P.negativeSet (W.shiftedNativeModel.rowRadius as i)
  · exact hwhole t _

theorem Potential.retainedCap_unit_filter_eq (P : W.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval W P) (Dcuts : Finset ℝ) (ag zg : ℝ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (bins : ℕ) (w : ℝ)
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (t : ι) (b : Fin bins) (hn : (P.retainedCapRows c Dcuts ag zg as bins w t b).Nonempty) :
    let J:=P.retainedBin c Dcuts ag zg as bins w b
    let C:=P.retainedBinCoordinates c Dcuts ag zg as ho bins w b
    J.filter (fun i=>C.unit i=C.unit (P.retainedCapFirst c Dcuts ag zg as bins w t b))=
      P.retainedCapRows c Dcuts ag zg as bins w t b := by
  dsimp only
  ext i
  simp only [retainedCapRows,Finset.mem_filter]
  by_cases hi:i∈P.retainedBin c Dcuts ag zg as bins w b
  · exact and_congr_right (fun _=>P.retainedCap_unit_class_iff c Dcuts ag zg as ho bins w hwhole t b hn i hi)
  · simp only [hi,false_and]

theorem Potential.retainedCap_coordinates_tendsto (P : W.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval W P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ} (hag : W.data.rmin<ag) (hzg : zg ≤ 1)
    (bins : ℕ) (hbins : 0<bins) (w : ℕ→ℝ)
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (t : ι) (b : Fin bins) (hlabel : ∀j,P.retainedCapLabel c Dcuts ag zg (as j) bins hbins (w j) t=b)
    (hat : ag ≤ (c t).left) (hzt : (c t).right ≤ zg)
    (hinterior : ∀d∈Dcuts,d∉Ioo (c t).left (c t).right)
    (f : Icc (0:ℝ) 1→ᵇℝ)
    (huniform : Tendsto (fun j=>W.actualCDF (as j) (ho j)
      (P.retainedBin c Dcuts ag zg (as j) bins (w j) b)) atTop (𝓝 f)) :
    let C:=fun j=>P.retainedBinCoordinates c Dcuts ag zg (as j) (ho j) bins (w j) b
    let p:=fun j=>P.retainedCapFirst c Dcuts ag zg (as j) bins (w j) t b
    Tendsto (fun j=>(C j).x ((C j).unit (p j)).val) atTop
      (𝓝 (f ⟨(c t).left,W.data.hrbounds.1.le.trans (c t).hleft,(c t).hlt.le.trans (c t).hright⟩)) ∧
    Tendsto (fun j=>(C j).x (((C j).unit (p j)).val+1)) atTop
      (𝓝 (f ⟨(c t).right,W.data.hrbounds.1.le.trans ((c t).hleft.trans (c t).hlt.le),(c t).hright⟩)) := by
  dsimp only
  let m:=W.shiftedNativeModel
  let J:=fun j=>P.retainedBin c Dcuts ag zg (as j) bins (w j) b
  let C:=fun j=>P.retainedBinCoordinates c Dcuts ag zg (as j) (ho j) bins (w j) b
  let p:=fun j=>P.retainedCapFirst c Dcuts ag zg (as j) bins (w j) t b
  let q:=fun j=>P.retainedCapLast c Dcuts ag zg (as j) bins (w j) t b
  let low:=fun j=>m.R (partitionPoint 0 (as j) (p j).val)
  let high:=fun j=>m.R (partitionPoint 0 (as j) ((q j).val+1))
  have hlowI j : low j∈Icc (0:ℝ) 1:=
    ⟨W.data.hrbounds.1.le.trans (m.R_bounds _).1,(m.R_bounds _).2⟩
  have hhighI j : high j∈Icc (0:ℝ) 1:=
    ⟨W.data.hrbounds.1.le.trans (m.R_bounds _).1,(m.R_bounds _).2⟩
  have hlI : (c t).left∈Icc (0:ℝ) 1:=
    ⟨W.data.hrbounds.1.le.trans (c t).hleft,(c t).hlt.le.trans (c t).hright⟩
  have hrI : (c t).right∈Icc (0:ℝ) 1:=
    ⟨W.data.hrbounds.1.le.trans ((c t).hleft.trans (c t).hlt.le),(c t).hright⟩
  have hradius:=P.retainedCap_radius_endpoints_tendsto c Dcuts as mesh ho he hmesh hm0 hlim
    hag hzg bins hbins w hwhole t b hlabel hat hzt hinterior
  have hlsub : Tendsto (fun j=>(⟨low j,hlowI j⟩ : Icc (0:ℝ) 1)) atTop (𝓝 ⟨(c t).left,hlI⟩):=
    tendsto_subtype_rng.mpr hradius.1
  have hrsub : Tendsto (fun j=>(⟨high j,hhighI j⟩ : Icc (0:ℝ) 1)) atTop (𝓝 ⟨(c t).right,hrI⟩):=
    tendsto_subtype_rng.mpr hradius.2
  have hleval:=selectedCumulative_uniform_moving_eval_tendsto _ f huniform _ ⟨(c t).left,hlI⟩ hlsub
  have hreval:=selectedCumulative_uniform_moving_eval_tendsto _ f huniform _ ⟨(c t).right,hrI⟩ hrsub
  have hn:=P.retainedCapRows_eventually_nonempty c Dcuts as mesh ho he hmesh hm0 hlim
    hag hzg bins hbins w hwhole t b hlabel hat hzt hinterior
  have hhigh : ∀j,∀i∈J j,m.u0 ≤ partitionPoint 0 (as j) i.val := by
    intro j i hi
    exact ((P.retainedRows_mem c Dcuts ag zg (as j) i).mp
      (P.retainedBin_subset c Dcuts ag zg (as j) bins (w j) b hi)).2.2.2.1
  constructor
  · apply hleval.congr'
    filter_upwards [hn] with j hj
    have hg:=P.retainedCap_unit_geometry c Dcuts ag zg (as j) (ho j) bins (w j) hwhole t b hj
    change cumulativeCellMass (m.selectedMassDensity (as j) (J j)) (low j)=
      (C j).x ((C j).unit (p j)).val
    exact (m.selected_first_coordinate_eq_cumulative W.data.hrbounds.1.le (as j) (ho j)
      (he j) (J j) (hhigh j) (C j).unit (C j).x (C j).start (C j).mass (C j).order
      (p j) hg.1 hg.2.2.2.1).symm
  · apply hreval.congr'
    filter_upwards [hn] with j hj
    have hg:=P.retainedCap_unit_geometry c Dcuts ag zg (as j) (ho j) bins (w j) hwhole t b hj
    change cumulativeCellMass (m.selectedMassDensity (as j) (J j)) (high j)=
      (C j).x (((C j).unit (p j)).val+1)
    have hh:=(m.selected_last_coordinate_eq_cumulative W.data.hrbounds.1.le (as j) (ho j)
      (he j) (J j) (hhigh j) (C j).unit (C j).x (C j).start (C j).mass (C j).order
      (q j) hg.2.1 hg.2.2.2.2).symm
    have hu : (C j).unit (p j)=(C j).unit (q j):=hg.2.2.1
    change cumulativeCellMass (m.selectedMassDensity (as j) (J j)) (high j)=
      (C j).x (((C j).unit (q j)).val+1) at hh
    rw [←hu] at hh
    exact hh

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
