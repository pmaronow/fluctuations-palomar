module

public import ComparisonActualHighWallThetaZeroSelectedCapEndpoints
public import ComparisonActualHighWallThetaZeroSelectedCapLabelsPositiveOrigin
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
private theorem cap_extrema_tendsto_positive_origin {left right : ℝ} (hlt : left<right)
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

theorem Potential.retainedCapRows_cell_eventually_positive_origin (P : W.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval W P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ} (hag : W.data.rmin≤ag) (hzg : zg ≤ 1)
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
  filter_upwards [P.retainedRows_cell_eventually_positive_origin c Dcuts as mesh ho he hmesh hm0 hlim hag hzg
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

theorem Potential.retainedCapRows_eventually_nonempty_positive_origin (P : W.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval W P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ} (hag : W.data.rmin≤ag) (hzg : zg ≤ 1)
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
  filter_upwards [P.retainedCapRows_cell_eventually_positive_origin c Dcuts as mesh ho he hmesh hm0 hlim
    hag hzg bins hbins w hwhole t b hlabel hat hzt hr (fun hd=>hinterior r hd hr)] with j hj
  obtain ⟨i,hi,_,_⟩:=hj
  exact ⟨i,hi⟩

theorem Potential.retainedCap_radius_endpoints_tendsto_positive_origin (P : W.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval W P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ} (hag : W.data.rmin≤ag) (hzg : zg ≤ 1)
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
  have hn:=P.retainedCapRows_eventually_nonempty_positive_origin c Dcuts as mesh ho he hmesh hm0 hlim
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
    filter_upwards [P.retainedCapRows_cell_eventually_positive_origin c Dcuts as mesh ho he hmesh hm0 hlim
      hag hzg bins hbins w hwhole t b hlabel hat hzt hr (fun hd=>hinterior r hd hr)] with j hj
    obtain ⟨i,hi,hil,hri⟩:=hj
    have hp:=m.R_monotone (partitionPoint_mono (as j) (ho j)
      (P.retainedCapFirst_le c Dcuts ag zg (as j) bins (w j) t b i hi))
    have hq:=m.R_monotone (partitionPoint_mono (as j) (ho j)
      (P.le_retainedCapLast c Dcuts ag zg (as j) bins (w j) t b i hi))
    have hd:=hdiam j i.val hil
    exact ⟨hp.trans hri.1.le,by dsimp only [high];linarith [hri.2]⟩
  obtain ⟨hl,hr⟩:=cap_extrema_tendsto_positive_origin (c t).hlt low high _ ht hbound hcover
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

theorem Potential.retainedCap_coordinates_tendsto_positive_origin (P : W.Potential) {ι : Type*}
    (c : ι→ShiftedCapInterval W P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ} (hag : W.data.rmin≤ag) (hzg : zg ≤ 1)
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
  have hradius:=P.retainedCap_radius_endpoints_tendsto_positive_origin c Dcuts as mesh ho he hmesh hm0 hlim
    hag hzg bins hbins w hwhole t b hlabel hat hzt hinterior
  have hlsub : Tendsto (fun j=>(⟨low j,hlowI j⟩ : Icc (0:ℝ) 1)) atTop (𝓝 ⟨(c t).left,hlI⟩):=
    tendsto_subtype_rng.mpr hradius.1
  have hrsub : Tendsto (fun j=>(⟨high j,hhighI j⟩ : Icc (0:ℝ) 1)) atTop (𝓝 ⟨(c t).right,hrI⟩):=
    tendsto_subtype_rng.mpr hradius.2
  have hleval:=selectedCumulative_uniform_moving_eval_tendsto _ f huniform _ ⟨(c t).left,hlI⟩ hlsub
  have hreval:=selectedCumulative_uniform_moving_eval_tendsto _ f huniform _ ⟨(c t).right,hrI⟩ hrsub
  have hn:=P.retainedCapRows_eventually_nonempty_positive_origin c Dcuts as mesh ho he hmesh hm0 hlim
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
