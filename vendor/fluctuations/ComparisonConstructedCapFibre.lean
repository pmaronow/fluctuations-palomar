module

public import ComparisonNativeConstructedRows

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2600000
attribute [local instance] Classical.propDecidable

theorem canonical_original_cell_right_le {ι : Type}
    (q : ℝ→ι→ℝ≥0) (D : Finset ℝ) (hD : ∀d∈D,d∈Icc (0:ℝ) 1) (m : ℕ)
    {b : ℝ} (hb : b∈D) :
    let as := finiteCutMasses (finiteBoundaryMassNodes D) m
    let steps := sampleClockSteps q 0 as
    ∀i : Fin (steps.length+1),physicalCutMass 0 steps i.val<b →
      physicalCutMass 0 steps (i.val+1)≤b := by
  dsimp only
  let as := finiteCutMasses (finiteBoundaryMassNodes D) m
  let steps := sampleClockSteps q 0 as
  have ho := sampleClockSteps_ordered q as
    (finiteCutMasses_ordered _ (finiteBoundaryMassNodes_bound D (fun d hd=>(hD d hd).2)) m)
  have hend := finiteBoundaryMassIndex_exact q D hD m hb
  change physicalCutMass 0 steps (finiteBoundaryMassIndex b as)=b at hend
  intro i hi
  have hidx : i.val<finiteBoundaryMassIndex b as := by
    by_contra hno
    have hh := physicalCutMass_monotone steps ho (Nat.le_of_not_gt hno)
    rw [hend] at hh
    exact hi.not_ge hh
  have hh := physicalCutMass_monotone steps ho (show i.val+1≤finiteBoundaryMassIndex b as by omega)
  exact hh.trans_eq hend

theorem canonical_retained_cap_left_filter {ι : Type}
    (q : ℝ→ι→ℝ≥0) (D : Finset ℝ) (hD : ∀d∈D,d∈Icc (0:ℝ) 1) (m : ℕ)
    {a b : ℝ} (ha : a∈D) (hb : b∈D) (hab : a<b)
    (hinterior : ∀d∈D,d∉Ioo a b) :
    let as := finiteCutMasses (finiteBoundaryMassNodes D) m
    let steps := sampleClockSteps q 0 as
    (Finset.univ.filter (fun i : Fin (steps.length+1)=>
      0<pathMassDifferences steps 0 i ∧ physicalCutMass 0 steps i.val∈Ioo a b))=
      (completeMassCapCells steps a b).erase (finiteBoundaryClockCell q as a) := by
  dsimp only
  let as := finiteCutMasses (finiteBoundaryMassNodes D) m
  let steps := sampleClockSteps q 0 as
  rw [←finiteBoundaryRows_complete_cap_sdiff q D hD m ha hb hab hinterior]
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]
  constructor
  · rintro ⟨hp,hi⟩
    have hright := canonical_original_cell_right_le q D hD m hb i hi.2
    have hmid := physicalCellMassMidpoint_strict_inside steps i hp
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp,hi.1.trans hmid.1,hmid.2.trans_le hright⟩,?_⟩
    intro hrow
    obtain ⟨d,hd,hdi⟩ := Finset.mem_image.mp hrow
    have he := finiteBoundaryMassIndex_exact q D hD m hd
    change physicalCutMass 0 steps (finiteBoundaryClockCell q as d).val=d at he
    rw [hdi] at he
    exact hinterior d hd (he ▸ hi)
  · rintro ⟨hi,hrow⟩
    have hp := (Finset.mem_filter.mp hi).2.1
    exact ⟨hp,completeMassCapCells_sdiff_left_cut_mem q D hD m ha hb i
      (Finset.mem_sdiff.mpr ⟨hi,hrow⟩)⟩

theorem firstWholeUnitCell_cap_iff {N : ℕ} (U : Set ℝ) (r : Fin N→ℝ)
    {a b : ℝ} (hcap : ∀s∈Ioo a b,wholeUnit U s=Ioo a b)
    {anchor : Fin N} (ha : r anchor∈Ioo a b) (i : Fin N) :
    firstWholeUnitCell U r i=firstWholeUnitCell U r anchor ↔ r i∈Ioo a b := by
  rw [firstWholeUnitCell_eq_iff]
  constructor
  · intro he
    have hm := self_mem_wholeUnit U (r i)
    rw [he,hcap _ ha] at hm
    exact hm
  · intro hi
    rw [hcap _ hi,hcap _ ha]

theorem firstWholeUnitCell_cap_filter {N : ℕ} (U : Set ℝ) (r : Fin N→ℝ)
    (J : Finset (Fin N)) {a b : ℝ} (hcap : ∀s∈Ioo a b,wholeUnit U s=Ioo a b)
    {anchor : Fin N} (ha : r anchor∈Ioo a b) :
    J.filter (fun i=>firstWholeUnitCell U r i=firstWholeUnitCell U r anchor)=
      J.filter (fun i=>r i∈Ioo a b) := by
  ext i
  simp only [Finset.mem_filter,firstWholeUnitCell_cap_iff U r hcap ha]

theorem native_bin_label_fibre {N K bins : ℕ} (S : Fin N→ℝ) (J : Finset (Fin N))
    (unit : Fin N→Fin K) (w : ℝ) (b : Fin bins) (u : Fin K)
    (hlabel : heightBin bins w (NativeUnitHeight.height S J unit u)=b.val) :
    (NativeUnitHeight.bin S J unit bins w b).filter (fun i=>unit i=u)=J.filter (fun i=>unit i=u) := by
  ext i
  simp only [NativeUnitHeight.bin,Finset.mem_filter]
  constructor
  · rintro ⟨⟨hi,_⟩,hu⟩
    exact ⟨hi,hu⟩
  · rintro ⟨hi,hu⟩
    exact ⟨⟨hi,by rw [hu];exact hlabel⟩,hu⟩

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparisonConstructedRows_cap_fibre {ι : Type} {τ : Type*}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (a z : τ→ℝ) (H : ℝ→ℝ) (D : Finset ℝ) (ag zg : ℝ) (m : ℕ) (t : τ)
    (hD : ∀d∈D,d∈Icc (0:ℝ) 1) (ha : a t∈D) (hz : z t∈D) (haz : a t<z t)
    (hinterior : ∀d∈D,d∉Ioo (a t) (z t)) (hag : ag≤a t) (hzg : z t≤zg) :
    let Dm := D.image α.val.val
    let as := finiteCutMasses (finiteBoundaryMassNodes Dm) m
    let steps := sampleClockSteps q 0 as
    (comparisonConstructedRows hc hk hkc hm hM q α as a z H D ag zg).filter
      (fun i=>comparisonConstructedRowRadius hc hk hkc hm hM q α as i∈Ioo (a t) (z t))=
      (completeMassCapCells steps (α.val.val (a t)) (α.val.val (z t))).erase
        (finiteBoundaryClockCell q as (α.val.val (a t))) := by
  dsimp only
  let Dm := D.image α.val.val
  let as := finiteCutMasses (finiteBoundaryMassNodes Dm) m
  let steps := sampleClockSteps q 0 as
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  have hDa := hD _ ha
  have hDz := hD _ hz
  have hDm : ∀d∈Dm,d∈Icc (0:ℝ) 1 := by
    intro d hd
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hd
    exact α.val.property.1 r
  have haM : α.val.val (a t)∈Dm := Finset.mem_image.mpr ⟨a t,ha,rfl⟩
  have hzM : α.val.val (z t)∈Dm := Finset.mem_image.mpr ⟨z t,hz,rfl⟩
  have hαaz := inverseConstraint_strictMonoOn hc hk hkc α.property hDa hDz haz
  have hpre := comparisonSweepQuantile_preimage_open_interval hc hk hkc hm hM α hDa hDz
  have hDmInterior : ∀d∈Dm,d∉Ioo (α.val.val (a t)) (α.val.val (z t)) := by
    intro d hd hinside
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hd
    have hR : R (α.val.val r)∈Ioo (a t) (z t) := by
      change α.val.val r∈R⁻¹' Ioo (a t) (z t)
      rw [hpre]
      exact hinside
    dsimp only [R] at hR
    rw [comparisonSweepQuantile_inverse hc hk hkc hm hM α (hD r hr)] at hR
    exact hinterior r hr hR
  rw [←canonical_retained_cap_left_filter q Dm hDm m haM hzM hαaz hDmInterior]
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have hcut := physicalCutMass_sampleClockSteps q 0 as i.val
    (show i.val≤as.length by simpa only [sampleClockSteps_length] using Nat.le_of_lt_succ i.isLt)
  have hleft : comparisonConstructedRowRadius hc hk hkc hm hM q α as i∈Ioo (a t) (z t) ↔
      physicalCutMass 0 steps i.val∈Ioo (α.val.val (a t)) (α.val.val (z t)) := by
    change physicalCutMass 0 steps i.val∈R⁻¹' Ioo (a t) (z t) ↔ _
    rw [hpre]
  constructor
  · rintro ⟨hi,hr⟩
    exact ⟨(Finset.mem_filter.mp hi).2.1,hleft.mp hr⟩
  · rintro ⟨hp,hi⟩
    have hri := hleft.mpr hi
    have hrightM := canonical_original_cell_right_le q Dm hDm m hzM i hi.2
    have hright : R (partitionPoint 0 as (i.val+1))≤z t := by
      have hh := (comparisonSweepQuantile_monotone hc hk hkc hm hM α) hrightM
      rw [comparisonSweepQuantile_inverse hc hk hkc hm hM α hDz] at hh
      have hiLe : i.val+1≤as.length := by
        have hiL : i.val≤as.length := by simpa only [sampleClockSteps_length] using Nat.le_of_lt_succ i.isLt
        by_contra hno
        have hie : i.val=as.length := by omega
        have hc := physicalCutMass_sampleClockSteps q 0 as i.val hiL
        rw [hie,partitionPoint_length,finiteCutMasses_end _
          (finiteBoundaryMassNodes_bound Dm (fun d hd=>(hDm d hd).2)) m] at hc
        have hb1 := (α.val.property.1 (z t)).2
        rw [hie,hc] at hi
        linarith [hi.2]
      rw [physicalCutMass_sampleClockSteps q 0 as (i.val+1) hiLe] at hh
      exact hh
    have hil : i.val<as.length := by
      have hiL : i.val≤as.length := by simpa only [sampleClockSteps_length] using Nat.le_of_lt_succ i.isLt
      by_contra hno
      have hie : i.val=as.length := by omega
      rw [hcut,hie,partitionPoint_length,finiteCutMasses_end _
        (finiteBoundaryMassNodes_bound Dm (fun d hd=>(hDm d hd).2)) m] at hi
      linarith [(α.val.property.1 (z t)).2,hi.2]
    have hrpoint : R (partitionPoint 0 as i.val)∈Ioo (a t) (z t) := by
      simpa only [comparisonConstructedRowRadius_eq] using hri
    refine ⟨Finset.mem_filter.mpr ⟨?_,hp,hag.trans hrpoint.1.le,hright.trans hzg⟩,hri⟩
    apply (comparisonNativeSelectedRows_mem hc hk hkc hm hM q α as a z H D i).mpr
    refine ⟨hil,?_,Or.inl ⟨t,hrpoint,hright⟩⟩
    intro d hd heq
    exact hinterior d hd (heq ▸ hrpoint)

theorem comparisonConstructedBin_cap_fibre {τ : Type*}
    (n bins : ℕ) (q : ℝ→FeatureIndex n→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (a z : τ→ℝ) (H : ℝ→ℝ) (D : Finset ℝ) (ag zg w : ℝ) (U : Set ℝ)
    (m : ℕ) (t : τ) (b : Fin bins)
    (hD : ∀d∈D,d∈Icc (0:ℝ) 1) (ha : a t∈D) (hz : z t∈D) (haz : a t<z t)
    (hinterior : ∀d∈D,d∉Ioo (a t) (z t)) (hag : ag≤a t) (hzg : z t≤zg)
    (hcap : ∀r∈Ioo (a t) (z t),wholeUnit U r=Ioo (a t) (z t)) :
    let Dm := D.image α.val.val
    let as := finiteCutMasses (finiteBoundaryMassNodes Dm) m
    let steps := sampleClockSteps q 0 as
    let J := comparisonConstructedRows hc hk hkc hm hM q α as a z H D ag zg
    let r := comparisonConstructedRowRadius hc hk hkc hm hM q α as
    let unit := firstWholeUnitCell U r
    ∀anchor : Fin (steps.length+1),r anchor∈Ioo (a t) (z t) →
      heightBin bins w (NativeUnitHeight.height
        (fun i=>physicalPathSecondMoment n steps (q 0) i.val) J unit (unit anchor))=b.val →
      (comparisonConstructedBin hc hk hkc hm hM n bins q α as a z H D ag zg w U b).filter
        (fun i=>unit i=unit anchor)=
      (completeMassCapCells steps (α.val.val (a t)) (α.val.val (z t))).erase
        (finiteBoundaryClockCell q as (α.val.val (a t))) := by
  dsimp only
  intro anchor hanchor hlabel
  unfold comparisonConstructedBin
  rw [native_bin_label_fibre _ _ _ w b _ hlabel,
    firstWholeUnitCell_cap_filter U _ _ hcap hanchor]
  exact comparisonConstructedRows_cap_fibre hc hk hkc hm hM q α a z H D ag zg m t
    hD ha hz haz hinterior hag hzg

end
end OAI.SKFluctuations.LaplaceWindowFormalization
