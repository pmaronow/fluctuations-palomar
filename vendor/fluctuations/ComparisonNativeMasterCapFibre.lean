module

public import ComparisonConstructedCapFibre

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 12000000
attribute [local instance] Classical.propDecidable
theorem masterBoundaryMassIndex_exact {ι : Type} (clock : ℝ → ι → ℝ≥0)
    (D : Finset ℝ) (hD : ∀d∈D,d∈Icc (0:ℝ) 1)
    (us : List PositiveMass) (hnodes : ∀u∈us,u.val ≤ 1)
    (hretain : ∀d∈D,∀hp : 0<d,(⟨d,hp⟩ : PositiveMass)∈us) (m : ℕ) {d : ℝ} (hd : d∈D) :
    let as := finiteCutMasses us m
    physicalCutMass 0 (sampleClockSteps clock 0 as) (finiteBoundaryMassIndex d as)=d := by
  dsimp only
  by_cases hz : d=0
  · simp [finiteBoundaryMassIndex,hz,physicalCutMass]
  · have hp : 0<d := lt_of_le_of_ne (hD d hd).1 (Ne.symm hz)
    have hnode := finiteCutMasses_nodes us m (hretain d hd hp)
    simpa only [finiteBoundaryMassIndex,hz,ite_false] using
      physicalCutMass_retained_prefix clock _ (finiteCutMasses_ordered _ hnodes m) ⟨d,hp⟩ hnode

theorem masterBoundaryMass_cap_erase_initial_mass {ι : Type} (clock : ℝ → ι → ℝ≥0)
    (D : Finset ℝ) (hD:∀d∈D,d∈Icc (0:ℝ) 1)
    (us : List PositiveMass) (hnodes : ∀u∈us,u.val ≤ 1)
    (hretain : ∀d∈D,∀hp : 0<d,(⟨d,hp⟩ : PositiveMass)∈us) (m : ℕ)
    {a b : ℝ} (ha:a∈D) (hb:b∈D) (hab:a<b) :
    let as := finiteCutMasses us m
    let steps := sampleClockSteps clock 0 as
    physicalWindowMass steps 0 ((completeMassCapCells steps a b).erase (finiteBoundaryClockCell clock as a))=
      (b-a)-pathMassDifferences steps 0 (finiteBoundaryClockCell clock as a) := by
  dsimp only
  let as := finiteCutMasses us m
  let steps := sampleClockSteps clock 0 as
  let p := finiteBoundaryClockCell clock as a
  let q := finiteBoundaryMassIndex b as
  have ho : OrderedSteps 0 steps := sampleClockSteps_ordered clock as
    (finiteCutMasses_ordered _ hnodes m)
  have hea := masterBoundaryMassIndex_exact clock D hD us hnodes hretain m ha
  have heb := masterBoundaryMassIndex_exact clock D hD us hnodes hretain m hb
  change physicalCutMass 0 steps p.val=a at hea
  change physicalCutMass 0 steps q=b at heb
  have hpq:p.val<q := by
    by_contra hno
    have hh := physicalCutMass_monotone steps ho (le_of_not_gt hno)
    rw [hea,heb] at hh
    exact hab.not_ge hh
  have hq:q ≤ steps.length+1 := by
    change finiteBoundaryMassIndex b as ≤ (sampleClockSteps clock 0 as).length+1
    unfold finiteBoundaryMassIndex
    split_ifs
    · omega
    · rw [sampleClockSteps_length]
      exact (retainedMassPrefixIndex_le_length b as).trans (Nat.le_succ _)
  have hh := completeMassCapCells_erase_initial_mass steps ho p hpq hq
  simpa only [hea,heb] using hh

theorem masterBoundaryRows_complete_cap_sdiff {ι : Type} (clock : ℝ → ι → ℝ≥0)
    (D : Finset ℝ) (hD:∀d∈D,d∈Icc (0:ℝ) 1)
    (us : List PositiveMass) (hnodes : ∀u∈us,u.val ≤ 1)
    (hretain : ∀d∈D,∀hp : 0<d,(⟨d,hp⟩ : PositiveMass)∈us) (m : ℕ)
    {a b : ℝ} (ha:a∈D) (hb:b∈D) (hab:a<b)
    (hinterior:∀d∈D,d∉Ioo a b) :
    let as := finiteCutMasses us m
    let steps := sampleClockSteps clock 0 as
    (completeMassCapCells steps a b)\fixedEndpointRows clock as D=
      (completeMassCapCells steps a b).erase (finiteBoundaryClockCell clock as a) := by
  dsimp only
  let as := finiteCutMasses us m
  let steps := sampleClockSteps clock 0 as
  have ho : OrderedSteps 0 steps := sampleClockSteps_ordered clock as
    (finiteCutMasses_ordered _ hnodes m)
  have hcell (d : ℝ) (hd:d∈D) : physicalCutMass 0 steps (finiteBoundaryClockCell clock as d).val=d :=
    masterBoundaryMassIndex_exact clock D hD us hnodes hretain m hd
  have hiff (i : Fin (steps.length+1)) (hi:i∈completeMassCapCells steps a b) :
      i∈fixedEndpointRows clock as D ↔ i=finiteBoundaryClockCell clock as a := by
    constructor
    · intro hrow
      obtain ⟨d,hd,hdi⟩ := Finset.mem_image.mp hrow
      have hip : 0 < pathMassDifferences steps 0 i := (Finset.mem_filter.mp hi).2.1
      have him : physicalCellMassMidpoint steps i∈Ioo a b := (Finset.mem_filter.mp hi).2.2
      have hindices : (finiteBoundaryClockCell clock as a).val ≤ i.val ∧
          i.val < (finiteBoundaryClockCell clock as b).val := by
        rw [←hcell a ha,←hcell b hb] at him
        exact (physicalCellMassMidpoint_mem_iff_interval steps ho _ _ i hip).mp him
      have had : a ≤ d := by
        have hh := physicalCutMass_monotone steps ho hindices.1
        rw [hcell a ha,←hdi,hcell d hd] at hh
        exact hh
      have hdb : d ≤ b := by
        have hh := physicalCutMass_monotone steps ho hindices.2.le
        rw [hcell b hb,←hdi,hcell d hd] at hh
        exact hh
      have hne : d≠b := by
        intro he
        rw [he] at hdi
        rw [←hdi] at hindices
        exact lt_irrefl _ hindices.2
      have hlt : d<b := lt_of_le_of_ne hdb hne
      have he : d=a := by
        by_contra hno
        exact hinterior d hd ⟨lt_of_le_of_ne had (Ne.symm hno),hlt⟩
      simpa only [he] using hdi.symm
    · intro he
      exact Finset.mem_image.mpr ⟨a,ha,he.symm⟩
  ext i
  simp only [Finset.mem_sdiff,Finset.mem_erase]
  change (i∈completeMassCapCells steps a b ∧ i∉fixedEndpointRows clock as D) ↔
    i≠finiteBoundaryClockCell clock as a ∧ i∈completeMassCapCells steps a b
  by_cases hi:i∈completeMassCapCells steps a b
  · simp only [hi,true_and,and_true,hiff i hi]
  · simp [hi]

 
theorem masterCompleteMassCapCells_sdiff_left_cut_mem {ι : Type}
    (clock : ℝ → ι → ℝ≥0) (D:Finset ℝ) (hD:∀d∈D,d∈Icc (0:ℝ) 1)
    (us : List PositiveMass) (hnodes : ∀u∈us,u.val ≤ 1)
    (hretain : ∀d∈D,∀hp : 0<d,(⟨d,hp⟩ : PositiveMass)∈us)
    (m:ℕ) {a b:ℝ} (ha:a∈D) (hb:b∈D)
    (i:Fin ((sampleClockSteps clock 0 (finiteCutMasses us m)).length+1))
    (hi:i∈(completeMassCapCells (sampleClockSteps clock 0 (finiteCutMasses us m)) a b)\
      fixedEndpointRows clock (finiteCutMasses us m) D) :
    physicalCutMass 0 (sampleClockSteps clock 0 (finiteCutMasses us m)) i.val∈Ioo a b := by
  let as:=finiteCutMasses us m
  let steps:=sampleClockSteps clock 0 as
  have ho:MassOrdered 0 as := finiteCutMasses_ordered _
    hnodes m
  have hs:OrderedSteps 0 steps:=sampleClockSteps_ordered clock as ho
  obtain ⟨hi,hB⟩:=Finset.mem_sdiff.mp hi
  obtain ⟨hp,hm⟩:0 < pathMassDifferences steps 0 i ∧ physicalCellMassMidpoint steps i∈Ioo a b := by
    simpa only [completeMassCapCells,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  have hlow:=masterBoundaryMassIndex_exact clock D hD us hnodes hretain m ha
  have hhigh:=masterBoundaryMassIndex_exact clock D hD us hnodes hretain m hb
  change physicalCutMass 0 steps (finiteBoundaryMassIndex a as)=a at hlow
  change physicalCutMass 0 steps (finiteBoundaryMassIndex b as)=b at hhigh
  have hloidx:=((physicalCellMassMidpoint_mem_iff_interval steps hs
    (finiteBoundaryMassIndex a as) (finiteBoundaryMassIndex b as) i hp).mp
      (by simpa only [hlow,hhigh] using hm)).1
  have hleft:a ≤ physicalCutMass 0 steps i.val := by
    rw [←hlow]
    exact physicalCutMass_monotone steps hs hloidx
  have hstrict:a<physicalCutMass 0 steps i.val := lt_of_le_of_ne hleft (by
    intro he
    have hc:=finiteBoundaryClockCell_eq_of_positive_left_cut clock as ho i hp
    rw [←he] at hc
    exact hB (Finset.mem_image.mpr ⟨a,ha,hc⟩))
  exact ⟨hstrict,(physicalCellMassMidpoint_strict_inside steps i hp).1.trans hm.2⟩

theorem master_original_cell_right_le {ι : Type}
    (q : ℝ→ι→ℝ≥0) (D : Finset ℝ) (hD : ∀d∈D,d∈Icc (0:ℝ) 1)
    (us : List PositiveMass) (hnodes : ∀u∈us,u.val ≤ 1)
    (hretain : ∀d∈D,∀hp : 0<d,(⟨d,hp⟩ : PositiveMass)∈us) (m : ℕ)
    {b : ℝ} (hb : b∈D) :
    let as := finiteCutMasses us m
    let steps := sampleClockSteps q 0 as
    ∀i : Fin (steps.length+1),physicalCutMass 0 steps i.val<b →
      physicalCutMass 0 steps (i.val+1)≤b := by
  dsimp only
  let as := finiteCutMasses us m
  let steps := sampleClockSteps q 0 as
  have ho := sampleClockSteps_ordered q as
    (finiteCutMasses_ordered _ hnodes m)
  have hend := masterBoundaryMassIndex_exact q D hD us hnodes hretain m hb
  change physicalCutMass 0 steps (finiteBoundaryMassIndex b as)=b at hend
  intro i hi
  have hidx : i.val<finiteBoundaryMassIndex b as := by
    by_contra hno
    have hh := physicalCutMass_monotone steps ho (Nat.le_of_not_gt hno)
    rw [hend] at hh
    exact hi.not_ge hh
  have hh := physicalCutMass_monotone steps ho (show i.val+1≤finiteBoundaryMassIndex b as by omega)
  exact hh.trans_eq hend

theorem master_retained_cap_left_filter {ι : Type}
    (q : ℝ→ι→ℝ≥0) (D : Finset ℝ) (hD : ∀d∈D,d∈Icc (0:ℝ) 1)
    (us : List PositiveMass) (hnodes : ∀u∈us,u.val ≤ 1)
    (hretain : ∀d∈D,∀hp : 0<d,(⟨d,hp⟩ : PositiveMass)∈us) (m : ℕ)
    {a b : ℝ} (ha : a∈D) (hb : b∈D) (hab : a<b)
    (hinterior : ∀d∈D,d∉Ioo a b) :
    let as := finiteCutMasses us m
    let steps := sampleClockSteps q 0 as
    (Finset.univ.filter (fun i : Fin (steps.length+1)=>
      0<pathMassDifferences steps 0 i ∧ physicalCutMass 0 steps i.val∈Ioo a b))=
      (completeMassCapCells steps a b).erase (finiteBoundaryClockCell q as a) := by
  dsimp only
  let as := finiteCutMasses us m
  let steps := sampleClockSteps q 0 as
  rw [←masterBoundaryRows_complete_cap_sdiff q D hD us hnodes hretain m ha hb hab hinterior]
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_sdiff]
  constructor
  · rintro ⟨hp,hi⟩
    have hright := master_original_cell_right_le q D hD us hnodes hretain m hb i hi.2
    have hmid := physicalCellMassMidpoint_strict_inside steps i hp
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp,hi.1.trans hmid.1,hmid.2.trans_le hright⟩,?_⟩
    intro hrow
    obtain ⟨d,hd,hdi⟩ := Finset.mem_image.mp hrow
    have he := masterBoundaryMassIndex_exact q D hD us hnodes hretain m hd
    change physicalCutMass 0 steps (finiteBoundaryClockCell q as d).val=d at he
    rw [hdi] at he
    exact hinterior d hd (he ▸ hi)
  · rintro ⟨hi,hrow⟩
    have hp := (Finset.mem_filter.mp hi).2.1
    exact ⟨hp,masterCompleteMassCapCells_sdiff_left_cut_mem q D hD us hnodes hretain m ha hb i
      (Finset.mem_sdiff.mpr ⟨hi,hrow⟩)⟩

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
theorem comparisonConstructedRows_cap_fibre_master {ι : Type} {τ : Type*}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (a z : τ→ℝ) (H : ℝ→ℝ) (D : Finset ℝ)
    (us : List PositiveMass) (hnodes : ∀u∈us,u.val ≤ 1)
    (hretain : ∀d∈D,∀hp : 0<α.val.val d,(⟨α.val.val d,hp⟩ : PositiveMass)∈us) (ag zg : ℝ) (m : ℕ) (t : τ)
    (hD : ∀d∈D,d∈Icc (0:ℝ) 1) (ha : a t∈D) (hz : z t∈D) (haz : a t<z t)
    (hinterior : ∀d∈D,d∉Ioo (a t) (z t)) (hag : ag≤a t) (hzg : z t≤zg) :
    let Dm := D.image α.val.val
    let as := finiteCutMasses us m
    let steps := sampleClockSteps q 0 as
    (comparisonConstructedRows hc hk hkc hm hM q α as a z H D ag zg).filter
      (fun i=>comparisonConstructedRowRadius hc hk hkc hm hM q α as i∈Ioo (a t) (z t))=
      (completeMassCapCells steps (α.val.val (a t)) (α.val.val (z t))).erase
        (finiteBoundaryClockCell q as (α.val.val (a t))) := by
  dsimp only
  let Dm := D.image α.val.val
  let as := finiteCutMasses us m
  let steps := sampleClockSteps q 0 as
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  have hDa := hD _ ha
  have hDz := hD _ hz
  have hDm : ∀d∈Dm,d∈Icc (0:ℝ) 1 := by
    intro d hd
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hd
    exact α.val.property.1 r
  have hDmRetain : ∀d∈Dm,∀hp : 0<d,(⟨d,hp⟩ : PositiveMass)∈us := by
    intro d hd hp
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hd
    exact hretain r hr hp
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
  rw [←master_retained_cap_left_filter q Dm hDm us hnodes hDmRetain m haM hzM hαaz hDmInterior]
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
    have hrightM := master_original_cell_right_le q Dm hDm us hnodes hDmRetain m hzM i hi.2
    have hright : R (partitionPoint 0 as (i.val+1))≤z t := by
      have hh := (comparisonSweepQuantile_monotone hc hk hkc hm hM α) hrightM
      rw [comparisonSweepQuantile_inverse hc hk hkc hm hM α hDz] at hh
      have hiLe : i.val+1≤as.length := by
        have hiL : i.val≤as.length := by simpa only [sampleClockSteps_length] using Nat.le_of_lt_succ i.isLt
        by_contra hno
        have hie : i.val=as.length := by omega
        have hc := physicalCutMass_sampleClockSteps q 0 as i.val hiL
        rw [hie,partitionPoint_length,finiteCutMasses_end _
          hnodes m] at hc
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
        hnodes m] at hi
      linarith [(α.val.property.1 (z t)).2,hi.2]
    have hrpoint : R (partitionPoint 0 as i.val)∈Ioo (a t) (z t) := by
      simpa only [comparisonConstructedRowRadius_eq] using hri
    refine ⟨Finset.mem_filter.mpr ⟨?_,hp,hag.trans hrpoint.1.le,hright.trans hzg⟩,hri⟩
    apply (comparisonNativeSelectedRows_mem hc hk hkc hm hM q α as a z H D i).mpr
    refine ⟨hil,?_,Or.inl ⟨t,hrpoint,hright⟩⟩
    intro d hd heq
    exact hinterior d hd (heq ▸ hrpoint)

theorem comparisonConstructedBin_cap_fibre_master {τ : Type*}
    (n bins : ℕ) (q : ℝ→FeatureIndex n→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (a z : τ→ℝ) (H : ℝ→ℝ) (D : Finset ℝ)
    (us : List PositiveMass) (hnodes : ∀u∈us,u.val ≤ 1)
    (hretain : ∀d∈D,∀hp : 0<α.val.val d,(⟨α.val.val d,hp⟩ : PositiveMass)∈us) (ag zg w : ℝ) (U : Set ℝ)
    (m : ℕ) (t : τ) (b : Fin bins)
    (hD : ∀d∈D,d∈Icc (0:ℝ) 1) (ha : a t∈D) (hz : z t∈D) (haz : a t<z t)
    (hinterior : ∀d∈D,d∉Ioo (a t) (z t)) (hag : ag≤a t) (hzg : z t≤zg)
    (hcap : ∀r∈Ioo (a t) (z t),wholeUnit U r=Ioo (a t) (z t)) :
    let Dm := D.image α.val.val
    let as := finiteCutMasses us m
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
  exact comparisonConstructedRows_cap_fibre_master hc hk hkc hm hM q α a z H D us hnodes hretain ag zg m t
    hD ha hz haz hinterior hag hzg

end

end OAI.SKFluctuations.LaplaceWindowFormalization
