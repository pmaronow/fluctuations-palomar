module

public import ComparisonWholeCapMassCoordinates
public import ComparisonSelectedRestrictions

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open Set Hierarchy LaplaceWindowFormalization
open scoped BigOperators NNReal
attribute [local instance] Classical.propDecidable

theorem physicalWindowMass_erase_zero_row {ι : Type} (steps : List (GaussianStep ι))
    (J : Finset (Fin (steps.length+1))) (p : Fin (steps.length+1))
    (hp:pathMassDifferences steps 0 p=0) :
    physicalWindowMass steps 0 (J.erase p)=physicalWindowMass steps 0 J := by
  by_cases hm:p∈J
  · unfold physicalWindowMass
    rw [Finset.sum_erase_eq_sub hm,hp,sub_zero]
  · rw [Finset.erase_eq_of_notMem hm]

theorem completeMassCapCells_erase_initial_mass {ι : Type}
    (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (p : Fin (steps.length+1)) {q : ℕ} (hpq:p.val<q) (hq:q ≤ steps.length+1) :
    physicalWindowMass steps 0
      ((completeMassCapCells steps (physicalCutMass 0 steps p.val)
        (physicalCutMass 0 steps q)).erase p)=
      (physicalCutMass 0 steps q-physicalCutMass 0 steps p.val)-pathMassDifferences steps 0 p := by
  have hfull := completeMassCapCells_mass steps ha hpq.le hq
  by_cases hp:0 < pathMassDifferences steps 0 p
  · have hmem:p∈completeMassCapCells steps (physicalCutMass 0 steps p.val)
      (physicalCutMass 0 steps q) := by
      simp only [completeMassCapCells,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨hp,(physicalCellMassMidpoint_mem_iff_interval steps ha p.val q p hp).mpr ⟨le_rfl,hpq⟩⟩
    unfold physicalWindowMass at hfull ⊢
    rw [Finset.sum_erase_eq_sub hmem,hfull]
  · have hz:pathMassDifferences steps 0 p=0 := le_antisymm (le_of_not_gt hp)
      (pathMassDifferences_nonneg steps ha p)
    rw [physicalWindowMass_erase_zero_row steps _ p hz,hfull,hz,sub_zero]

def finiteBoundaryClockCell {ι : Type} (clock : ℝ → ι → ℝ≥0)
    (as : List PositiveMass) (d : ℝ) : Fin ((sampleClockSteps clock 0 as).length+1) :=
  ⟨finiteBoundaryMassIndex d as,by
    unfold finiteBoundaryMassIndex
    split_ifs
    · omega
    · rw [sampleClockSteps_length]
      exact Nat.lt_succ_of_le (retainedMassPrefixIndex_le_length d as)⟩

def fixedEndpointRows {ι : Type} (clock : ℝ → ι → ℝ≥0)
    (as : List PositiveMass) (D : Finset ℝ) : Finset (Fin ((sampleClockSteps clock 0 as).length+1)) :=
  D.image (finiteBoundaryClockCell clock as)

theorem fixedEndpointRows_mass_le {ι : Type} (clock : ℝ → ι → ℝ≥0)
    (as : List PositiveMass) (D : Finset ℝ) {mesh : ℝ} (hm:0 ≤ mesh)
    (hmesh:PartitionMesh mesh 0 as) :
    physicalWindowMass (sampleClockSteps clock 0 as) 0 (fixedEndpointRows clock as D) ≤
      (D.card:ℝ)*mesh := by
  unfold physicalWindowMass
  calc
    _ ≤ ∑i∈fixedEndpointRows clock as D,mesh := by
      apply Finset.sum_le_sum
      intro i hi
      rw [pathMassDifferences_eq_cutMass]
      exact sampled_physicalMass_mesh clock as hmesh i
    _ = ((fixedEndpointRows clock as D).card:ℝ)*mesh := by simp
    _ ≤ (D.card:ℝ)*mesh := mul_le_mul_of_nonneg_right
      (by exact_mod_cast Finset.card_image_le) hm

theorem canonical_fixedEndpointRows_mass_le {ι : Type} (clock : ℝ → ι → ℝ≥0)
    (D : Finset ℝ) (hD:∀d∈D,d∈Icc (0:ℝ) 1) (m : ℕ) :
    let as := finiteCutMasses (finiteBoundaryMassNodes D) m
    physicalWindowMass (sampleClockSteps clock 0 as) 0 (fixedEndpointRows clock as D) ≤
      (D.card:ℝ)*((m+1:ℕ):ℝ)⁻¹ := by
  dsimp only
  exact fixedEndpointRows_mass_le clock _ D (by positivity)
    (finiteCutMasses_mesh _ (finiteBoundaryMassNodes_bound D (fun d hd => (hD d hd).2)) m)

theorem finiteBoundaryMass_cap_erase_initial_mass {ι : Type} (clock : ℝ → ι → ℝ≥0)
    (D : Finset ℝ) (hD:∀d∈D,d∈Icc (0:ℝ) 1) (m : ℕ)
    {a b : ℝ} (ha:a∈D) (hb:b∈D) (hab:a<b) :
    let as := finiteCutMasses (finiteBoundaryMassNodes D) m
    let steps := sampleClockSteps clock 0 as
    physicalWindowMass steps 0 ((completeMassCapCells steps a b).erase (finiteBoundaryClockCell clock as a))=
      (b-a)-pathMassDifferences steps 0 (finiteBoundaryClockCell clock as a) := by
  dsimp only
  let as := finiteCutMasses (finiteBoundaryMassNodes D) m
  let steps := sampleClockSteps clock 0 as
  let p := finiteBoundaryClockCell clock as a
  let q := finiteBoundaryMassIndex b as
  have ho : OrderedSteps 0 steps := sampleClockSteps_ordered clock as
    (finiteCutMasses_ordered _ (finiteBoundaryMassNodes_bound D (fun d hd => (hD d hd).2)) m)
  have hea := finiteBoundaryMassIndex_exact clock D hD m ha
  have heb := finiteBoundaryMassIndex_exact clock D hD m hb
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

theorem cap_discard_mass_positive_and_ratio {mu removed mesh : ℝ}
    (hremoved:0 ≤ removed) (hbound:removed ≤ mesh) (hsmall:mesh < mu) :
    0 < mu-removed ∧ mu/(mu-removed) ≤ mu/(mu-mesh) := by
  have hmu : 0 ≤ mu := hremoved.trans hbound |>.trans hsmall.le
  have hkeep : 0 < mu-removed := sub_pos.mpr (hbound.trans_lt hsmall)
  exact ⟨hkeep,div_le_div_of_nonneg_left hmu (sub_pos.mpr hsmall) (by linarith)⟩

theorem physicalSelectedUnitMass_eq_window_filter {ι V : Type} [Fintype V] [DecidableEq V]
    (steps : List (GaussianStep ι)) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → V) (u : V) :
    physicalSelectedUnitMass steps J unit u=
      physicalWindowMass steps 0 (J.filter (fun i => unit i=u)) := by
  unfold physicalSelectedUnitMass physicalWindowMass
  rw [Finset.sum_filter]
  have he (i : Fin (steps.length+1)) :
      (if i∈J ∧ unit i=u then pathMassDifferences steps 0 i else 0)=
        if i∈J then (if unit i=u then pathMassDifferences steps 0 i else 0) else 0 := by
    by_cases hi:i∈J <;> simp [hi]
  simp_rw [he]
  rw [Finset.sum_ite_mem,Finset.univ_inter]

theorem selectedWholeUnitBin_cap_unit_filter {ι V : Type} [Fintype V] [DecidableEq V]
    (steps : List (GaussianStep ι)) (r : Fin (steps.length+1) → ℝ)
    {U : Set ℝ} {a b : ℝ} (hU:U⊆Icc a b)
    (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ) (bins : ℕ) (w : ℝ) (j : ℕ)
    (unit : Fin (steps.length+1) → V)
    (hclass : ∀i∈selectedWholeUnitBinCells steps r U F S a b bins w j,
      ∀t∈selectedWholeUnitBinCells steps r U F S a b bins w j,
      unit i=unit t ↔ wholeUnit U (r i)=wholeUnit U (r t))
    {i : Fin (steps.length+1)}
    (hi:i∈selectedWholeUnitBinCells steps r U F S a b bins w j) (hir:r i∈U) :
    (selectedWholeUnitBinCells steps r U F S a b bins w j).filter (fun t => unit t=unit i)=
      Finset.univ.filter (fun t => 0 < pathMassDifferences steps 0 t ∧
        r t∈ordConnectedComponent U (r i)) := by
  ext t
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro ht
    have he := (hclass t ht.1 i hi).mp ht.2
    have hm : r t∈wholeUnit U (r i) := he ▸ self_mem_wholeUnit U (r t)
    exact ⟨((mem_selectedWholeUnitBinCells _ _ _ _ _ _ _ _ _ _ _).mp ht.1).1,
      by simpa [wholeUnit,hir] using hm⟩
  · intro ht
    have hm : r t∈wholeUnit U (r i) := by simpa [wholeUnit,hir] using ht.2
    have htJ := selectedWholeUnitBinCells_complete steps r hU F S bins w j hi ht.1 hm
    exact ⟨htJ,(hclass t htJ i hi).mpr (wholeUnit_eq_of_mem U hm)⟩

theorem selectedWholeUnitBin_cap_unit_restriction_mass {ι V : Type}
    [Fintype V] [DecidableEq V] (steps : List (GaussianStep ι))
    (r : Fin (steps.length+1) → ℝ) {U : Set ℝ} {a b : ℝ} (hU:U⊆Icc a b)
    (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ) (bins : ℕ) (w : ℝ) (j : ℕ)
    (unit : Fin (steps.length+1) → V)
    (hclass : ∀i∈selectedWholeUnitBinCells steps r U F S a b bins w j,
      ∀t∈selectedWholeUnitBinCells steps r U F S a b bins w j,
      unit i=unit t ↔ wholeUnit U (r i)=wholeUnit U (r t))
    (B : Finset (Fin (steps.length+1))) {i : Fin (steps.length+1)}
    (hi:i∈selectedWholeUnitBinCells steps r U F S a b bins w j) (hir:r i∈U) :
    physicalSelectedUnitMass steps ((selectedWholeUnitBinCells steps r U F S a b bins w j)\B)
      unit (unit i)=physicalWindowMass steps 0
      ((Finset.univ.filter (fun t => 0 < pathMassDifferences steps 0 t ∧
        r t∈ordConnectedComponent U (r i)))\B) := by
  rw [physicalSelectedUnitMass_eq_window_filter]
  have he :
      ((selectedWholeUnitBinCells steps r U F S a b bins w j)\B).filter (fun t => unit t=unit i)=
      ((selectedWholeUnitBinCells steps r U F S a b bins w j).filter (fun t => unit t=unit i))\B := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_sdiff]
    tauto
  rw [he,selectedWholeUnitBin_cap_unit_filter steps r hU F S bins w j unit hclass hi hir]

theorem finiteBoundaryRows_complete_cap_sdiff {ι : Type} (clock : ℝ → ι → ℝ≥0)
    (D : Finset ℝ) (hD:∀d∈D,d∈Icc (0:ℝ) 1) (m : ℕ)
    {a b : ℝ} (ha:a∈D) (hb:b∈D) (hab:a<b)
    (hinterior:∀d∈D,d∉Ioo a b) :
    let as := finiteCutMasses (finiteBoundaryMassNodes D) m
    let steps := sampleClockSteps clock 0 as
    (completeMassCapCells steps a b)\fixedEndpointRows clock as D=
      (completeMassCapCells steps a b).erase (finiteBoundaryClockCell clock as a) := by
  dsimp only
  let as := finiteCutMasses (finiteBoundaryMassNodes D) m
  let steps := sampleClockSteps clock 0 as
  have ho : OrderedSteps 0 steps := sampleClockSteps_ordered clock as
    (finiteCutMasses_ordered _ (finiteBoundaryMassNodes_bound D (fun d hd => (hD d hd).2)) m)
  have hcell (d : ℝ) (hd:d∈D) : physicalCutMass 0 steps (finiteBoundaryClockCell clock as d).val=d :=
    finiteBoundaryMassIndex_exact clock D hD m hd
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

 theorem finiteBoundaryRows_complete_cap_mass {ι : Type} (clock : ℝ → ι → ℝ≥0)
    (D : Finset ℝ) (hD:∀d∈D,d∈Icc (0:ℝ) 1) (m : ℕ)
    {a b : ℝ} (ha:a∈D) (hb:b∈D) (hab:a<b)
    (hinterior:∀d∈D,d∉Ioo a b) :
    let as := finiteCutMasses (finiteBoundaryMassNodes D) m
    let steps := sampleClockSteps clock 0 as
    physicalWindowMass steps 0 ((completeMassCapCells steps a b)\fixedEndpointRows clock as D)=
      (b-a)-pathMassDifferences steps 0 (finiteBoundaryClockCell clock as a) := by
  dsimp only
  rw [finiteBoundaryRows_complete_cap_sdiff clock D hD m ha hb hab hinterior]
  exact finiteBoundaryMass_cap_erase_initial_mass clock D hD m ha hb hab

 theorem comparisonWholeCapEndpointMasses_avoid_cap_interior {k M : ℝ → ℝ}
    (α : inverseIntegralConstraints 0 0 k M) {U : Set ℝ} (hopen:IsOpen U)
    (hU:U⊆Icc (0:ℝ) 1) (F : Finset (ordConnectedSection U))
    {r : ℝ} (hr:r∈U) :
    ∀d∈comparisonWholeCapEndpointMasses α U F,
      d∉Ioo (α.val.val (sInf (ordConnectedComponent U r)))
        (α.val.val (sSup (ordConnectedComponent U r))) := by
  obtain ⟨_,_,_,_,heq,_,_⟩ := wholeCap_component_endpoints hopen hU hr
  have hno {x : ℝ} (hx:x∉U) :
      α.val.val x∉Ioo (α.val.val (sInf (ordConnectedComponent U r)))
        (α.val.val (sSup (ordConnectedComponent U r))) := by
    intro hm
    have hlo : sInf (ordConnectedComponent U r)<x := by
      by_contra hbad
      exact hm.1.not_ge (α.val.property.2 (le_of_not_gt hbad))
    have hhi : x<sSup (ordConnectedComponent U r) := by
      by_contra hbad
      exact hm.2.not_ge (α.val.property.2 (le_of_not_gt hbad))
    exact hx (ordConnectedComponent_subset (heq.symm ▸ (show x∈Ioo
      (sInf (ordConnectedComponent U r)) (sSup (ordConnectedComponent U r)) from ⟨hlo,hhi⟩)))
  intro d hd
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨_,_,_,_,_,hinf,hsup⟩ := wholeCap_component_endpoints hopen hU
    (ordConnectedSection_subset z.property)
  rcases Finset.mem_insert.mp hd with rfl|hd
  · exact hno hinf
  · have he := Finset.mem_singleton.mp hd
    subst d
    exact hno hsup

 theorem comparisonWholeCap_retained_grid_mass_after_discard {ι : Type}
    {c : ℝ} {k M : ℝ → ℝ} (hc:0<c) (hk:ContinuousOn k (Icc (0:ℝ) 1))
    (hkc:∀r∈Icc (0:ℝ) 1,c ≤ k r) (hm:MonotoneOn M (Icc (0:ℝ) 1)) (hM:0 ≤ M 1)
    (clock : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M) {U : Set ℝ}
    (hopen:IsOpen U) (hU:U⊆Icc (0:ℝ) 1) (F : Finset (ordConnectedSection U))
    (m : ℕ) {r : ordConnectedSection U} (hr:r∈F) :
    let D := comparisonWholeCapEndpointMasses α U F
    let as := finiteCutMasses (finiteBoundaryMassNodes D) m
    let steps := sampleClockSteps clock 0 as
    let a := α.val.val (sInf (ordConnectedComponent U r.val))
    let b := α.val.val (sSup (ordConnectedComponent U r.val))
    physicalWindowMass steps 0 ((completeMassCapCells steps a b)\fixedEndpointRows clock as D)=
      (wholeCapRadiusMass (comparisonSweepQuantile hc hk hkc hm hM α)
        (fun u _ => comparisonSweepQuantile_bounds hc hk hkc hm hM α u)).real
          (ordConnectedComponent U r.val)-pathMassDifferences steps 0 (finiteBoundaryClockCell clock as a) := by
  dsimp only
  have hrU := ordConnectedSection_subset r.property
  obtain ⟨hlo,hlr,hrz,hhi,heq,_,_⟩ := wholeCap_component_endpoints hopen hU hrU
  have hla : sInf (ordConnectedComponent U r.val)∈Icc (0:ℝ) 1 :=
    ⟨hlo,hlr.le.trans (hU hrU).2⟩
  have hlb : sSup (ordConnectedComponent U r.val)∈Icc (0:ℝ) 1 :=
    ⟨(hU hrU).1.trans hrz.le,hhi⟩
  have hab := inverseConstraint_strictMonoOn hc hk hkc α.property hla hlb (hlr.trans hrz)
  have hend := comparisonWholeCapEndpointMasses_contains α U F hr
  rw [finiteBoundaryRows_complete_cap_mass clock _ (comparisonWholeCapEndpointMasses_bound α U F) m
    hend.1 hend.2 hab (comparisonWholeCapEndpointMasses_avoid_cap_interior α hopen hU F hrU)]
  congr 1
  conv_rhs => rw [heq]
  exact (wholeCap_actual_comparison_mass_Ioo hc hk hkc hm hM α (hlr.trans hrz)).symm

end OAI.SKFluctuations.WholeUnitSideKernel

