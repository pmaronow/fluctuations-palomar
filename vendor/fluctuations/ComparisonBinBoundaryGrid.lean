module

public import ComparisonCapBoundaryRowDiscard

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open Set Hierarchy MeasureTheory LaplaceWindowFormalization
open scoped BigOperators NNReal
attribute [local instance] Classical.propDecidable

theorem wholeUnit_closed_set_boundaries_contact {U A : Set ℝ}
    (hopen:IsOpen U) (hU:U⊆Icc (0:ℝ) 1) (hA:A⊆Icc (0:ℝ) 1) (hne:A.Nonempty)
    (hwhole:∀r∈A,wholeUnit U r⊆A) : sInf A∉U ∧ sSup A∉U := by
  have hloA : BddBelow A := ⟨0,fun r hr => (hA hr).1⟩
  have hhiA : BddAbove A := ⟨1,fun r hr => (hA hr).2⟩
  constructor
  · intro hr
    obtain ⟨_,hlr,hrz,_,_,_,_⟩ := wholeCap_component_endpoints hopen hU hr
    obtain ⟨v,hv,hvz⟩ := exists_lt_of_csInf_lt hne hrz
    have hrv : sInf A ≤ v := csInf_le hloA hv
    have hvC : v∈ordConnectedComponent U (sInf A) := by
      have he := (wholeCap_component_endpoints hopen hU hr).2.2.2.2.1
      rw [he]
      exact ⟨hlr.trans_le hrv,hvz⟩
    let t := (sInf (ordConnectedComponent U (sInf A))+sInf A)/2
    have htC : t∈ordConnectedComponent U (sInf A) := by
      have he := (wholeCap_component_endpoints hopen hU hr).2.2.2.2.1
      rw [he]
      constructor <;> dsimp [t] <;> linarith
    have ht : t∈A := hwhole v hv (by
      have hvU := ordConnectedComponent_subset hvC
      simp only [wholeUnit,ite_eq_left hvU]
      exact (ordConnectedComponent_eq hvC) ▸ htC)
    have hbound := csInf_le hloA ht
    dsimp [t] at hbound
    linarith
  · intro hr
    obtain ⟨_,hlr,hrz,_,_,_,_⟩ := wholeCap_component_endpoints hopen hU hr
    obtain ⟨v,hv,hlv⟩ := exists_lt_of_lt_csSup hne hlr
    have hvr : v ≤ sSup A := le_csSup hhiA hv
    have hvC : v∈ordConnectedComponent U (sSup A) := by
      have he := (wholeCap_component_endpoints hopen hU hr).2.2.2.2.1
      rw [he]
      exact ⟨hlv,hvr.trans_lt hrz⟩
    let t := (sSup A+sSup (ordConnectedComponent U (sSup A)))/2
    have htC : t∈ordConnectedComponent U (sSup A) := by
      have he := (wholeCap_component_endpoints hopen hU hr).2.2.2.2.1
      rw [he]
      constructor <;> dsimp [t] <;> linarith
    have ht : t∈A := hwhole v hv (by
      have hvU := ordConnectedComponent_subset hvC
      simp only [wholeUnit,ite_eq_left hvU]
      exact (ordConnectedComponent_eq hvC) ▸ htC)
    have hbound := le_csSup hhiA ht
    dsimp [t] at hbound
    linarith

theorem heightBinSet_wholeUnit_closed {U : Set ℝ} (hU:U⊆Icc (0:ℝ) 1)
    (S : ℝ → ℝ) (bins : ℕ) (w : ℝ) (j : ℕ) :
    ∀r∈heightBinSet (capEndHeight U S) 0 1 bins w j,
      wholeUnit U r⊆heightBinSet (capEndHeight U S) 0 1 bins w j := by
  intro r hr t ht
  have htDomain:t∈Icc (0:ℝ) 1 := by
    by_cases hrU:r∈U
    · exact hU (ordConnectedComponent_subset (by simpa [wholeUnit,hrU] using ht))
    · have he:t=r := by simpa [wholeUnit,hrU] using ht
      exact he ▸ hr.1
  exact ⟨htDomain,by
    change heightBin bins w (capEndHeight U S t)=j
    rw [capEndHeight_const_on_wholeUnit U S ht]
    exact hr.2⟩

def heightBinBoundaryMasses (U : Set ℝ) (S : ℝ → ℝ) (bins : ℕ) (w : ℝ) : Finset ℝ :=
  (Finset.range bins).biUnion (fun j =>
    let A := heightBinSet (capEndHeight U S) 0 1 bins w j
    if A.Nonempty then {sInf A,sSup A} else ∅)

theorem heightBinBoundaryMasses_bound (U : Set ℝ) (S : ℝ → ℝ) (bins : ℕ) (w : ℝ) :
    ∀d∈heightBinBoundaryMasses U S bins w,d∈Icc (0:ℝ) 1 := by
  intro d hd
  obtain ⟨j,hj,hd⟩ := Finset.mem_biUnion.mp hd
  let A := heightBinSet (capEndHeight U S) 0 1 bins w j
  change d∈(if A.Nonempty then {sInf A,sSup A} else ∅) at hd
  split_ifs at hd with hne
  · have hA:A⊆Icc (0:ℝ) 1 := fun r hr => hr.1
    have hlo : BddBelow A := ⟨0,fun r hr => (hA hr).1⟩
    have hhi : BddAbove A := ⟨1,fun r hr => (hA hr).2⟩
    obtain ⟨r,hr⟩ := hne
    rcases Finset.mem_insert.mp hd with rfl|hd
    · exact ⟨le_csInf ⟨r,hr⟩ (fun x hx => (hA hx).1),(csInf_le hlo hr).trans (hA hr).2⟩
    · have he := Finset.mem_singleton.mp hd
      subst d
      exact ⟨(hA hr).1.trans (le_csSup hhi hr),csSup_le ⟨r,hr⟩ (fun x hx => (hA hx).2)⟩
  · exact False.elim (Finset.notMem_empty _ hd)

theorem heightBinBoundaryMasses_contact {U : Set ℝ}
    (hopen:IsOpen U) (hU:U⊆Icc (0:ℝ) 1) (S : ℝ → ℝ) (bins : ℕ) (w : ℝ) :
    ∀d∈heightBinBoundaryMasses U S bins w,d∉U := by
  intro d hd
  obtain ⟨j,hj,hd⟩ := Finset.mem_biUnion.mp hd
  let A := heightBinSet (capEndHeight U S) 0 1 bins w j
  change d∈(if A.Nonempty then {sInf A,sSup A} else ∅) at hd
  split_ifs at hd with hne
  · have hcontact := wholeUnit_closed_set_boundaries_contact hopen hU
      (show A⊆Icc (0:ℝ) 1 from fun r hr => hr.1) hne
      (heightBinSet_wholeUnit_closed hU S bins w j)
    rcases Finset.mem_insert.mp hd with rfl|hd
    · exact hcontact.1
    · have he := Finset.mem_singleton.mp hd
      subst d
      exact hcontact.2
  · exact False.elim (Finset.notMem_empty _ hd)

theorem heightBinBoundaryMasses_card_le (U : Set ℝ) (S : ℝ → ℝ) (bins : ℕ) (w : ℝ) :
    (heightBinBoundaryMasses U S bins w).card ≤ 2*bins := by
  unfold heightBinBoundaryMasses
  calc
    _ ≤ ∑j∈Finset.range bins,
        (if (heightBinSet (capEndHeight U S) 0 1 bins w j).Nonempty then
          {sInf (heightBinSet (capEndHeight U S) 0 1 bins w j),
            sSup (heightBinSet (capEndHeight U S) 0 1 bins w j)} else (∅:Finset ℝ)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑j∈Finset.range bins,2 := Finset.sum_le_sum (fun j hj => by
      split_ifs
      · exact Finset.card_le_two
      · simp)
    _ = _ := by simp;omega

section
variable {c : ℝ} {k M : ℝ → ℝ} (hc:0<c) (hk:ContinuousOn k (Icc (0:ℝ) 1))
    (hkc:∀r∈Icc (0:ℝ) 1,c ≤ k r) (hm:MonotoneOn M (Icc (0:ℝ) 1)) (hM:0 ≤ M 1)

def comparisonWholeCapBinEndpointMasses (α : inverseIntegralConstraints 0 0 k M)
    (U : Set ℝ) (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ) (bins : ℕ) (w : ℝ) : Finset ℝ :=
  let q := comparisonSweepQuantile hc hk hkc hm hM α
  comparisonWholeCapEndpointMasses α U F∪heightBinBoundaryMasses (q⁻¹' U) (S∘q) bins w

theorem comparisonWholeCapBinEndpointMasses_bound (α : inverseIntegralConstraints 0 0 k M)
    (U : Set ℝ) (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ) (bins : ℕ) (w : ℝ) :
    ∀d∈comparisonWholeCapBinEndpointMasses hc hk hkc hm hM α U F S bins w,d∈Icc (0:ℝ) 1 := by
  intro d hd
  rcases Finset.mem_union.mp hd with hd|hd
  · exact comparisonWholeCapEndpointMasses_bound α U F d hd
  · exact heightBinBoundaryMasses_bound _ _ bins w d hd

theorem comparisonWholeCapBinEndpointMasses_avoid_cap
    (α : inverseIntegralConstraints 0 0 k M) {U : Set ℝ} (hopen:IsOpen U)
    (hU:U⊆Ioo (0:ℝ) 1) (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ)
    (bins : ℕ) (w : ℝ) {r : ℝ} (hr:r∈U) :
    ∀d∈comparisonWholeCapBinEndpointMasses hc hk hkc hm hM α U F S bins w,
      d∉Ioo (α.val.val (sInf (ordConnectedComponent U r)))
        (α.val.val (sSup (ordConnectedComponent U r))) := by
  intro d hd hbad
  have hUcc:U⊆Icc (0:ℝ) 1 := hU.trans Ioo_subset_Icc_self
  rcases Finset.mem_union.mp hd with hd|hd
  · exact comparisonWholeCapEndpointMasses_avoid_cap_interior α hopen hUcc F hr d hd hbad
  · have hopenMass := hopen.preimage (comparisonSweepQuantile_continuous hc hk hkc hm hM α)
    have hmassSub := (comparisonSweepQuantile_preimage_open_subset hc hk hkc hm hM α hU).trans
      Ioo_subset_Icc_self
    have hcontact := heightBinBoundaryMasses_contact hopenMass hmassSub
      (S∘comparisonSweepQuantile hc hk hkc hm hM α) bins w d hd
    have he := comparisonWholeCap_mass_component hc hk hkc hm hM α hopen hUcc hr
    rw [←he] at hbad
    exact hcontact (ordConnectedComponent_subset hbad)

theorem comparisonWholeCapEndpointMasses_card_le
    (α : inverseIntegralConstraints 0 0 k M) (U : Set ℝ)
    (F : Finset (ordConnectedSection U)) :
    (comparisonWholeCapEndpointMasses α U F).card ≤ 2*F.card := by
  unfold comparisonWholeCapEndpointMasses
  calc
    _ ≤ ∑r∈F,({α.val.val (sInf (ordConnectedComponent U r.val)),
      α.val.val (sSup (ordConnectedComponent U r.val))}:Finset ℝ).card := Finset.card_biUnion_le
    _ ≤ ∑r∈F,2 := Finset.sum_le_sum (fun r hr => Finset.card_le_two)
    _ = _ := by simp;omega

theorem comparisonWholeCapBinEndpointMasses_card_le
    (α : inverseIntegralConstraints 0 0 k M) (U : Set ℝ)
    (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ) (bins : ℕ) (w : ℝ) :
    (comparisonWholeCapBinEndpointMasses hc hk hkc hm hM α U F S bins w).card ≤
      2*F.card+2*bins := by
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add
    (comparisonWholeCapEndpointMasses_card_le α U F)
    (heightBinBoundaryMasses_card_le _ _ bins w))

theorem comparisonWholeCapBinBoundaryRows_mass_le {ι : Type}
    (clock : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (U : Set ℝ) (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ)
    (m bins : ℕ) (w : ℝ) :
    let D := comparisonWholeCapBinEndpointMasses hc hk hkc hm hM α U F S bins w
    let as := finiteCutMasses (finiteBoundaryMassNodes D) m
    physicalWindowMass (sampleClockSteps clock 0 as) 0 (fixedEndpointRows clock as D) ≤
      ((2*F.card+2*bins:ℕ):ℝ)*((m+1:ℕ):ℝ)⁻¹ := by
  dsimp only
  exact (canonical_fixedEndpointRows_mass_le clock _
    (comparisonWholeCapBinEndpointMasses_bound hc hk hkc hm hM α U F S bins w) m).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast
        comparisonWholeCapBinEndpointMasses_card_le hc hk hkc hm hM α U F S bins w)
          (by positivity))

def comparisonWholeCapBinOriginalBin {ι : Type} (clock : ℝ → ι → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (U : Set ℝ) (hU:U⊆Icc (0:ℝ) 1)
    (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ) (m bins : ℕ) (w : ℝ) (j : ℕ) :=
  let q := comparisonSweepQuantile hc hk hkc hm hM α
  let D := comparisonWholeCapBinEndpointMasses hc hk hkc hm hM α U F S bins w
  let as := finiteCutMasses (finiteBoundaryMassNodes D) m
  let steps := sampleClockSteps clock 0 as
  selectedWholeUnitBinCells steps (physicalCellMassMidpoint steps) (q⁻¹' U)
    (comparisonWholeCapMassSelection hc hk hkc hm hM α U hU F) (S∘q) 0 1 bins w j

theorem comparisonWholeCapBinOriginalBin_partition {ι : Type} (clock : ℝ → ι → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (U : Set ℝ) (hU:U⊆Icc (0:ℝ) 1)
    (F : Finset (ordConnectedSection U)) (S : ℝ → ℝ) (m bins : ℕ) (w : ℝ) (j : ℕ)
    (hJ:(comparisonWholeCapBinOriginalBin hc hk hkc hm hM clock α U hU F S m bins w j).Nonempty) :
    let q := comparisonSweepQuantile hc hk hkc hm hM α
    let D := comparisonWholeCapBinEndpointMasses hc hk hkc hm hM α U F S bins w
    let as := finiteCutMasses (finiteBoundaryMassNodes D) m
    let steps := sampleClockSteps clock 0 as
    let J := comparisonWholeCapBinOriginalBin hc hk hkc hm hM clock α U hU F S m bins w j
    ∃ (K : ℕ) (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ),
      0 < K ∧ x 0=0 ∧ x K=physicalWindowMass steps 0 J ∧
      (∀u:Fin K,x u.val < x (u.val+1)) ∧
      (∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u.val) ∧
      (∀i∈J,∀t∈J,unit i=unit t ↔
        wholeUnit (q⁻¹' U) (physicalCellMassMidpoint steps i)=
          wholeUnit (q⁻¹' U) (physicalCellMassMidpoint steps t)) ∧
      MonotoneOn unit (J:Set (Fin (steps.length+1))) := by
  dsimp only
  let D := comparisonWholeCapBinEndpointMasses hc hk hkc hm hM α U F S bins w
  let as := finiteCutMasses (finiteBoundaryMassNodes D) m
  let steps := sampleClockSteps clock 0 as
  have ho : OrderedSteps 0 steps := sampleClockSteps_ordered clock as
    (finiteCutMasses_ordered _ (finiteBoundaryMassNodes_bound D
      (fun d hd => (comparisonWholeCapBinEndpointMasses_bound hc hk hkc hm hM α U F S bins w d hd).2)) m)
  exact selectedWholeUnitBin_exists_coordinates steps ho (physicalCellMassMidpoint steps)
    (physicalCellMassMidpoint_monotone steps ho) _ _ _ 0 1 bins w j hJ

theorem comparisonWholeCapBin_grid_mass_after_discard {ι : Type}
    (clock : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M) {U : Set ℝ}
    (hopen:IsOpen U) (hU:U⊆Ioo (0:ℝ) 1) (F : Finset (ordConnectedSection U))
    (S : ℝ → ℝ) (m bins : ℕ) (w : ℝ) {r : ordConnectedSection U} (hr:r∈F) :
    let D := comparisonWholeCapBinEndpointMasses hc hk hkc hm hM α U F S bins w
    let as := finiteCutMasses (finiteBoundaryMassNodes D) m
    let steps := sampleClockSteps clock 0 as
    let a := α.val.val (sInf (ordConnectedComponent U r.val))
    let b := α.val.val (sSup (ordConnectedComponent U r.val))
    physicalWindowMass steps 0 ((completeMassCapCells steps a b)\fixedEndpointRows clock as D)=
      (wholeCapRadiusMass (comparisonSweepQuantile hc hk hkc hm hM α)
        (fun u _ => comparisonSweepQuantile_bounds hc hk hkc hm hM α u)).real
          (ordConnectedComponent U r.val)-pathMassDifferences steps 0 (finiteBoundaryClockCell clock as a) := by
  dsimp only
  have hUcc:=hU.trans Ioo_subset_Icc_self
  have hrU := ordConnectedSection_subset r.property
  obtain ⟨hlo,hlr,hrz,hhi,heq,_,_⟩ := wholeCap_component_endpoints hopen hUcc hrU
  have hla : sInf (ordConnectedComponent U r.val)∈Icc (0:ℝ) 1 :=
    ⟨hlo,hlr.le.trans (hUcc hrU).2⟩
  have hlb : sSup (ordConnectedComponent U r.val)∈Icc (0:ℝ) 1 :=
    ⟨(hUcc hrU).1.trans hrz.le,hhi⟩
  have hab := inverseConstraint_strictMonoOn hc hk hkc α.property hla hlb (hlr.trans hrz)
  have hend := comparisonWholeCapEndpointMasses_contains α U F hr
  rw [finiteBoundaryRows_complete_cap_mass clock _
    (comparisonWholeCapBinEndpointMasses_bound hc hk hkc hm hM α U F S bins w) m
    (Finset.mem_union_left _ hend.1) (Finset.mem_union_left _ hend.2) hab
    (comparisonWholeCapBinEndpointMasses_avoid_cap hc hk hkc hm hM α hopen hU F S bins w hrU)]
  congr 1
  conv_rhs => rw [heq]
  exact (wholeCap_actual_comparison_mass_Ioo hc hk hkc hm hM α (hlr.trans hrz)).symm

end
end OAI.SKFluctuations.WholeUnitSideKernel
