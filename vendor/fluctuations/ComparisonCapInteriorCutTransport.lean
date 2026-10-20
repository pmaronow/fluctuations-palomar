module

public import ComparisonRestrictedWholeUnitPartition

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open Set Hierarchy LaplaceWindowFormalization
open scoped BigOperators NNReal
attribute [local instance] Classical.propDecidable

theorem retainedMassPrefixIndex_eq_of_positive_left_cut {ι : Type}
    (clock : ℝ → ι → ℝ≥0) {a : ℝ} (as : List PositiveMass) (ho:MassOrdered a as)
    (i:Fin ((sampleClockSteps clock a as).length+1))
    (hp:0 < pathMassDifferences (sampleClockSteps clock a as) a i) :
    retainedMassPrefixIndex (physicalCutMass a (sampleClockSteps clock a as) i.val) as=i.val := by
  induction as generalizing a with
  | nil =>
    have hi:i.val=0 := by simpa [sampleClockSteps] using Nat.le_of_lt_succ i.isLt
    simp [retainedMassPrefixIndex,retainedMassBefore,hi]
  | cons b bs ih =>
    revert hp
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hp
      have hab:a<b.val := by
        have hh:0<b.val-a := by
          exact hp
        linarith
      simp [sampleClockSteps,physicalCutMass,retainedMassPrefixIndex,
        retainedMassBefore_cons_gt b bs hab.not_ge]
    · intro hp
      have hj:j.val ≤ bs.length := by
        simpa only [sampleClockSteps_length] using Nat.le_of_lt_succ j.isLt
      have hbd:b.val ≤ physicalCutMass b.val (sampleClockSteps clock b.val bs) j.val := by
        rw [physicalCutMass_sampleClockSteps clock b.val bs j.val hj]
        exact (partitionPoint_mem bs ho.2.2 j.val).1
      have hpi:0 < pathMassDifferences (sampleClockSteps clock b.val bs) b.val j := by
        exact hp
      have he:=ih ho.2.2 j hpi
      change retainedMassPrefixIndex (physicalCutMass b.val (sampleClockSteps clock b.val bs) j.val)
        (b::bs)=j.val+1
      simpa only [retainedMassPrefixIndex,retainedMassBefore_cons_le b bs hbd,List.length_cons]
        using congrArg Nat.succ he

theorem retainedMassPrefixIndex_zero (as:List PositiveMass) : retainedMassPrefixIndex 0 as=0 := by
  cases as with
  | nil => rfl
  | cons b bs =>
    simp [retainedMassPrefixIndex,retainedMassBefore_cons_gt b bs (not_le.mpr b.property)]

theorem finiteBoundaryClockCell_eq_of_positive_left_cut {ι : Type}
    (clock : ℝ → ι → ℝ≥0) (as:List PositiveMass) (ho:MassOrdered 0 as)
    (i:Fin ((sampleClockSteps clock 0 as).length+1))
    (hp:0 < pathMassDifferences (sampleClockSteps clock 0 as) 0 i) :
    finiteBoundaryClockCell clock as (physicalCutMass 0 (sampleClockSteps clock 0 as) i.val)=i := by
  apply Fin.ext
  have he:=retainedMassPrefixIndex_eq_of_positive_left_cut clock as ho i hp
  change finiteBoundaryMassIndex (physicalCutMass 0 (sampleClockSteps clock 0 as) i.val) as=i.val
  unfold finiteBoundaryMassIndex
  split_ifs with hz
  · rw [hz,retainedMassPrefixIndex_zero] at he
    exact he
  · exact he

theorem completeMassCapCells_sdiff_left_cut_mem {ι : Type}
    (clock : ℝ → ι → ℝ≥0) (D:Finset ℝ) (hD:∀d∈D,d∈Icc (0:ℝ) 1)
    (m:ℕ) {a b:ℝ} (ha:a∈D) (hb:b∈D)
    (i:Fin ((sampleClockSteps clock 0 (finiteCutMasses (finiteBoundaryMassNodes D) m)).length+1))
    (hi:i∈(completeMassCapCells (sampleClockSteps clock 0 (finiteCutMasses (finiteBoundaryMassNodes D) m)) a b)\
      fixedEndpointRows clock (finiteCutMasses (finiteBoundaryMassNodes D) m) D) :
    physicalCutMass 0 (sampleClockSteps clock 0 (finiteCutMasses (finiteBoundaryMassNodes D) m)) i.val∈Ioo a b := by
  let as:=finiteCutMasses (finiteBoundaryMassNodes D) m
  let steps:=sampleClockSteps clock 0 as
  have ho:MassOrdered 0 as := finiteCutMasses_ordered _
    (finiteBoundaryMassNodes_bound D (fun d hd => (hD d hd).2)) m
  have hs:OrderedSteps 0 steps:=sampleClockSteps_ordered clock as ho
  obtain ⟨hi,hB⟩:=Finset.mem_sdiff.mp hi
  obtain ⟨hp,hm⟩:0 < pathMassDifferences steps 0 i ∧ physicalCellMassMidpoint steps i∈Ioo a b := by
    simpa only [completeMassCapCells,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  have hlow:=finiteBoundaryMassIndex_exact clock D hD m ha
  have hhigh:=finiteBoundaryMassIndex_exact clock D hD m hb
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

theorem comparisonWholeCapBin_original_left_cut_mem {ι : Type}
    {c:ℝ} {k M:ℝ→ℝ} (hc:0<c) (hk:ContinuousOn k (Icc (0:ℝ) 1))
    (hkc:∀r∈Icc (0:ℝ) 1,c ≤ k r) (hm:MonotoneOn M (Icc (0:ℝ) 1)) (hM:0 ≤ M 1)
    (clock:ℝ→ι→ℝ≥0) (α:inverseIntegralConstraints 0 0 k M) {U:Set ℝ}
    (hopen:IsOpen U) (hU:U⊆Icc (0:ℝ) 1) (F:Finset (ordConnectedSection U))
    (S:ℝ→ℝ) (m bins:ℕ) (w:ℝ) {r:ordConnectedSection U} (hr:r∈F) :
    let q:=comparisonSweepQuantile hc hk hkc hm hM α
    let D:=comparisonWholeCapBinEndpointMasses hc hk hkc hm hM α U F S bins w
    let as:=finiteCutMasses (finiteBoundaryMassNodes D) m
    let steps:=sampleClockSteps clock 0 as
    let a:=α.val.val (sInf (ordConnectedComponent U r.val))
    let b:=α.val.val (sSup (ordConnectedComponent U r.val))
    ∀i∈(completeMassCapCells steps a b)\fixedEndpointRows clock as D,
      q (physicalCutMass 0 steps i.val)∈ordConnectedComponent U r.val := by
  dsimp only
  intro i hi
  have hrU:=ordConnectedSection_subset r.property
  obtain ⟨hlo,hlr,hrz,hhi,heq,_,_⟩:=wholeCap_component_endpoints hopen hU hrU
  have hla:sInf (ordConnectedComponent U r.val)∈Icc (0:ℝ) 1 :=
    ⟨hlo,hlr.le.trans (hU hrU).2⟩
  have hlb:sSup (ordConnectedComponent U r.val)∈Icc (0:ℝ) 1 :=
    ⟨(hU hrU).1.trans hrz.le,hhi⟩
  have hend:=comparisonWholeCapEndpointMasses_contains α U F hr
  have hleft:=completeMassCapCells_sdiff_left_cut_mem clock _
    (comparisonWholeCapBinEndpointMasses_bound hc hk hkc hm hM α U F S bins w) m
    (Finset.mem_union_left _ hend.1) (Finset.mem_union_left _ hend.2) i hi
  have hpre:=comparisonSweepQuantile_preimage_open_interval hc hk hkc hm hM α hla hlb
  rw [←hpre] at hleft
  rw [heq]
  exact hleft

theorem completeMassCapCells_sdiff_left_cut_bin_eq {ι : Type}
    (clock : ℝ → ι → ℝ≥0) (D:Finset ℝ) (hD:∀d∈D,d∈Icc (0:ℝ) 1)
    (m:ℕ) {a b:ℝ} (ha:a∈D) (hb:b∈D)
    {U:Set ℝ} {r:ℝ} (hr:r∈U) (hC:ordConnectedComponent U r=Ioo a b)
    (S:ℝ→ℝ) (bins:ℕ) (w:ℝ) :
    let as:=finiteCutMasses (finiteBoundaryMassNodes D) m
    let steps:=sampleClockSteps clock 0 as
    ∀i∈(completeMassCapCells steps a b)\fixedEndpointRows clock as D,
      capHeightBin U S bins w (physicalCutMass 0 steps i.val)=
        capHeightBin U S bins w (physicalCellMassMidpoint steps i) := by
  dsimp only
  intro i hi
  have hl:=completeMassCapCells_sdiff_left_cut_mem clock D hD m ha hb i hi
  have hm:=((Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2).2
  rw [←hC] at hl hm
  exact (capHeightBin_const_on_component U S bins w hr hl).trans
    (capHeightBin_const_on_component U S bins w hr hm).symm

end OAI.SKFluctuations.WholeUnitSideKernel
