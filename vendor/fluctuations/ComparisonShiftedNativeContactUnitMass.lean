module

public import ComparisonShiftedNativeMaskColumns
public import ComparisonNativeVarianceBinGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem sampled_contact_cap_unit_mass_le_mesh
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as)
    (H : ℝ→ℝ) {U : Set ℝ} (hopen : IsOpen U) (hU : U⊆Icc m.rmin 1)
    (hneg : ∀r ∈ U,H r<0) {K : ℕ}
    (A : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K)
    (hhigh : ∀j∈A,m.u0≤ physicalCutMass 0 (sampleClockSteps m.q 0 as) j.val)
    (hclass : ∀i ∈ A,∀j ∈ A,unit i=unit j↔
      wholeUnit U (m.R (physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val))=
      wholeUnit U (m.R (physicalCutMass 0 (sampleClockSteps m.q 0 as) j.val)))
    {i : Fin ((sampleClockSteps m.q 0 as).length+1)} (hi : i ∈ A)
    (hiU : m.R (physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val) ∈ U)
    (hmeet : ∀j ∈ A,unit j=unit i→∃t ∈ Icc
      (m.R (physicalCutMass 0 (sampleClockSteps m.q 0 as) j.val))
      (m.R (physicalCutMass 0 (sampleClockSteps m.q 0 as) (j.val+1))),H t=0) :
    physicalSelectedUnitMass (sampleClockSteps m.q 0 as) A unit (unit i) ≤ mesh := by
  let steps := sampleClockSteps m.q 0 as
  let ri := m.R (physicalCutMass 0 steps i.val)
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered m.q as ho
  obtain ⟨hlo,hls,hsz,hhi,heq,_,_⟩ := wholeCap_component_endpoints hopen
    hU hiU
  have haI : sInf (ordConnectedComponent U ri) ∈ Icc m.rmin 1 := ⟨hlo,by linarith⟩
  have hzI : sSup (ordConnectedComponent U ri) ∈ Icc m.rmin 1 := ⟨by linarith,hhi⟩
  have hstrict := inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property
  apply physicalSelectedUnitMass_le_mesh_of_straddling m.q as ho hmesh A unit (unit i)
    (m.alpha.val.val (sSup (ordConnectedComponent U ri)))
  intro j hj hji
  have heunit := (hclass i hi j hj).mp hji.symm
  have hjr : m.R (physicalCutMass 0 steps j.val) ∈
      ordConnectedComponent U ri := by
    have hmem := heunit.symm ▸ self_mem_wholeUnit U
      (m.R (physicalCutMass 0 steps j.val))
    simpa only [wholeUnit,ite_eq_left hiU] using hmem
  have hjI := heq ▸ hjr
  obtain ⟨t,ht,hzero⟩ := hmeet j hj hji
  have hzt : sSup (ordConnectedComponent U ri) ≤ t := by
    by_contra hno
    have htI : t ∈ Ioo (sInf (ordConnectedComponent U ri)) (sSup (ordConnectedComponent U ri)) :=
      ⟨hjI.1.trans_le ht.1,lt_of_not_ge hno⟩
    have hnt := hneg t (ordConnectedComponent_subset (heq.symm ▸ htI))
    rw [hzero] at hnt
    exact lt_irrefl _ hnt
  have hjrI := m.R_bounds (physicalCutMass 0 steps j.val)
  have hjnextI := m.R_bounds (physicalCutMass 0 steps (j.val+1))
  have hs1 := m.R_spec ⟨hhigh j hj,(physicalCutMass_mem steps hs j.val).2⟩
  have hs2 := m.R_spec ⟨(hhigh j hj).trans (physicalCutMass_monotone steps hs (Nat.le_succ j.val)),(physicalCutMass_mem steps hs (j.val+1)).2⟩
  constructor
  · rw [←hs1]
    exact hstrict hjrI hzI hjI.2
  · rw [←hs2]
    exact hstrict.monotoneOn hzI hjnextI (hzt.trans ht.2)

theorem sampled_contact_unit_mass_le_mesh
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as)
    (U : Set ℝ) {K : ℕ}
    (A : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K)
    (hhigh : ∀j∈A,m.u0≤ physicalCutMass 0 (sampleClockSteps m.q 0 as) j.val)
    (hpos : ∀i ∈ A,0< pathMassDifferences (sampleClockSteps m.q 0 as) 0 i)
    (hclass : ∀i ∈ A,∀j ∈ A,unit i=unit j↔
      wholeUnit U (m.R (physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val))=
      wholeUnit U (m.R (physicalCutMass 0 (sampleClockSteps m.q 0 as) j.val)))
    {i : Fin ((sampleClockSteps m.q 0 as).length+1)} (hi : i ∈ A)
    (hiU : m.R (physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val) ∉ U) :
    physicalSelectedUnitMass (sampleClockSteps m.q 0 as) A unit (unit i) ≤ mesh := by
  let steps := sampleClockSteps m.q 0 as
  have hs : OrderedSteps 0 steps := sampleClockSteps_ordered m.q as ho
  have hcstrict := physicalCutMass_strictOn_positive_selected steps hs A hpos
  have heunit (j : Fin (steps.length+1)) (hj : j ∈ A) (hji : unit j=unit i) : j=i := by
    have he := (hclass i hi j hj).mp hji.symm
    have hmem := he.symm ▸ self_mem_wholeUnit U
      (m.R (physicalCutMass 0 steps j.val))
    have hr : m.R (physicalCutMass 0 steps j.val)=
        m.R (physicalCutMass 0 steps i.val) := by
      simpa only [wholeUnit,ite_eq_right hiU,Set.mem_singleton_iff] using hmem
    have hmassEq := congrArg m.alpha.val.val hr
    rw [m.R_spec ⟨hhigh j hj,(physicalCutMass_mem steps hs j.val).2⟩,
      m.R_spec ⟨hhigh i hi,(physicalCutMass_mem steps hs i.val).2⟩] at hmassEq
    exact hcstrict.injOn hj hi hmassEq
  have he : physicalSelectedUnitMass steps A unit (unit i)=pathMassDifferences steps 0 i := by
    unfold physicalSelectedUnitMass
    rw [Finset.sum_eq_single i]
    · simp only [hi,and_self,ite_true]
    · intro j hj hji
      have hn : ¬(j ∈ A ∧ unit j=unit i) := fun h=>hji (heunit j h.1 h.2)
      simp only [hn,ite_false]
    · simp
  rw [he,pathMassDifferences_eq_cutMass]
  exact sampled_physicalMass_mesh m.q as hmesh i

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
