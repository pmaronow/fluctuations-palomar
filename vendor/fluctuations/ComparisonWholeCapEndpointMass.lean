module

public import ComparisonWholeCapPhysicalMass
public import ComparisonWholeCapRetainedCells

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open Set MeasureTheory LaplaceWindowFormalization Hierarchy
open scoped BigOperators NNReal ENNReal
attribute [local instance] Classical.propDecidable
attribute [local instance] Measure.Subtype.measureSpace

section
variable {c : ℝ} {k M : ℝ → ℝ} (hc : 0<c)
    (hk : ContinuousOn k (Icc (0:ℝ) 1)) (hkc : ∀ r∈Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem wholeCap_actual_comparison_mass_singleton (α : inverseIntegralConstraints 0 0 k M)
    (r : ℝ) :
    wholeCapRadiusMass (comparisonSweepQuantile hc hk hkc hm hM α)
      (fun u _ => comparisonSweepQuantile_bounds hc hk hkc hm hM α u) {r}=0 := by
  rw [wholeCapRadiusMass_apply _
    ((comparisonSweepQuantile_monotone hc hk hkc hm hM α).monotoneOn _)
    _ (measurableSet_singleton r)]
  let u : ParisiFinite.OrderPoint := ⟨α.val.val r,α.val.property.1 r⟩
  have hsub : {t:ParisiFinite.OrderPoint | comparisonSweepQuantile hc hk hkc hm hM α t∈({r}:Set ℝ)}⊆{u} := by
    intro t ht
    have he : comparisonSweepQuantile hc hk hkc hm hM α t=r := Set.mem_singleton_iff.mp ht
    have hs := comparisonSweepQuantile_spec hc hk hkc hm hM α t.property
    rw [he] at hs
    exact Set.mem_singleton_iff.mpr (Subtype.ext hs.symm)
  apply le_antisymm ((measure_mono hsub).trans_eq ?_) zero_le
  change volume {u}=0
  exact measure_singleton u

theorem wholeCap_actual_comparison_mass_Ioo (α : inverseIntegralConstraints 0 0 k M)
    {a b : ℝ} (hab : a<b) :
    (wholeCapRadiusMass (comparisonSweepQuantile hc hk hkc hm hM α)
      (fun u _ => comparisonSweepQuantile_bounds hc hk hkc hm hM α u)).real (Ioo a b)=
      α.val.val b-α.val.val a := by
  have he : Ioc a b\{b}=Ioo a b := by
    ext r
    simp only [mem_sdiff,mem_Ioc,mem_singleton_iff,mem_Ioo]
    constructor
    · rintro ⟨⟨har,hrb⟩,hne⟩
      exact ⟨har,lt_of_le_of_ne hrb hne⟩
    · intro hr
      exact ⟨⟨hr.1,hr.2.le⟩,hr.2.ne⟩
  rw [←he,measureReal_sdiff (by simpa only [singleton_subset_iff,mem_Ioc] using
    (show a<b ∧ b ≤ b from ⟨hab,le_rfl⟩)) (measurableSet_singleton b),
    wholeCap_actual_comparison_mass_Ioc hc hk hkc hm hM α hab.le]
  have hz := wholeCap_actual_comparison_mass_singleton hc hk hkc hm hM α b
  simp only [Measure.real,hz,ENNReal.toReal_zero,sub_zero]

end

def finiteBoundaryMassNodes (D : Finset ℝ) : List PositiveMass :=
  (D.filter (fun d => 0<d)).attach.toList.map (fun d =>
    ⟨d.val,(Finset.mem_filter.mp d.property).2⟩)

theorem finiteBoundaryMassNodes_bound (D : Finset ℝ)
    (hD : ∀d∈D,d ≤ 1) : ∀d∈finiteBoundaryMassNodes D,d.val ≤ 1 := by
  intro d hd
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hd
  exact hD z.val (Finset.mem_filter.mp z.property).1

theorem finiteBoundaryMassNodes_mem (D : Finset ℝ) {d : ℝ} (hd:d∈D) (hp:0<d) :
    (⟨d,hp⟩:PositiveMass)∈finiteBoundaryMassNodes D := by
  apply List.mem_map.mpr
  refine ⟨⟨d,Finset.mem_filter.mpr ⟨hd,hp⟩⟩,?_,?_⟩
  · simp
  · rfl

def finiteBoundaryMassIndex (d : ℝ) (as : List PositiveMass) : ℕ :=
  if d=0 then 0 else retainedMassPrefixIndex d as

theorem finiteBoundaryMassIndex_exact {ι : Type} (clock : ℝ → ι → ℝ≥0)
    (D : Finset ℝ) (hD : ∀d∈D,d∈Icc (0:ℝ) 1) (m : ℕ) {d : ℝ} (hd:d∈D) :
    let as := finiteCutMasses (finiteBoundaryMassNodes D) m
    physicalCutMass 0 (sampleClockSteps clock 0 as) (finiteBoundaryMassIndex d as)=d := by
  dsimp only
  by_cases hz:d=0
  · simp [finiteBoundaryMassIndex,hz,physicalCutMass]
  · have hp : 0<d := lt_of_le_of_ne (hD d hd).1 (Ne.symm hz)
    have hbound := finiteBoundaryMassNodes_bound D (fun d hd => (hD d hd).2)
    have hnode := finiteCutMasses_nodes (finiteBoundaryMassNodes D) m
      (finiteBoundaryMassNodes_mem D hd hp)
    simpa only [finiteBoundaryMassIndex,hz,ite_false] using
      physicalCutMass_retained_prefix clock _
        (finiteCutMasses_ordered _ hbound m) ⟨d,hp⟩ hnode

theorem finiteBoundaryMass_complete_cap_mass {ι : Type} (clock : ℝ → ι → ℝ≥0)
    (D : Finset ℝ) (hD : ∀d∈D,d∈Icc (0:ℝ) 1) (m : ℕ)
    {a b : ℝ} (ha:a∈D) (hb:b∈D) (hab:a<b) :
    let as := finiteCutMasses (finiteBoundaryMassNodes D) m
    let steps := sampleClockSteps clock 0 as
    physicalWindowMass steps 0 (completeMassCapCells steps a b)=b-a := by
  dsimp only
  let as := finiteCutMasses (finiteBoundaryMassNodes D) m
  let steps := sampleClockSteps clock 0 as
  have hbound := finiteBoundaryMassNodes_bound D (fun d hd => (hD d hd).2)
  have ho : OrderedSteps 0 steps := sampleClockSteps_ordered clock as
    (finiteCutMasses_ordered _ hbound m)
  have hea := finiteBoundaryMassIndex_exact clock D hD m ha
  have heb := finiteBoundaryMassIndex_exact clock D hD m hb
  change physicalCutMass 0 steps (finiteBoundaryMassIndex a as)=a at hea
  change physicalCutMass 0 steps (finiteBoundaryMassIndex b as)=b at heb
  have hpq : finiteBoundaryMassIndex a as ≤ finiteBoundaryMassIndex b as := by
    by_contra hno
    have hh := physicalCutMass_monotone steps ho (lt_of_not_ge hno).le
    rw [hea,heb] at hh
    exact hab.not_ge hh
  have hq : finiteBoundaryMassIndex b as ≤ steps.length+1 := by
    unfold finiteBoundaryMassIndex
    split_ifs
    · omega
    · change retainedMassPrefixIndex b as ≤ (sampleClockSteps clock 0 as).length+1
      rw [sampleClockSteps_length]
      exact (retainedMassPrefixIndex_le_length b as).trans (Nat.le_succ _)
  have hh := completeMassCapCells_mass steps ho hpq hq
  simpa only [hea,heb] using hh

end OAI.SKFluctuations.WholeUnitSideKernel
