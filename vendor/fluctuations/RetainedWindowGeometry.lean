module

public import RetainedThreeCuts
public import PhysicalWindowTraceAggregation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Hierarchy
open scoped NNReal

def retainedMassPrefixIndex (u : ℝ) (as : List PositiveMass) : ℕ :=
  (retainedMassBefore u as).length

theorem retainedMassPrefixIndex_le_length (u : ℝ) (as : List PositiveMass) :
    retainedMassPrefixIndex u as≤as.length := by
  have h := congrArg List.length (retainedMass_append u as)
  simp only [List.length_append] at h
  dsimp [retainedMassPrefixIndex]
  omega

theorem retainedMassPrefixIndex_monotone {start : ℝ} (as : List PositiveMass)
    (ho : MassOrdered start as) (a b : PositiveMass) (ha : a∈as) (hb : b∈as)
    (hab : a.val≤b.val) : retainedMassPrefixIndex a.val as≤retainedMassPrefixIndex b.val as := by
  have h := congrArg List.length (retainedMass_later_prefix as ho a b ha hb hab)
  simp only [List.length_append] at h
  dsimp [retainedMassPrefixIndex]
  omega

theorem physicalCutMass_retained_prefix {ι : Type} (q : ℝ → ι → ℝ≥0)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (u : PositiveMass) (hu : u∈as) :
    physicalCutMass 0 (sampleClockSteps q 0 as) (retainedMassPrefixIndex u.val as)=u.val := by
  rw [← retainedMass_sampleClockSteps_append q as ho u hu]
  dsimp [retainedMassPrefixIndex]
  rw [physicalCutMass_append_prefix _ _ 0 _ (by simp only [sampleClockSteps_length]; exact le_rfl),
    physicalCutMass_sampleClockSteps q 0 (retainedMassBefore u.val as) _ le_rfl,
    physicalPartitionPoint_length,retainedMass_endpoint as ho u hu]

theorem physicalRetainedWindow_geometry {ι : Type} (q : ℝ → ι → ℝ≥0)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (a b : PositiveMass)
    (ha : a∈as) (hb : b∈as) (hab : a.val≤b.val) :
    let steps := sampleClockSteps q 0 as
    let J := physicalIntervalCells steps (retainedMassPrefixIndex a.val as)
      (retainedMassPrefixIndex b.val as)
    physicalWindowMass steps 0 J=b.val-a.val ∧
    (∀ j∈J, a.val≤physicalCutMass 0 steps j.val ∧ physicalCutMass 0 steps j.val≤b.val) := by
  dsimp only
  have hip := retainedMassPrefixIndex_monotone as ho a b ha hb hab
  have hib : retainedMassPrefixIndex b.val as≤(sampleClockSteps q 0 as).length+1 := by
    rw [sampleClockSteps_length]
    exact (retainedMassPrefixIndex_le_length b.val as).trans (Nat.le_succ _)
  refine ⟨?_,?_⟩
  · rw [physicalIntervalMass _ 0 hip hib,
      physicalCutMass_retained_prefix q as ho b hb,physicalCutMass_retained_prefix q as ho a ha]
  · intro j hj
    have hh := (mem_physicalIntervalCells _ _ _ j).mp hj
    have hl := physicalCutMass_monotone _ (sampleClockSteps_ordered q as ho) hh.1
    have hu := physicalCutMass_monotone _ (sampleClockSteps_ordered q as ho) hh.2.le
    rw [physicalCutMass_retained_prefix q as ho a ha] at hl
    rw [physicalCutMass_retained_prefix q as ho b hb] at hu
    exact ⟨hl,hu⟩

theorem physicalRetainedPastFuture_bracket {ι : Type} (q : ℝ → ι → ℝ≥0)
    (as : List PositiveMass) (a b c d : ℝ) (cut : ℕ)
    (hcutLeft : retainedMassPrefixIndex b as≤cut)
    (hcutRight : cut≤retainedMassPrefixIndex c as) :
    (∀ j∈physicalIntervalCells (sampleClockSteps q 0 as)
      (retainedMassPrefixIndex a as) (retainedMassPrefixIndex b as), j.val≤cut) ∧
    (∀ j∈physicalIntervalCells (sampleClockSteps q 0 as)
      (retainedMassPrefixIndex c as) (retainedMassPrefixIndex d as), cut≤j.val) := by
  constructor
  · intro j hj
    exact ((mem_physicalIntervalCells _ _ _ j).mp hj).2.le.trans hcutLeft
  · intro j hj
    exact hcutRight.trans ((mem_physicalIntervalCells _ _ _ j).mp hj).1

theorem canonicalRetainedWindow_geometry {ι : Type} (q : ℝ → ι → ℝ≥0)
    (us : List PositiveMass) (hu : ∀ u∈us, u.val≤1)
    (a b : PositiveMass) (ha : a∈us) (hb : b∈us) (hab : a.val≤b.val) (k:ℕ) :
    let as := finiteCutMasses us k
    let steps := sampleClockSteps q 0 as
    let J := physicalIntervalCells steps (retainedMassPrefixIndex a.val as)
      (retainedMassPrefixIndex b.val as)
    physicalWindowMass steps 0 J=b.val-a.val ∧
    (∀ j∈J, a.val≤physicalCutMass 0 steps j.val ∧ physicalCutMass 0 steps j.val≤b.val) :=
  physicalRetainedWindow_geometry q _ (finiteCutMasses_ordered us hu k) a b
    (finiteCutMasses_nodes us k ha) (finiteCutMasses_nodes us k hb) hab

end OAI.SKFluctuations.LaplaceWindowFormalization
