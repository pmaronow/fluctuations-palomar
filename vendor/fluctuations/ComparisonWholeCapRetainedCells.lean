module

public import ComparisonFiniteWholeUnitPartition
public import RetainedWindowGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open Set Hierarchy LaplaceWindowFormalization
open scoped BigOperators NNReal
attribute [local instance] Classical.propDecidable

def physicalCellMassMidpoint {ι : Type} (steps : List (GaussianStep ι))
    (i : Fin (steps.length+1)) : ℝ :=
  (physicalCutMass 0 steps i.val+physicalCutMass 0 steps (i.val+1))/2

theorem physicalCellMassMidpoint_monotone {ι : Type}
    (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps) :
    Monotone (physicalCellMassMidpoint steps) := by
  intro i j hij
  have hl := physicalCutMass_monotone steps ha (show i.val ≤ j.val from hij)
  have hh := physicalCutMass_monotone steps ha (show i.val+1 ≤ j.val+1 by omega)
  unfold physicalCellMassMidpoint
  linarith

theorem physicalCellMassMidpoint_strict_inside {ι : Type}
    (steps : List (GaussianStep ι)) (i : Fin (steps.length+1))
    (hp : 0 < pathMassDifferences steps 0 i) :
    physicalCutMass 0 steps i.val < physicalCellMassMidpoint steps i ∧
      physicalCellMassMidpoint steps i < physicalCutMass 0 steps (i.val+1) := by
  rw [pathMassDifferences_eq_cutMass] at hp
  unfold physicalCellMassMidpoint
  constructor <;> linarith

theorem physicalCellMassMidpoint_mem_iff_interval {ι : Type}
    (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (p q : ℕ) (i : Fin (steps.length+1))
    (hp : 0 < pathMassDifferences steps 0 i) :
    physicalCellMassMidpoint steps i∈Ioo (physicalCutMass 0 steps p)
      (physicalCutMass 0 steps q) ↔ p ≤ i.val ∧ i.val < q := by
  have hmid := physicalCellMassMidpoint_strict_inside steps i hp
  constructor
  · intro hi
    constructor
    · by_contra hno
      have hle := physicalCutMass_monotone steps ha (show i.val+1 ≤ p by omega)
      exact (hi.1.trans hmid.2).not_ge hle
    · by_contra hno
      have hle := physicalCutMass_monotone steps ha (show q ≤ i.val by omega)
      exact (hmid.1.trans hi.2).not_ge hle
  · intro hi
    have hl := physicalCutMass_monotone steps ha hi.1
    have hh := physicalCutMass_monotone steps ha (show i.val+1 ≤ q by omega)
    exact ⟨hl.trans_lt hmid.1,hmid.2.trans_le hh⟩

def completeMassCapCells {ι : Type} (steps : List (GaussianStep ι))
    (a b : ℝ) : Finset (Fin (steps.length+1)) :=
  Finset.univ.filter (fun i => 0 < pathMassDifferences steps 0 i ∧
    physicalCellMassMidpoint steps i∈Ioo a b)

theorem completeMassCapCells_eq_positive_interval {ι : Type}
    (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps) (p q : ℕ) :
    completeMassCapCells steps (physicalCutMass 0 steps p) (physicalCutMass 0 steps q)=
      positiveSelectedCells steps (physicalIntervalCells steps p q) := by
  ext i
  simp only [completeMassCapCells,positiveSelectedCells,Finset.mem_filter,
    Finset.mem_univ,true_and,mem_physicalIntervalCells]
  constructor
  · intro hi
    exact ⟨(physicalCellMassMidpoint_mem_iff_interval steps ha p q i hi.1).mp hi.2,hi.1⟩
  · intro hi
    exact ⟨hi.2,(physicalCellMassMidpoint_mem_iff_interval steps ha p q i hi.2).mpr hi.1⟩

theorem completeMassCapCells_mass {ι : Type}
    (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps) {p q : ℕ}
    (hpq : p ≤ q) (hq : q ≤ steps.length+1) :
    physicalWindowMass steps 0
      (completeMassCapCells steps (physicalCutMass 0 steps p) (physicalCutMass 0 steps q))=
      physicalCutMass 0 steps q-physicalCutMass 0 steps p := by
  rw [completeMassCapCells_eq_positive_interval steps ha,
    positiveSelectedCells_mass steps ha,physicalIntervalMass steps 0 hpq hq]

theorem canonicalCompleteMassCapCells_mass {ι : Type} (clock : ℝ → ι → ℝ≥0)
    (us : List PositiveMass) (hu : ∀ u∈us,u.val ≤ 1)
    (a b : PositiveMass) (ha : a∈us) (hb : b∈us) (hab : a.val ≤ b.val) (m : ℕ) :
    let as := finiteCutMasses us m
    let steps := sampleClockSteps clock 0 as
    physicalWindowMass steps 0 (completeMassCapCells steps a.val b.val)=b.val-a.val := by
  dsimp only
  let as := finiteCutMasses us m
  have has := finiteCutMasses_ordered us hu m
  have han := finiteCutMasses_nodes us m ha
  have hbn := finiteCutMasses_nodes us m hb
  have hpq := retainedMassPrefixIndex_monotone as has a b han hbn hab
  have hq : retainedMassPrefixIndex b.val as ≤ (sampleClockSteps clock 0 as).length+1 := by
    rw [sampleClockSteps_length]
    exact (retainedMassPrefixIndex_le_length b.val as).trans (Nat.le_succ _)
  have hh := completeMassCapCells_mass (sampleClockSteps clock 0 as)
    (sampleClockSteps_ordered clock as has) hpq hq
  simpa only [physicalCutMass_retained_prefix clock as has a han,
    physicalCutMass_retained_prefix clock as has b hbn] using hh

end OAI.SKFluctuations.WholeUnitSideKernel
