module

public import RetainedMassSubgrid
public import PhysicalBPathLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Filter Set
open scoped NNReal Topology

theorem canonicalRetainedMass_three_ordered (us : List PositiveMass)
    (hu : ∀ u ∈ us, u.val≤1) (a c : PositiveMass) (ha : a∈us) (hc : c∈us)
    (hac : a.val<c.val) (k : ℕ) :
    let as := finiteCutMasses us k
    MassOrdered 0 (retainedMassBefore a.val as) ∧
    MassOrdered a.val (retainedMassBand a.val c.val as) ∧
    MassOrdered c.val (retainedMassTail a.val c.val as) ∧
    partitionEnd 0 (retainedMassBefore a.val as)=a.val ∧
    partitionEnd a.val (retainedMassBand a.val c.val as)=c.val :=
  retainedMass_three_ordered _ (finiteCutMasses_ordered us hu k) a c
    (finiteCutMasses_nodes us k ha) (finiteCutMasses_nodes us k hc) hac

theorem canonicalRetainedMass_three_sampleClockSteps {ι : Type*}
    (q : ℝ → ι → ℝ≥0) (us : List PositiveMass) (hu : ∀ u ∈ us, u.val≤1)
    (a c : PositiveMass) (ha : a∈us) (hc : c∈us) (hac : a.val<c.val) (k : ℕ) :
    let as := finiteCutMasses us k
    sampleClockSteps q 0 (retainedMassBefore a.val as) ++
      sampleClockSteps q a.val (retainedMassBand a.val c.val as) ++
      sampleClockSteps q c.val (retainedMassTail a.val c.val as)=sampleClockSteps q 0 as :=
  retainedMass_three_sampleClockSteps q _ (finiteCutMasses_ordered us hu k) a c
    (finiteCutMasses_nodes us k ha) (finiteCutMasses_nodes us k hc) hac

theorem canonicalRetainedMassBand_duration_mesh (us : List PositiveMass)
    (hu : ∀ u ∈ us, u.val≤1) (a : PositiveMass) (ha : a∈us) (c : ℝ) (k : ℕ) :
    ∀ (w:ℝ≥0), w∈sampleMassDurations a.val (retainedMassBand a.val c (finiteCutMasses us k)) →
      (w:ℝ) ≤ (((k+1:ℕ):ℝ))⁻¹ :=
  retainedMassBand_duration_mesh _ (finiteCutMasses_ordered us hu k)
    (finiteCutMasses_mesh us hu k) a (finiteCutMasses_nodes us k ha) c

theorem canonicalRetainedMass_later_splitClockSteps_length {ι : Type*}
    (q : ℝ → ι → ℝ≥0) (us : List PositiveMass) (hu : ∀ u ∈ us, u.val≤1)
    (a c : PositiveMass) (ha : a∈us) (hc : c∈us) (hac : a.val≤c.val) (k : ℕ) :
    (splitClockSteps c.val (sampleClockSteps q 0 (finiteCutMasses us k))).1.length=
      (retainedMassBefore a.val (finiteCutMasses us k)).length+
        (retainedMassBand a.val c.val (finiteCutMasses us k)).length :=
  retainedMass_later_splitClockSteps_length q _ (finiteCutMasses_ordered us hu k) a c
    (finiteCutMasses_nodes us k ha) (finiteCutMasses_nodes us k hc) hac

end OAI.SKFluctuations.LaplaceWindowFormalization
