module

public import CanonicalRetainedMassSubgrid

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Hierarchy
open scoped NNReal

theorem retainedMass_four_append (a b c : ℝ) (as : List PositiveMass) :
    retainedMassBefore a as ++ retainedMassBand a b as ++
      retainedMassBand b c (retainedMassAfter a as) ++
      retainedMassTail b c (retainedMassAfter a as)=as := by
  calc
    _ = retainedMassBefore a as ++ retainedMassAfter a as := by
      simpa only [retainedMassBand, List.append_assoc] using
        congrArg (fun l => retainedMassBefore a as ++ l)
          (retainedMass_three_append b c (retainedMassAfter a as))
    _ = as := retainedMass_append a as

theorem retainedMass_four_ordered {start : ℝ} (as : List PositiveMass) (ho : MassOrdered start as)
    (a b c : PositiveMass) (ha : a∈as) (hb : b∈as) (hc : c∈as)
    (hab : a.val<b.val) (hbc : b.val<c.val) :
    MassOrdered start (retainedMassBefore a.val as) ∧
    MassOrdered a.val (retainedMassBand a.val b.val as) ∧
    MassOrdered b.val (retainedMassBand b.val c.val (retainedMassAfter a.val as)) ∧
    MassOrdered c.val (retainedMassTail b.val c.val (retainedMassAfter a.val as)) ∧
    partitionEnd start (retainedMassBefore a.val as)=a.val ∧
    partitionEnd a.val (retainedMassBand a.val b.val as)=b.val ∧
    partitionEnd b.val (retainedMassBand b.val c.val (retainedMassAfter a.val as))=c.val := by
  have hua : a.val ∈ Icc (0:ℝ) 1 :=
    ⟨a.2.le,(massOrdered_mem_le_end as ho ha).trans ho.end_bounds.2⟩
  obtain ⟨hbefore,hrest,_,_⟩ := retainedMass_ordered as ho hua (ho.le_of_mem ha)
  have hblater := retainedMass_later_mem as ho a b ha hb hab
  have hclater := retainedMass_later_mem as ho a c ha hc (hab.trans hbc)
  obtain ⟨htarget,hfuture,htail,hendb,hendc⟩ :=
    retainedMass_three_ordered (retainedMassAfter a.val as) hrest b c hblater hclater hbc
  exact ⟨hbefore,htarget,hfuture,htail,retainedMass_endpoint as ho a ha,hendb,hendc⟩

theorem retainedMass_four_splitClockSteps_length {ι : Type*} (q : ℝ → ι → ℝ≥0)
    {start : ℝ} (as : List PositiveMass) (ho : MassOrdered start as)
    (a b c : PositiveMass) (ha : a∈as) (hb : b∈as) (hc : c∈as)
    (hab : a.val<b.val) (hbc : b.val<c.val) :
    (splitClockSteps c.val (sampleClockSteps q start as)).1.length=
      (retainedMassBefore a.val as).length+(retainedMassBand a.val b.val as).length+
      (retainedMassBand b.val c.val (retainedMassAfter a.val as)).length := by
  have hua : a.val ∈ Icc (0:ℝ) 1 :=
    ⟨a.2.le,(massOrdered_mem_le_end as ho ha).trans ho.end_bounds.2⟩
  have hrest := (retainedMass_ordered as ho hua (ho.le_of_mem ha)).2.1
  have hblater := retainedMass_later_mem as ho a b ha hb hab
  have hclater := retainedMass_later_mem as ho a c ha hc (hab.trans hbc)
  rw [retainedMass_splitClockSteps_length,retainedMass_later_prefix as ho a c ha hc (hab.trans hbc).le]
  unfold retainedMassBand
  rw [retainedMass_later_prefix (retainedMassAfter a.val as) hrest b c hblater hclater hbc.le,
    List.length_append,List.length_append]
  simp only [retainedMassBand]
  omega

theorem retainedMass_four_duration_mesh {start mesh : ℝ} (as : List PositiveMass)
    (ho : MassOrdered start as) (hm : PartitionMesh mesh start as)
    (a b c : PositiveMass) (ha : a∈as) (hb : b∈as) (hc : c∈as)
    (hab : a.val<b.val) (hbc : b.val<c.val) :
    (∀ (w:ℝ≥0), w∈sampleMassDurations a.val (retainedMassBand a.val b.val as) → (w:ℝ) ≤ mesh) ∧
    (∀ (w:ℝ≥0), w∈sampleMassDurations b.val
      (retainedMassBand b.val c.val (retainedMassAfter a.val as)) → (w:ℝ) ≤ mesh) := by
  refine ⟨retainedMassBand_duration_mesh as ho hm a ha b.val,?_⟩
  have he := retainedMass_four_append a.val b.val c.val as
  obtain ⟨_,_,_,_,hea,heb,_⟩ := retainedMass_four_ordered as ho a b c ha hb hc hab hbc
  have hend : partitionEnd start (retainedMassBefore a.val as++retainedMassBand a.val b.val as)=b.val := by
    rw [partitionEnd_append,hea,heb]
  have he' : ((retainedMassBefore a.val as++retainedMassBand a.val b.val as) ++
      retainedMassBand b.val c.val (retainedMassAfter a.val as)) ++
      retainedMassTail b.val c.val (retainedMassAfter a.val as)=as := he
  exact sampleMassDurations_internal_mesh _ _ _ (he'.symm ▸ ho) (he'.symm ▸ hm) hend

theorem retainedMass_four_sampleClockSteps {ι : Type*} (q : ℝ → ι → ℝ≥0)
    {start : ℝ} (as : List PositiveMass) (ho : MassOrdered start as)
    (a b c : PositiveMass) (ha : a∈as) (hb : b∈as) (hc : c∈as)
    (hab : a.val<b.val) (hbc : b.val<c.val) :
    sampleClockSteps q start (retainedMassBefore a.val as) ++
      sampleClockSteps q a.val (retainedMassBand a.val b.val as) ++
      sampleClockSteps q b.val (retainedMassBand b.val c.val (retainedMassAfter a.val as)) ++
      sampleClockSteps q c.val (retainedMassTail b.val c.val (retainedMassAfter a.val as)) =
      sampleClockSteps q start as := by
  have hua : a.val ∈ Icc (0:ℝ) 1 :=
    ⟨a.2.le,(massOrdered_mem_le_end as ho ha).trans ho.end_bounds.2⟩
  have hrest := (retainedMass_ordered as ho hua (ho.le_of_mem ha)).2.1
  have hblater := retainedMass_later_mem as ho a b ha hb hab
  have hclater := retainedMass_later_mem as ho a c ha hc (hab.trans hbc)
  calc
    _ = sampleClockSteps q start (retainedMassBefore a.val as) ++
        sampleClockSteps q a.val (retainedMassAfter a.val as) := by
      simpa only [retainedMassBand, List.append_assoc] using
        congrArg (fun l => sampleClockSteps q start (retainedMassBefore a.val as) ++ l)
          (retainedMass_three_sampleClockSteps q (retainedMassAfter a.val as) hrest
            b c hblater hclater hbc)
    _ = sampleClockSteps q start as :=
      retainedMass_sampleClockSteps_append q as ho a ha

theorem canonicalRetainedMass_four_ordered (us : List PositiveMass)
    (hu : ∀ u ∈ us, u.val≤1) (a b c : PositiveMass) (ha : a∈us) (hb : b∈us) (hc : c∈us)
    (hab : a.val<b.val) (hbc : b.val<c.val) (k : ℕ) :
    let as := finiteCutMasses us k
    MassOrdered 0 (retainedMassBefore a.val as) ∧
    MassOrdered a.val (retainedMassBand a.val b.val as) ∧
    MassOrdered b.val (retainedMassBand b.val c.val (retainedMassAfter a.val as)) ∧
    MassOrdered c.val (retainedMassTail b.val c.val (retainedMassAfter a.val as)) ∧
    partitionEnd 0 (retainedMassBefore a.val as)=a.val ∧
    partitionEnd a.val (retainedMassBand a.val b.val as)=b.val ∧
    partitionEnd b.val (retainedMassBand b.val c.val (retainedMassAfter a.val as))=c.val :=
  retainedMass_four_ordered _ (finiteCutMasses_ordered us hu k) a b c
    (finiteCutMasses_nodes us k ha) (finiteCutMasses_nodes us k hb) (finiteCutMasses_nodes us k hc) hab hbc

theorem canonicalRetainedMass_four_sampleClockSteps {ι : Type*} (q : ℝ → ι → ℝ≥0)
    (us : List PositiveMass) (hu : ∀ u ∈ us, u.val≤1)
    (a b c : PositiveMass) (ha : a∈us) (hb : b∈us) (hc : c∈us)
    (hab : a.val<b.val) (hbc : b.val<c.val) (k : ℕ) :
    let as := finiteCutMasses us k
    sampleClockSteps q 0 (retainedMassBefore a.val as) ++
      sampleClockSteps q a.val (retainedMassBand a.val b.val as) ++
      sampleClockSteps q b.val (retainedMassBand b.val c.val (retainedMassAfter a.val as)) ++
      sampleClockSteps q c.val (retainedMassTail b.val c.val (retainedMassAfter a.val as)) =
      sampleClockSteps q 0 as :=
  retainedMass_four_sampleClockSteps q _ (finiteCutMasses_ordered us hu k) a b c
    (finiteCutMasses_nodes us k ha) (finiteCutMasses_nodes us k hb) (finiteCutMasses_nodes us k hc) hab hbc

theorem canonicalRetainedMass_four_splitClockSteps_length {ι : Type*} (q : ℝ → ι → ℝ≥0)
    (us : List PositiveMass) (hu : ∀ u ∈ us, u.val≤1)
    (a b c : PositiveMass) (ha : a∈us) (hb : b∈us) (hc : c∈us)
    (hab : a.val<b.val) (hbc : b.val<c.val) (k : ℕ) :
    let as := finiteCutMasses us k
    (splitClockSteps c.val (sampleClockSteps q 0 as)).1.length=
      (retainedMassBefore a.val as).length+(retainedMassBand a.val b.val as).length+
      (retainedMassBand b.val c.val (retainedMassAfter a.val as)).length :=
  retainedMass_four_splitClockSteps_length q _ (finiteCutMasses_ordered us hu k) a b c
    (finiteCutMasses_nodes us k ha) (finiteCutMasses_nodes us k hb) (finiteCutMasses_nodes us k hc) hab hbc

end OAI.SKFluctuations.LaplaceWindowFormalization
