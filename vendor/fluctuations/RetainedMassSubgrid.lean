module

public import MassDurationSubgrid
public import FiniteMassBandIntegral

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Hierarchy
open scoped NNReal
attribute [local instance] Classical.propDecidable

def retainedMassBefore (u : ℝ) (as : List PositiveMass) : List PositiveMass :=
  as.takeWhile (fun b => decide (b.val≤u))

def retainedMassAfter (u : ℝ) (as : List PositiveMass) : List PositiveMass :=
  as.dropWhile (fun b => decide (b.val≤u))

theorem retainedMass_append (u : ℝ) (as : List PositiveMass) :
    retainedMassBefore u as ++ retainedMassAfter u as=as :=
  List.takeWhile_append_dropWhile

theorem retainedMassBefore_cons_le {u : ℝ} (b : PositiveMass) (bs : List PositiveMass)
    (hb : b.val≤u) : retainedMassBefore u (b::bs)=b::retainedMassBefore u bs := by
  simp [retainedMassBefore,List.takeWhile,hb]

theorem retainedMassBefore_cons_gt {u : ℝ} (b : PositiveMass) (bs : List PositiveMass)
    (hb : ¬b.val≤u) : retainedMassBefore u (b::bs)=[] := by
  simp [retainedMassBefore,List.takeWhile,hb]

theorem retainedMassAfter_cons_le {u : ℝ} (b : PositiveMass) (bs : List PositiveMass)
    (hb : b.val≤u) : retainedMassAfter u (b::bs)=retainedMassAfter u bs := by
  simp [retainedMassAfter,List.dropWhile,hb]

theorem retainedMassAfter_cons_gt {u : ℝ} (b : PositiveMass) (bs : List PositiveMass)
    (hb : ¬b.val≤u) : retainedMassAfter u (b::bs)=b::bs := by
  simp [retainedMassAfter,List.dropWhile,hb]

theorem retainedMass_ordered {a u : ℝ} (as : List PositiveMass)
    (ho : MassOrdered a as) (hu : u ∈ Icc (0:ℝ) 1) (hau : a≤u) :
    MassOrdered a (retainedMassBefore u as) ∧ MassOrdered u (retainedMassAfter u as) ∧
      (∀ b ∈ retainedMassBefore u as, b.val≤u) ∧
      (∀ b ∈ retainedMassAfter u as, u<b.val) := by
  induction as generalizing a with
  | nil => exact ⟨ho,hu,by simp [retainedMassBefore],by simp [retainedMassAfter]⟩
  | cons b bs ih =>
    by_cases hb : b.val≤u
    · rw [retainedMassBefore_cons_le b bs hb,retainedMassAfter_cons_le b bs hb]
      obtain ⟨hp,hq,hl,hr⟩ := ih ho.2.2 hb
      refine ⟨⟨ho.1,ho.2.1,hp⟩,hq,?_,hr⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl|hc
      · exact hb
      · exact hl c hc
    · rw [retainedMassBefore_cons_gt b bs hb,retainedMassAfter_cons_gt b bs hb]
      refine ⟨⟨ho.1,hau.trans hu.2⟩,⟨hu.1,(lt_of_not_ge hb).le,ho.2.2⟩,by simp,?_⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl|hc
      · exact lt_of_not_ge hb
      · exact (lt_of_not_ge hb).trans_le (ho.2.2.le_of_mem hc)

theorem partitionEnd_le_of_nodes {a u : ℝ} (as : List PositiveMass)
    (hau : a≤u) (hnodes : ∀ b ∈ as, b.val≤u) : partitionEnd a as≤u := by
  induction as generalizing a with
  | nil => exact hau
  | cons b bs ih =>
    exact ih (hnodes b List.mem_cons_self)
      (fun c hc => hnodes c (List.mem_cons_of_mem b hc))

theorem retainedMass_endpoint {a : ℝ} (as : List PositiveMass)
    (ho : MassOrdered a as) (u : PositiveMass) (hnode : u∈as) :
    partitionEnd a (retainedMassBefore u.val as)=u.val := by
  have hu : u.val ∈ Icc (0:ℝ) 1 :=
    ⟨u.2.le,(massOrdered_mem_le_end as ho hnode).trans ho.end_bounds.2⟩
  have hau := ho.le_of_mem hnode
  obtain ⟨hp,hq,hl,hr⟩ := retainedMass_ordered as ho hu hau
  have hmem : u∈retainedMassBefore u.val as := by
    rw [← retainedMass_append u.val as] at hnode
    rcases List.mem_append.mp hnode with hnode|hnode
    · exact hnode
    · exact False.elim (lt_irrefl u.val (hr u hnode))
  exact le_antisymm (partitionEnd_le_of_nodes _ hau hl) (massOrdered_mem_le_end _ hp hmem)

theorem retainedMass_splitClockSteps {ι : Type*} (q : ℝ → ι → ℝ≥0)
    (a u : ℝ) (as : List PositiveMass) :
    splitClockSteps u (sampleClockSteps q a as) =
      (sampleClockSteps q a (retainedMassBefore u as),
       sampleClockSteps q (partitionEnd a (retainedMassBefore u as)) (retainedMassAfter u as)) := by
  induction as generalizing a with
  | nil => rfl
  | cons b bs ih =>
    by_cases hb : b.val≤u
    · simp only [sampleClockSteps,splitClockSteps,ite_eq_left hb,retainedMassBefore_cons_le b bs hb,
        retainedMassAfter_cons_le b bs hb,partitionEnd,ih]
    · simp only [sampleClockSteps,splitClockSteps,ite_eq_right hb,retainedMassBefore_cons_gt b bs hb,
        retainedMassAfter_cons_gt b bs hb,partitionEnd]

theorem retainedMass_splitClockSteps_length {ι : Type*} (q : ℝ → ι → ℝ≥0)
    (a u : ℝ) (as : List PositiveMass) :
    (splitClockSteps u (sampleClockSteps q a as)).1.length=(retainedMassBefore u as).length := by
  rw [retainedMass_splitClockSteps]
  exact sampleClockSteps_length q a _

theorem retainedMass_sampleClockSteps_append {ι : Type*} (q : ℝ → ι → ℝ≥0)
    {a : ℝ} (as : List PositiveMass) (ho : MassOrdered a as)
    (u : PositiveMass) (hnode : u∈as) :
    sampleClockSteps q a (retainedMassBefore u.val as) ++
      sampleClockSteps q u.val (retainedMassAfter u.val as)=sampleClockSteps q a as := by
  calc
    _ = sampleClockSteps q a (retainedMassBefore u.val as) ++
        sampleClockSteps q (partitionEnd a (retainedMassBefore u.val as)) (retainedMassAfter u.val as) := by
      rw [retainedMass_endpoint as ho u hnode]
    _ = sampleClockSteps q a (retainedMassBefore u.val as ++ retainedMassAfter u.val as) :=
      (sampleClockSteps_append q a _ _).symm
    _ = _ := by rw [retainedMass_append]

def retainedMassBand (a c : ℝ) (as : List PositiveMass) : List PositiveMass :=
  retainedMassBefore c (retainedMassAfter a as)

def retainedMassTail (a c : ℝ) (as : List PositiveMass) : List PositiveMass :=
  retainedMassAfter c (retainedMassAfter a as)

theorem retainedMass_three_append (a c : ℝ) (as : List PositiveMass) :
    retainedMassBefore a as ++ retainedMassBand a c as ++ retainedMassTail a c as=as := by
  rw [List.append_assoc]
  unfold retainedMassBand retainedMassTail
  rw [retainedMass_append,retainedMass_append]

theorem retainedMassBefore_append_of_all_le {u : ℝ} (before after : List PositiveMass)
    (hbefore : ∀ b ∈ before, b.val≤u) :
    retainedMassBefore u (before++after)=before++retainedMassBefore u after := by
  induction before with
  | nil => rfl
  | cons b bs ih =>
    rw [List.cons_append,retainedMassBefore_cons_le b _ (hbefore b List.mem_cons_self)]
    exact congrArg (List.cons b) (ih (fun c hc => hbefore c (List.mem_cons_of_mem b hc)))

theorem retainedMass_later_mem {start : ℝ} (as : List PositiveMass) (ho : MassOrdered start as)
    (a c : PositiveMass) (ha : a∈as) (hc : c∈as) (hac : a.val<c.val) :
    c∈retainedMassAfter a.val as := by
  have hua : a.val ∈ Icc (0:ℝ) 1 :=
    ⟨a.2.le,(massOrdered_mem_le_end as ho ha).trans ho.end_bounds.2⟩
  have hleft := (retainedMass_ordered as ho hua (ho.le_of_mem ha)).2.2.1
  rw [← retainedMass_append a.val as] at hc
  rcases List.mem_append.mp hc with hc|hc
  · exact False.elim (not_le.mpr hac (hleft c hc))
  · exact hc

theorem retainedMass_three_ordered {start : ℝ} (as : List PositiveMass)
    (ho : MassOrdered start as) (a c : PositiveMass) (ha : a∈as) (hc : c∈as)
    (hac : a.val<c.val) :
    MassOrdered start (retainedMassBefore a.val as) ∧
    MassOrdered a.val (retainedMassBand a.val c.val as) ∧
    MassOrdered c.val (retainedMassTail a.val c.val as) ∧
    partitionEnd start (retainedMassBefore a.val as)=a.val ∧
    partitionEnd a.val (retainedMassBand a.val c.val as)=c.val := by
  have hua : a.val ∈ Icc (0:ℝ) 1 :=
    ⟨a.2.le,(massOrdered_mem_le_end as ho ha).trans ho.end_bounds.2⟩
  have huc : c.val ∈ Icc (0:ℝ) 1 :=
    ⟨c.2.le,(massOrdered_mem_le_end as ho hc).trans ho.end_bounds.2⟩
  obtain ⟨hbefore,hrest,_,_⟩ := retainedMass_ordered as ho hua (ho.le_of_mem ha)
  have hclater := retainedMass_later_mem as ho a c ha hc hac
  obtain ⟨hband,htail,_,_⟩ := retainedMass_ordered (retainedMassAfter a.val as) hrest huc hac.le
  exact ⟨hbefore,hband,htail,retainedMass_endpoint as ho a ha,
    retainedMass_endpoint (retainedMassAfter a.val as) hrest c hclater⟩

theorem retainedMass_later_prefix {start : ℝ} (as : List PositiveMass) (ho : MassOrdered start as)
    (a c : PositiveMass) (ha : a∈as) (_hc : c∈as) (hac : a.val≤c.val) :
    retainedMassBefore c.val as=retainedMassBefore a.val as++retainedMassBand a.val c.val as := by
  have hua : a.val ∈ Icc (0:ℝ) 1 :=
    ⟨a.2.le,(massOrdered_mem_le_end as ho ha).trans ho.end_bounds.2⟩
  have hbefore := (retainedMass_ordered as ho hua (ho.le_of_mem ha)).2.2.1
  conv_lhs => rw [← retainedMass_append a.val as]
  exact retainedMassBefore_append_of_all_le _ _ (fun b hb => (hbefore b hb).trans hac)

theorem retainedMassBand_duration_mesh {start mesh : ℝ} (as : List PositiveMass)
    (ho : MassOrdered start as) (hm : PartitionMesh mesh start as)
    (a : PositiveMass) (ha : a∈as) (c : ℝ) :
    ∀ (w:ℝ≥0), w∈sampleMassDurations a.val (retainedMassBand a.val c as) → (w:ℝ) ≤ mesh := by
  have he := retainedMass_three_append a.val c as
  have hfull : MassOrdered start
      (retainedMassBefore a.val as++retainedMassBand a.val c as++retainedMassTail a.val c as) := he.symm ▸ ho
  have hmfull : PartitionMesh mesh start
      (retainedMassBefore a.val as++retainedMassBand a.val c as++retainedMassTail a.val c as) := he.symm ▸ hm
  exact sampleMassDurations_internal_mesh _ _ _ hfull hmfull (retainedMass_endpoint as ho a ha)

theorem retainedMass_three_sampleClockSteps {ι : Type*} (q : ℝ → ι → ℝ≥0)
    {start : ℝ} (as : List PositiveMass) (ho : MassOrdered start as)
    (a c : PositiveMass) (ha : a∈as) (hc : c∈as) (hac : a.val<c.val) :
    sampleClockSteps q start (retainedMassBefore a.val as) ++
      sampleClockSteps q a.val (retainedMassBand a.val c.val as) ++
      sampleClockSteps q c.val (retainedMassTail a.val c.val as)=sampleClockSteps q start as := by
  obtain ⟨_,_,_,hea,hec⟩ := retainedMass_three_ordered as ho a c ha hc hac
  calc
    _ = sampleClockSteps q start
        (retainedMassBefore a.val as++retainedMassBand a.val c.val as++retainedMassTail a.val c.val as) := by
      rw [sampleClockSteps_append,sampleClockSteps_append,hea,partitionEnd_append,hea,hec]
    _ = _ := by rw [retainedMass_three_append]

theorem retainedMass_later_splitClockSteps_length {ι : Type*} (q : ℝ → ι → ℝ≥0)
    {start : ℝ} (as : List PositiveMass) (ho : MassOrdered start as)
    (a c : PositiveMass) (ha : a∈as) (hc : c∈as) (hac : a.val≤c.val) :
    (splitClockSteps c.val (sampleClockSteps q start as)).1.length=
      (retainedMassBefore a.val as).length+(retainedMassBand a.val c.val as).length := by
  rw [retainedMass_splitClockSteps_length,retainedMass_later_prefix as ho a c ha hc hac,List.length_append]

end OAI.SKFluctuations.LaplaceWindowFormalization
