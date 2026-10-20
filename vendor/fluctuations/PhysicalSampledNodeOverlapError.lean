module

public import PhysicalRetainedOverlapLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 1000000

theorem massPartition_end_ge_start {u : ℝ} (as : List PositiveMass) (ho : MassOrdered u as) :
    u ≤ partitionEnd u as := by
  induction as generalizing u with
  | nil=>rfl
  | cons a as ih=>exact ho.2.1.trans (ih ho.2.2)

theorem massPartition_mem_le_end {u : ℝ} (as : List PositiveMass) (ho : MassOrdered u as)
    {v : PositiveMass} (hv : v∈as) : v.val ≤ partitionEnd u as := by
  induction as generalizing u with
  | nil=>simp at hv
  | cons a as ih=>
    rcases List.mem_cons.mp hv with hv|hv
    · subst v;exact massPartition_end_ge_start as ho.2.2
    · exact ih ho.2.2 hv

theorem massPartition_take_ordered {u : ℝ} (as : List PositiveMass) (ho : MassOrdered u as)
    (j : ℕ) : MassOrdered u (as.take j) := by
  induction as generalizing u j with
  | nil=>simpa only [List.take_nil] using ho
  | cons a as ih=>
    cases j with
    | zero=>exact massOrdered_bounds ho
    | succ j=>exact ⟨ho.1,ho.2.1,ih ho.2.2 j⟩

theorem massPartition_take_end (u : ℝ) (as : List PositiveMass) (j : ℕ) :
    partitionEnd u (as.take j)=partitionPoint u as j := by
  induction as generalizing u j with
  | nil=>simp only [List.take_nil,partitionEnd,partitionPoint,partitionValues,id_eq]
  | cons a as ih=>
    cases j with
    | zero=>rfl
    | succ j=>exact ih a.val j

theorem massPartition_drop_ordered {u : ℝ} (as : List PositiveMass) (ho : MassOrdered u as)
    (j : ℕ) : MassOrdered (partitionPoint u as j) (as.drop j) := by
  induction as generalizing u j with
  | nil=>simpa only [List.drop_nil,partitionPoint,partitionValues,id_eq] using ho
  | cons a as ih=>
    cases j with
    | zero=>exact ho
    | succ j=>exact ih ho.2.2 j

theorem massPartition_point_succ_eq_getElem (u : ℝ) (as : List PositiveMass)
    {j : ℕ} (hj : j < as.length) : partitionPoint u as (j+1)=as[j].val := by
  induction as generalizing u j with
  | nil=>simp at hj
  | cons a as ih=>
    cases j with
    | zero=>simp only [partitionPoint,partitionValues,partitionValues_zero,id_eq,List.getElem_cons_zero]
    | succ j=>exact ih a.val (by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hj)

theorem massPartition_point_pos (u : ℝ) (as : List PositiveMass)
    {j : ℕ} (hj0 : 0 < j) (hj : j ≤ as.length) : 0 < partitionPoint u as j := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0.ne'
  rw [massPartition_point_succ_eq_getElem u as (by omega)]
  exact as[l].property

theorem massPartition_point_next_mesh {u mesh : ℝ} (as : List PositiveMass)
    (hmesh : PartitionMesh mesh u as) {j : ℕ} (hj : j < as.length) :
    partitionPoint u as (j+1)-partitionPoint u as j ≤ mesh := by
  induction as generalizing u j with
  | nil=>simp at hj
  | cons a as ih=>
    cases j with
    | zero=>simpa only [partitionPoint,partitionValues,partitionValues_zero,id_eq] using hmesh.1
    | succ j=>exact ih hmesh.2 (by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hj)

theorem physicalSampledNodeSecondMoment_error (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hm : PartitionMesh mesh 0 as) (j : ℕ) (hj : j ≤ as.length)
    (hu : 0 < partitionPoint 0 as j) :
    let q := completedPathClock (n+1) b h
    let steps := sampleClockSteps q 0 as
    |physicalPathSecondMoment (n+1) steps (q 0) j-orderedPathS (n+1) b h (partitionPoint 0 as j)| ≤
      mesh*(2*ClockTree.errorJetVariation 2 0 0*
        clockVariationBound (physicalFeatureCoordinateBound n) q) := by
  dsimp only
  let q := completedPathClock (n+1) b h
  let before := as.take j
  let after := as.drop j
  let u := partitionPoint 0 as j
  have heu : partitionEnd 0 before=u := massPartition_take_end 0 as j
  have hv : u ≤ 1 := (partitionPoint_mem as ho j).2
  have hbefore : MassOrdered 0 before := massPartition_take_ordered as ho j
  have hafter : MassOrdered u after := massPartition_drop_ordered as ho j
  have hafterEnd : partitionEnd u after=1 := by
    have hh := congrArg (partitionEnd (0:ℝ)) (List.take_append_drop j as)
    rw [partitionEnd_append,heu,he] at hh
    exact hh
  have hfullMesh : PartitionMesh mesh 0 (before++after) := by
    simpa only [before,after,List.take_append_drop] using hm
  have herr := physicalRetainedCutSecondMoment_error n b h hb hh ⟨hu,hv⟩ before after
    hbefore hafter (fun v hv=>by
      change v.val ≤ u
      rw [←heu]
      exact massPartition_mem_le_end before hbefore hv)
    heu hafterEnd hfullMesh
  have hsample : sampleClockSteps q 0 before++sampleClockSteps q u after=sampleClockSteps q 0 as := by
    rw [←heu,←sampleClockSteps_append]
    simp only [before,after,List.take_append_drop]
  have hlen : (sampleClockSteps q 0 before).length=j := by
    simp only [sampleClockSteps_length,before,List.length_take,min_eq_left hj]
  have hout := abs_le.mpr ⟨by linarith [herr.2],herr.1⟩
  rw [hsample,hlen] at hout
  exact hout

end OAI.SKFluctuations.LaplaceWindowFormalization
