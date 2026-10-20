module

public import ComparisonSignedCavityNaturalScaleCalibration

@[expose] public section

noncomputable section
set_option maxHeartbeats 4500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type*} {as : List PositiveMass} {T : ClockTree S as}

def NativeGeneratedTest.initialEdgeCount (P : NativeGeneratedTest T) (i : ℕ) : ℕ :=
  P.edges.countP fun e=>decide (T.splitIndex e.1 e.2=i)

theorem NativeGeneratedTest.edges_addProjection_perm (P : NativeGeneratedTest T)
    (a : ℝ) (star : ℕ) :
    (P.addProjection a star).edges.Perm (
      P.edges.map (fun e=>((nativeFreshAtSlot T a P.target star).embed e.1,
        (nativeFreshAtSlot T a P.target star).embed e.2)) ++
      [((nativeFreshAtSlot T a P.target star).embed P.target,
        (nativeFreshAtSlot T a P.target star).mark)]) := by
  simp only [NativeGeneratedTest.edges,NativeGeneratedTest.addProjection,
    List.map_append,List.map_map,List.append_assoc,Function.comp_def,
    List.map_cons,List.map_nil]
  rw [List.perm_append_left_iff,List.perm_append_left_iff]
  exact List.perm_append_comm

theorem NativeGeneratedTest.edges_switchTarget (P : NativeGeneratedTest T)
    (a : ℝ) (star : ℕ) (c : T.Slot) :
    (P.switchTarget a star c).edges =
      P.edges.map (fun e=>((nativeFreshAtSlot T a P.target star).embed e.1,
        (nativeFreshAtSlot T a P.target star).embed e.2)) ++
      [((nativeFreshAtSlot T a P.target star).mark,
        (nativeFreshAtSlot T a P.target star).embed c)] := by
  simp [NativeGeneratedTest.edges,NativeGeneratedTest.switchTarget]

theorem NativeGeneratedTest.initialEdgeCount_addProjection (P : NativeGeneratedTest T)
    (a : ℝ) {i star : ℕ} (hi : i<star) (hlen : star ≤ as.length) :
    (P.addProjection a star).initialEdgeCount i=P.initialEdgeCount i := by
  classical
  let p:=nativeFreshAtSlot T a P.target star
  have hs:=(nativeFreshAtSlot_old_splits T a P.target star).2
  have hnew : p.tree.splitIndex (p.embed P.target) p.mark=star := by
    rw [splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left hlen]
  unfold NativeGeneratedTest.initialEdgeCount
  rw [(P.edges_addProjection_perm a star).countP_eq]
  simp only [List.countP_append,List.countP_map,List.countP_cons,List.countP_nil]
  simp only [Function.comp_def,zero_add]
  simp_rw [hs]
  change _+(if decide (p.tree.splitIndex (p.embed P.target) p.mark=i) then 1 else 0)=_
  rw [hnew]
  simp [hi.ne']

theorem NativeGeneratedTest.initialEdgeCount_switchTarget (P : NativeGeneratedTest T)
    (a : ℝ) (c : T.Slot) {i star U : ℕ} (hi : i<star) (hstar : star<U)
    (hhigh : U ≤ T.splitIndex P.target c) :
    (P.switchTarget a star c).initialEdgeCount i=P.initialEdgeCount i := by
  classical
  let p:=nativeFreshAtSlot T a P.target star
  have hs:=(nativeFreshAtSlot_old_splits T a P.target star).2
  have hnew : p.tree.splitIndex p.mark (p.embed c)=star :=
    nativeFreshAtSlot_high_relative_star T a P.target c hstar hhigh
  unfold NativeGeneratedTest.initialEdgeCount
  rw [P.edges_switchTarget]
  simp only [List.countP_append,List.countP_map,List.countP_cons,List.countP_nil]
  simp only [Function.comp_def,zero_add]
  simp_rw [hs]
  change _+(if decide (p.tree.splitIndex p.mark (p.embed c)=i) then 1 else 0)=_
  rw [hnew]
  simp [hi.ne']

theorem NativeTestGenerated.initial_edge_count_le_one {i star : ℕ}
    {P : NativeGeneratedTest T} (hP : NativeTestGenerated i star T P) (hi : i<star) :
    P.initialEdgeCount i ≤ 1 := by
  induction hP with
  | seed T a s j hj hlen =>
    unfold NativeGeneratedTest.initialEdgeCount
    have H:=@List.countP_le_length _ (fun e=>decide
      ((nativeFreshAtSlot T a s j).tree.splitIndex e.1 e.2=i))
      (nativeGeneratedSeed T a s j).edges
    simpa [NativeGeneratedTest.edges,nativeGeneratedSeed] using H
  | constant h ih => simp [NativeGeneratedTest.initialEdgeCount,
      NativeGeneratedTest.constant,NativeGeneratedTest.edges]
  | projection h a hlen ih => rw [NativeGeneratedTest.initialEdgeCount_addProjection _ a hi hlen];exact ih
  | switch h a c U hstar hhigh ih =>
    rw [NativeGeneratedTest.initialEdgeCount_switchTarget _ a c hi hstar hhigh]
    exact ih

def NativeGeneratedTest.initialResources (P : NativeGeneratedTest T) (i : ℕ) :
    Finset (Fin P.edges.length) :=
  Finset.univ.filter fun e=>T.splitIndex (P.edges.get e).1 (P.edges.get e).2=i

theorem NativeGeneratedTest.initialResources_card (P : NativeGeneratedTest T) (i : ℕ) :
    (P.initialResources i).card=P.initialEdgeCount i := by
  classical
  have H:=(List.nodup_finRange P.edges.length).card_eq_countP
    (P:=fun e=>T.splitIndex (P.edges.get e).1 (P.edges.get e).2=i)
  simp only [List.toFinset_finRange] at H
  unfold NativeGeneratedTest.initialResources NativeGeneratedTest.initialEdgeCount
  rw [H]
  conv_rhs => rw [←List.map_get_finRange P.edges,List.countP_map]
  rfl

theorem NativeTestGenerated.initial_resources_le_one {i star : ℕ}
    {P : NativeGeneratedTest T} (hP : NativeTestGenerated i star T P) (hi : i<star) :
    (P.initialResources i).card ≤ 1 := by
  rw [P.initialResources_card]
  exact hP.initial_edge_count_le_one hi

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy

def generatedActualNaturalShape {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} {i star U cut : ℕ}
    {P : T.NativeGeneratedTest} (hP : ClockTree.NativeTestGenerated i star T P)
    (hi : i ≤ star) (hstar : star<U) (hU : U ≤ cut) (hcut : cut ≤ as.length)
    (s : T.Slot) (α β : Fin P.edges.length→ℝ) :
    ActualNaturalBoundaryShape n P.edges.length T where
  α:=α
  β:=β
  i:=P.boundaryAnchor s cut
  j:=P.boundaryTarget s cut
  distinct:=hP.oriented_endpoints_distinct hi hstar hU hcut s
  lowInGrid:=fun _=>T.splitIndex_le_clockLength _ _

theorem generated_natural_source_low_mass {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} {i star U cut : ℕ}
    {P : T.NativeGeneratedTest} (hP : ClockTree.NativeTestGenerated i star T P)
    (hi : i<star) (hstar : star<U) (hU : U ≤ cut) (hcut : cut ≤ as.length)
    (s : T.Slot) (α β : Fin P.edges.length→ℝ) (x W Cmass : ℝ)
    (hmassi : partitionPoint 0 as i ≤ Cmass*x)
    (hmassstar : partitionPoint 0 as star ≤ Cmass*W) :
    ∀e,partitionPoint 0 as
      (T.splitIndex ((generatedActualNaturalShape hP hi.le hstar hU hcut s α β).i e)
        ((generatedActualNaturalShape hP hi.le hstar hU hcut s α β).j e)) ≤
      Cmass*sourceFactorScale x W (P.initialResources i) e := by
  classical
  intro e
  change partitionPoint 0 as (T.splitIndex (P.boundaryAnchor s cut e)
    (P.boundaryTarget s cut e)) ≤ _
  rw [P.oriented_low_split]
  unfold sourceFactorScale ClockTree.NativeGeneratedTest.initialResources
  rcases hP.ancestry.edges_low (P.edges.get e) (List.get_mem _ e) with H|H
  · simp only [H,Finset.mem_filter,Finset.mem_univ,true_and,ite_true]
    exact hmassi
  · simp only [H,Finset.mem_filter,Finset.mem_univ,true_and,hi.ne',ite_false]
    exact hmassstar

theorem generated_source_field_le {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} {i star U cut : ℕ}
    {P : T.NativeGeneratedTest} (hP : ClockTree.NativeTestGenerated i star T P)
    (hi : i < star) (hstar : star < U) (hU : U ≤ cut) (hcut : cut ≤ as.length)
    (s : T.Slot) (α β : Fin P.edges.length→ℝ) (f : ℕ→ℝ) (x W Ch : ℝ)
    (hfi : |f i| ≤ Ch*x) (hfs : |f star| ≤ Ch*W) :
    ∀e,|f (T.splitIndex ((generatedActualNaturalShape hP hi.le hstar hU hcut s α β).i e)
      ((generatedActualNaturalShape hP hi.le hstar hU hcut s α β).j e))| ≤
      Ch*sourceFactorScale x W (P.initialResources i) e := by
  classical
  intro e
  change |f (T.splitIndex (P.boundaryAnchor s cut e) (P.boundaryTarget s cut e))| ≤ _
  rw [P.oriented_low_split]
  unfold sourceFactorScale ClockTree.NativeGeneratedTest.initialResources
  rcases hP.ancestry.edges_low (P.edges.get e) (List.get_mem _ e) with H|H
  · simp only [H,Finset.mem_filter,Finset.mem_univ,true_and,ite_true]
    exact hfi
  · simp only [H,Finset.mem_filter,Finset.mem_univ,true_and,hi.ne',ite_false]
    exact hfs

end OAI.SKFluctuations.Cavity
