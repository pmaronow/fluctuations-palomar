module

public import ComparisonSignedCavityActualResourceRecursion

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

theorem nativeActualResourceExpansion_append
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (ops more : List NativeActualExpansionOp)
    (st : NativeActualResourceState S as i star) :
    nativeActualResourceExpansion Γ hs hl (ops++more) st=
      (nativeActualResourceExpansion Γ hs hl ops st).flatMap
        (nativeActualResourceExpansion Γ hs hl more) := by
  induction ops generalizing st with
  | nil=>simp [nativeActualResourceExpansion]
  | cons op ops ih=>
    simp only [List.cons_append,nativeActualResourceExpansion,List.flatMap_assoc]
    congr 1
    funext Q
    exact ih Q

def nativeActualResourceFrontierWords (branches : List (List NativeActualExpansionOp)) :
    ℕ→List (List NativeActualExpansionOp)
  | 0=>[[]]
  | depth+1=>(nativeActualResourceFrontierWords branches depth).flatMap
      (fun ops=>branches.map (fun more=>ops++more))

theorem nativeActualListSum_comm {α β : Type} (xs : List α) (ys : List β) (f : α→β→ℝ) :
    (xs.map (fun x=>(ys.map (f x)).sum)).sum=
      (ys.map (fun y=>(xs.map (fun x=>f x y)).sum)).sum := by
  induction xs with
  | nil=>simp
  | cons x xs ih=>simp only [List.map_cons,List.sum_cons,List.sum_map_add,ih]

theorem nativeActualResourceFrontier_sum_eq_words
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : List (List NativeActualExpansionOp))
    (depth : ℕ) (st : NativeActualResourceState S as i star)
    (F : NativeActualResourceState S as i star→ℝ) :
    ((nativeActualResourceFrontier Γ hs hl branches depth st).map F).sum=
      ((nativeActualResourceFrontierWords branches depth).map (fun ops=>
        ((nativeActualResourceExpansion Γ hs hl ops st).map F).sum)).sum := by
  induction depth generalizing F with
  | zero=>simp [nativeActualResourceFrontier,nativeActualResourceFrontierWords,nativeActualResourceExpansion]
  | succ depth ih=>
    simp only [nativeActualResourceFrontier,List.map_flatMap,native_sum_flatMap]
    rw [ih]
    simp only [nativeActualResourceFrontierWords,List.map_flatMap,native_sum_flatMap,List.map_map,
      Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro ops hops
    simp only [nativeActualResourceBranchStep,List.map_flatMap,native_sum_flatMap]
    rw [nativeActualListSum_comm]
    congr 1
    apply List.map_congr_left
    intro more hmore
    rw [nativeActualResourceExpansion_append,List.map_flatMap,native_sum_flatMap]

theorem nativeActualExpansionMarkedCount_append (ops more : List NativeActualExpansionOp) :
    nativeActualExpansionMarkedCount (ops++more)=
      nativeActualExpansionMarkedCount ops+nativeActualExpansionMarkedCount more := by
  simp only [nativeActualExpansionMarkedCount,List.map_append,List.sum_append]

theorem nativeActualResourceFrontierWords_markedCount
    (branches : List (List NativeActualExpansionOp)) (increment : ℕ)
    (hinc : ∀ops∈branches,nativeActualExpansionMarkedCount ops=increment)
    (depth : ℕ) (ops : List NativeActualExpansionOp)
    (hops : ops∈nativeActualResourceFrontierWords branches depth) :
    nativeActualExpansionMarkedCount ops=depth*increment := by
  induction depth generalizing ops with
  | zero=>obtain rfl:=List.mem_singleton.mp hops;simp [nativeActualExpansionMarkedCount]
  | succ depth ih=>
    obtain ⟨pre,hpre,hops⟩:=List.mem_flatMap.mp hops
    obtain ⟨more,hmore,rfl⟩:=List.mem_map.mp hops
    rw [nativeActualExpansionMarkedCount_append,ih pre hpre,hinc more hmore,Nat.succ_mul]

theorem nativeActualResourceFrontierWords_length
    (branches : List (List NativeActualExpansionOp)) (depth : ℕ) :
    (nativeActualResourceFrontierWords branches depth).length=branches.length^depth := by
  induction depth with
  | zero=>simp [nativeActualResourceFrontierWords]
  | succ depth ih=>
    simp only [nativeActualResourceFrontierWords,List.length_flatMap,List.length_map]
    simp only [List.map_const',List.sum_replicate,ih,pow_succ,nsmul_eq_mul,Nat.cast_id]

end OAI.SKFluctuations.Hierarchy.ClockTree
