module

public import ComparisonSignedCavityActualResourceExpansion

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

theorem native_sum_flatMap {X : Type} (l : List X) (F : X → List ℝ) :
    (l.flatMap F).sum=(l.map (fun a=>(F a).sum)).sum := by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp only [List.flatMap_cons,List.sum_append,List.map_cons,List.sum_cons,ih]

def nativeActualResourceRecursiveSum
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star < U) (hl : star≤as.length)
    (F : NativeActualResourceState S as i star → ℝ) :
    List NativeActualExpansionOp → NativeActualResourceState S as i star → ℝ
  | [],st=>F st
  | op::ops,st=>((nativeActualResourceStep Γ hs hl op st).map
      (nativeActualResourceRecursiveSum Γ hs hl F ops)).sum

theorem nativeActualResourceExpansion_sum_eq_recursive
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star < U) (hl : star≤as.length)
    (F : NativeActualResourceState S as i star → ℝ)
    (ops : List NativeActualExpansionOp) (st : NativeActualResourceState S as i star) :
    ((nativeActualResourceExpansion Γ hs hl ops st).map F).sum=
      nativeActualResourceRecursiveSum Γ hs hl F ops st := by
  induction ops generalizing st with
  | nil=>simp only [nativeActualResourceExpansion,nativeActualResourceRecursiveSum,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  | cons op ops ih=>
    simp only [nativeActualResourceExpansion,List.map_flatMap,native_sum_flatMap,
      nativeActualResourceRecursiveSum]
    congr 1
    apply List.map_congr_left
    intro t ht
    exact ih t

@[simp] theorem NativeActualResourceState.markedRow_coefficient
    (st : NativeActualResourceState S as i star)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (p : MarkedPlacement st.tree) (hp : p∈st.tree.markedAttach 0)
    (hs : star < U) (hh : U≤p.tree.splitIndex (p.embed st.term.live.test.target) p.mark) :
    (st.markedRow Γ p hp hs hh).term.coefficient=(p.coeff*Γ st.toHigh p)*st.term.coefficient := rfl

theorem nativeActualHighExpansion_forkLedger
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star < U) (hl : star≤as.length) (f : ℕ → ℝ)
    (k : ℕ) (st : NativeActualResourceState S as i star) :
    ((nativeActualResourceExpansion Γ hs hl (List.replicate k .highRow) st).map
      (fun Q=>|Q.term.coefficient| *Q.tree.forkCost f)).sum=
      |st.term.coefficient| *nativeHighSwitchForkLedger star U Γ f k st.toHigh := by
  induction k generalizing st with
  | zero=>simp only [List.replicate_zero,nativeActualResourceExpansion,List.map_cons,
      List.map_nil,List.sum_cons,List.sum_nil,add_zero,nativeHighSwitchForkLedger,
      NativeActualResourceState.toHigh]
  | succ k ih=>
    rw [List.replicate_succ,nativeActualResourceExpansion]
    simp only [List.map_flatMap,native_sum_flatMap]
    simp_rw [ih]
    conv_rhs =>
      change |st.term.coefficient| *nativeHighSwitchForkLedger star U Γ f (k+1)
        (⟨st.tree,st.term.live.test.target⟩ : NativeHighSwitchState S as)
      rw [nativeHighSwitchForkLedger,←List.sum_map_mul_left]
    unfold nativeActualResourceStep
    simp only [List.map_flatMap,native_sum_flatMap]
    change _=((st.tree.markedAttach 0).map (fun p=>|st.term.coefficient| *
      (|p.coeff| *|Γ (⟨st.tree,st.term.live.test.target⟩ : NativeHighSwitchState S as) p| *(if U≤p.tree.splitIndex (p.embed st.term.live.test.target) p.mark then
        nativeHighSwitchForkLedger star U Γ f k ((⟨st.tree,st.term.live.test.target⟩ : NativeHighSwitchState S as).row star p) else 0)))).sum
    conv_rhs => rw [←List.attach_map_val]
    congr 1
    apply List.map_congr_left
    intro p hp
    split_ifs with hh
    · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
        NativeActualResourceState.markedRow_coefficient,abs_mul]
      have ht:=st.markedRow_toHigh Γ p.val p.property hs hh
      dsimp only [NativeActualResourceState.toHigh] at ht
      dsimp only [NativeActualResourceState.toHigh]
      rw [ht]
      ring
    · simp only [List.map_nil,List.sum_nil,mul_zero]

theorem nativeActualHighExpansion_forkLedger_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0 → |Γ st p|≤1)
    (hs : star < U) (hl : star≤as.length) (f : ℕ → ℝ)
    (hf : ∀j,0≤f j) (hlo : ∀j,j<U → f j=0)
    (k : ℕ) (st : NativeActualResourceState S as i star) (hsource : st.tree.forkCost f=0) :
    ((nativeActualResourceExpansion Γ hs hl (List.replicate k .highRow) st).map
      (fun Q=>|Q.term.coefficient| *Q.tree.forkCost f)).sum≤
      |st.term.coefficient| *nativeHighSwitchForkVariation st.tree.leaves k*edgeBudget 0 as f := by
  rw [nativeActualHighExpansion_forkLedger]
  simpa only [NativeActualResourceState.toHigh,mul_assoc] using
    mul_le_mul_of_nonneg_left (nativeHighSwitchForkLedger_le_edgeBudget ho star U hs Γ hΓ
      f hf hlo k st.toHigh hsource) (abs_nonneg st.term.coefficient)

end OAI.SKFluctuations.Hierarchy.ClockTree
