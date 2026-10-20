module

public import ComparisonSignedCavityActualResourceHistories

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

structure NativeActualResourceState (S : Type) (as : List PositiveMass) (i star : ℕ) where
  tree : ClockTree S as
  term : NativeResourceTerm i star tree
  generation : ℕ

def NativeActualResourceState.toHigh (st : NativeActualResourceState S as i star) :
    NativeHighSwitchState S as := ⟨st.tree,st.term.live.test.target⟩

def NativeActualResourceState.freeze (st : NativeActualResourceState S as i star) :
    NativeActualResourceState S as i star := ⟨st.tree,st.term.freeze,st.generation⟩

def NativeActualResourceState.reweight (st : NativeActualResourceState S as i star) (c : ℝ) :
    NativeActualResourceState S as i star := ⟨st.tree,st.term.reweight c,st.generation⟩

def NativeActualResourceState.retarget (st : NativeActualResourceState S as i star) :
    NativeActualResourceState S as i star :=
  ⟨(nativeFreshAtSlot st.tree 0 st.term.live.test.target star).tree,st.term.retarget 0,st.generation⟩

def NativeActualResourceState.projection (st : NativeActualResourceState S as i star)
    (hl : star≤as.length) : NativeActualResourceState S as i star :=
  ⟨(nativeFreshAtSlot st.tree 0 st.term.live.test.target star).tree,
    st.term.projection 0 st.generation hl,st.generation+1⟩

def NativeActualResourceState.markedRow (st : NativeActualResourceState S as i star)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (p : MarkedPlacement st.tree) (hp : p∈st.tree.markedAttach 0)
    (hs : star < U) (hh : U≤p.tree.splitIndex (p.embed st.term.live.test.target) p.mark) :
    NativeActualResourceState S as i star :=
  ⟨(nativeFreshAtSlot p.tree 0 (p.embed st.term.live.test.target) star).tree,
    (st.term.markedHighSwitch 0 st.generation p hp hs hh).reweight (p.coeff*Γ st.toHigh p),
    st.generation+1⟩

theorem NativeActualResourceState.markedRow_toHigh
    (st : NativeActualResourceState S as i star)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (p : MarkedPlacement st.tree) (hp : p∈st.tree.markedAttach 0)
    (hs : star < U) (hh : U≤p.tree.splitIndex (p.embed st.term.live.test.target) p.mark) :
    (st.markedRow Γ p hp hs hh).toHigh=st.toHigh.row star p := rfl

inductive NativeActualExpansionOp where
  | center
  | reweight (c : ℝ)
  | retarget
  | projection
  | highRow

def nativeActualResourceStep
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star < U) (hl : star≤as.length) (op : NativeActualExpansionOp)
    (st : NativeActualResourceState S as i star) : List (NativeActualResourceState S as i star) :=
  match op with
  | .center=>[st,st.freeze]
  | .reweight c=>[st.reweight c]
  | .retarget=>[st.retarget]
  | .projection=>[st.projection hl]
  | .highRow=>(st.tree.markedAttach 0).attach.flatMap (fun p=>
      if hh : U≤p.val.tree.splitIndex (p.val.embed st.term.live.test.target) p.val.mark then
        [st.markedRow Γ p.val p.property hs hh] else [])

def nativeActualResourceExpansion
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star < U) (hl : star≤as.length) : List NativeActualExpansionOp →
      NativeActualResourceState S as i star → List (NativeActualResourceState S as i star)
  | [],st=>[st]
  | op::ops,st=>(nativeActualResourceStep Γ hs hl op st).flatMap
      (nativeActualResourceExpansion Γ hs hl ops)

theorem nativeActualResourceStep_valid
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star < U) (hl : star≤as.length) (op : NativeActualExpansionOp)
    (st : NativeActualResourceState S as i star) {seed : List NativeResourceMark}
    (h : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (Q : NativeActualResourceState S as i star) (hQ : Q∈nativeActualResourceStep Γ hs hl op st) :
    NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term := by
  cases op with
  | center=>
    simp only [nativeActualResourceStep,List.mem_cons,List.not_mem_nil,or_false] at hQ
    rcases hQ with rfl|rfl
    · exact h
    · exact h.freeze
  | reweight c=>
    obtain rfl:=List.mem_singleton.mp hQ
    exact h.reweight c
  | retarget=>
    obtain rfl:=List.mem_singleton.mp hQ
    exact h.retarget
  | projection=>
    obtain rfl:=List.mem_singleton.mp hQ
    exact h.projection hl
  | highRow=>
    obtain ⟨p,hp,hQ⟩:=List.mem_flatMap.mp hQ
    split_ifs at hQ with hh
    · obtain rfl:=List.mem_singleton.mp hQ
      exact (h.markedSwitch p.val p.property hs hh).reweight (p.val.coeff*Γ st.toHigh p.val)
    · cases hQ

theorem nativeActualResourceExpansion_valid
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star < U) (hl : star≤as.length) (ops : List NativeActualExpansionOp)
    (st : NativeActualResourceState S as i star) {seed : List NativeResourceMark}
    (h : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (Q : NativeActualResourceState S as i star) (hQ : Q∈nativeActualResourceExpansion Γ hs hl ops st) :
    NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term := by
  induction ops generalizing st with
  | nil=>obtain rfl:=List.mem_singleton.mp hQ;exact h
  | cons op ops ih=>
    obtain ⟨P,hP,hQ⟩:=List.mem_flatMap.mp hQ
    exact ih P (nativeActualResourceStep_valid Γ hs hl op st h P hP) hQ

def nativeActualConstantState (as : List PositiveMass) (i star : ℕ) :
    NativeActualResourceState S as i star :=
  ⟨single as,.ofLive (nativeResourceConstant (single as) (singleSlot as) i star),0⟩

def nativeActualInitialState (as : List PositiveMass) (i star : ℕ) (a : ℝ) (hi : i≤as.length) :
    NativeActualResourceState S as i star :=
  ⟨(nativeFreshAtSlot (single as) a (singleSlot as) i).tree,
    .ofLive (nativeResourceSeed (single as) a (singleSlot as) i star .initial (Or.inl rfl) hi),0⟩

theorem nativeActualInitialExpansion_valid (as : List PositiveMass)
    (i star U : ℕ) (hi : i ≤ star) (hs : star < U) (hU : U≤as.length) (a : ℝ)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (ops : List NativeActualExpansionOp) (Q : NativeActualResourceState S as i star)
    (hQ : Q∈nativeActualResourceExpansion Γ hs (by omega) ops
      (nativeActualInitialState as i star a (by omega))) :
    NativeActualResourceGenerated i star U [.initial] Q.generation Q.tree Q.term :=
  nativeActualResourceExpansion_valid Γ hs (by omega) ops _
    (.physical (.seed as hU a .initial (Or.inl rfl) (by change i≤as.length;omega))) Q hQ

theorem nativeActualConstantExpansion_valid (as : List PositiveMass)
    (i star U : ℕ) (hs : star < U) (hU : U≤as.length)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (ops : List NativeActualExpansionOp) (Q : NativeActualResourceState S as i star)
    (hQ : Q∈nativeActualResourceExpansion Γ hs (by omega) ops (nativeActualConstantState as i star)) :
    NativeActualResourceGenerated i star U [] Q.generation Q.tree Q.term :=
  nativeActualResourceExpansion_valid Γ hs (by omega) ops _ (.physical (.constant as hU)) Q hQ

end OAI.SKFluctuations.Hierarchy.ClockTree
