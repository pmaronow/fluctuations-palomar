module

public import ComparisonSignedCavityHighFreshWordSums
public import ComparisonSignedCavityActualProjectionSpine

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}

def NativeProjectionSpine.fullEmbed {A : ClockTree S as}
    {base : NativeGeneratedTest A} {star : ℕ} :
    {T : ClockTree S as}→{P : NativeGeneratedTest T}→NativeProjectionSpine base star P→A.Slot→T.Slot
  | _,_,.base=>id
  | _,_,@NativeProjectionSpine.projection _ _ _ _ _ T P h a _=>
      fun c=>(nativeFreshAtSlot T a P.target star).embed (h.fullEmbed c)

def NativeProjectionSpine.fullRead {A : ClockTree S as}
    {base : NativeGeneratedTest A} {star : ℕ} :
    {T : ClockTree S as}→{P : NativeGeneratedTest T}→NativeProjectionSpine base star P→T.Assignment→A.Assignment
  | _,_,.base=>id
  | _,_,@NativeProjectionSpine.projection _ _ _ _ _ T P h a _=>
      fun σ=>h.fullRead ((nativeFreshAtSlot T a P.target star).restrict σ)

def NativeProjectionSpine.toothSlots {A : ClockTree S as}
    {base : NativeGeneratedTest A} {star : ℕ} :
    {T : ClockTree S as}→{P : NativeGeneratedTest T}→NativeProjectionSpine base star P→List T.Slot
  | _,_,.base=>[]
  | _,_,@NativeProjectionSpine.projection _ _ _ _ _ T P h a _=>
      h.toothSlots.map (nativeFreshAtSlot T a P.target star).embed++
        [(nativeFreshAtSlot T a P.target star).mark]

def NativeProjectionSpine.literalDiagram {A T : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) : NativeObservedDiagram A where
  tree:=T
  embed:=h.fullEmbed
  marks:=h.toothSlots
  read:=h.fullRead

theorem NativeProjectionSpine.fullEmbed_target {A T : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) : h.fullEmbed base.target=P.target := by
  induction h with
  | base=>rfl
  | projection h a hl ih=>
    change (nativeFreshAtSlot _ a _ star).embed (h.fullEmbed base.target)=_
    rw [ih]
    rfl

def NativeProjectionSpine.graftDiagram {A : ClockTree S as}
    {base : NativeGeneratedTest A} {star : ℕ} :
    {T : ClockTree S as}→{P : NativeGeneratedTest T}→NativeProjectionSpine base star P→
      NativeObservedDiagram A→NativeObservedDiagram A
  | _,_,.base=>id
  | _,_,.projection h a _=>fun D=>(h.graftDiagram D).fresh base.target star a

theorem NativeProjectionSpine.graft_identity {A T : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) :
    h.graftDiagram (NativeObservedDiagram.identity A)=h.literalDiagram := by
  induction h with
  | base=>rfl
  | @projection T P h a hl ih=>
    change (h.graftDiagram (NativeObservedDiagram.identity A)).fresh base.target star a=_
    rw [ih]
    exact congrArg (fun c : T.Slot => (show NativeObservedDiagram A from
      { tree:=(nativeFreshAtSlot T a c star).tree
        embed:=fun d=>(nativeFreshAtSlot T a c star).embed (h.fullEmbed d)
        marks:=h.toothSlots.map (nativeFreshAtSlot T a c star).embed++
          [(nativeFreshAtSlot T a c star).mark]
        read:=fun σ=>h.fullRead ((nativeFreshAtSlot T a c star).restrict σ) })) h.fullEmbed_target

theorem NativeProjectionSpine.high_words_graft {A T : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) (D : NativeObservedDiagram A) (k : ℕ) :
    nativeObservedHighWords (h.graftDiagram D) base.target star k=
      (nativeObservedHighWords D base.target star k).map (fun z=>(z.1,h.graftDiagram z.2)) := by
  induction h with
  | base=>simp only [graftDiagram,id_eq,List.map_id']
  | @projection T P h a hl ih=>
    simp only [graftDiagram,native_observed_high_words_fresh k _ _ _ hl a,ih,List.map_map,
      Function.comp_def]

theorem NativeProjectionSpine.high_words_literal {A T : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) (k : ℕ) :
    nativeObservedHighWords h.literalDiagram base.target star k=
      (nativeObservedHighWords (NativeObservedDiagram.identity A) base.target star k).map
        (fun z=>(z.1,h.graftDiagram z.2)) := by
  rw [←h.graft_identity]
  exact h.high_words_graft _ k

theorem NativeProjectionSpine.high_word_sum_literal {A T : ClockTree S as}
    {base : NativeGeneratedTest A} {P : NativeGeneratedTest T} {star : ℕ}
    (h : NativeProjectionSpine base star P) (k : ℕ) (F : NativeObservedDiagram A→ℝ) :
    nativeObservedHighWordSum h.literalDiagram base.target star k F=
      nativeObservedHighWordSum (NativeObservedDiagram.identity A) base.target star k
        (fun D=>F (h.graftDiagram D)) := by
  unfold nativeObservedHighWordSum
  rw [h.high_words_literal,List.map_map]
  rfl

end OAI.SKFluctuations.Hierarchy.ClockTree
