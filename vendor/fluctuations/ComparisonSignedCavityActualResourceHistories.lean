module

public import ComparisonSignedCavityActualMarkedResourceSwitch

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}

inductive NativeActualResourceGenerated (i star U : ℕ) :
    List NativeResourceMark → ℕ → {as : List PositiveMass} →
      (T : ClockTree S as) → NativeResourceTerm i star T → Prop
  | physical {as : List PositiveMass} {seed : List NativeResourceMark} {k : ℕ}
      {T : ClockTree S as} {P : NativeResourceTerm i star T}
      (h : NativePhysicalResourceGenerated i star U seed k T P) :
      NativeActualResourceGenerated i star U seed k T P
  | freeze {as : List PositiveMass} {seed : List NativeResourceMark} {k : ℕ}
      {T : ClockTree S as} {P : NativeResourceTerm i star T}
      (h : NativeActualResourceGenerated i star U seed k T P) :
      NativeActualResourceGenerated i star U seed k T P.freeze
  | reweight {as : List PositiveMass} {seed : List NativeResourceMark} {k : ℕ}
      {T : ClockTree S as} {P : NativeResourceTerm i star T}
      (h : NativeActualResourceGenerated i star U seed k T P) (c : ℝ) :
      NativeActualResourceGenerated i star U seed k T (P.reweight c)
  | retarget {as : List PositiveMass} {seed : List NativeResourceMark} {k : ℕ}
      {T : ClockTree S as} {P : NativeResourceTerm i star T}
      (h : NativeActualResourceGenerated i star U seed k T P) :
      NativeActualResourceGenerated i star U seed k
        (nativeFreshAtSlot T 0 P.live.test.target star).tree (P.retarget 0)
  | projection {as : List PositiveMass} {seed : List NativeResourceMark} {k : ℕ}
      {T : ClockTree S as} {P : NativeResourceTerm i star T}
      (h : NativeActualResourceGenerated i star U seed k T P) (hl : star≤as.length) :
      NativeActualResourceGenerated i star U seed (k+1)
        (nativeFreshAtSlot T 0 P.live.test.target star).tree (P.projection 0 k hl)
  | markedSwitch {as : List PositiveMass} {seed : List NativeResourceMark} {k : ℕ}
      {T : ClockTree S as} {P : NativeResourceTerm i star T}
      (h : NativeActualResourceGenerated i star U seed k T P)
      (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (hs : star < U) (hh : U≤p.tree.splitIndex (p.embed P.live.test.target) p.mark) :
      NativeActualResourceGenerated i star U seed (k+1)
        (nativeFreshAtSlot p.tree 0 (p.embed P.live.test.target) star).tree
        (P.markedHighSwitch 0 k p hp hs hh)

theorem NativeActualResourceGenerated.resource_word
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {seed : List NativeResourceMark} {k : ℕ} {P : NativeResourceTerm i star T}
    (h : NativeActualResourceGenerated i star U seed k T P) :
    P.resources=seed++(List.range k).map NativeResourceMark.markedStar := by
  induction h with
  | physical h=>exact h.to_resource_generated.resource_word
  | freeze h ih=>simpa only [NativeResourceTerm.freeze_resources] using ih
  | reweight h c ih=>simpa only [NativeResourceTerm.reweight_resources] using ih
  | retarget h ih=>simpa only [NativeResourceTerm.retarget_resources] using ih
  | projection h hl ih=>
    rw [NativeResourceTerm.projection_resources,ih]
    simp only [List.range_succ,List.map_append,List.map_singleton,List.append_assoc]
  | markedSwitch h p hp hs hh ih=>
    rw [NativeResourceTerm.markedHighSwitch_resources,ih]
    simp only [List.range_succ,List.map_append,List.map_singleton,List.append_assoc]

theorem NativeActualResourceGenerated.persistentLowForks
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {seed : List NativeResourceMark} {k : ℕ} {P : NativeResourceTerm i star T}
    (h : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star) :
    NativePersistentLowForks i star U T := by
  induction h with
  | physical h=>exact h.persistentLowForks
  | freeze h ih=>exact ih
  | reweight h c ih=>exact ih
  | retarget h ih=>exact ih.freshStar 0 _
  | projection h hl ih=>exact ih.freshStar 0 _
  | markedSwitch h p hp hs hh ih=>
    have hMarked:=ih.observedHigh hi hs 0 p hp _ (by rwa [p.tree.splitIndex_symm])
    exact hMarked.freshStar 0 _

theorem NativeActualResourceGenerated.frozenLowForks
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {seed : List NativeResourceMark} {k : ℕ} {P : NativeResourceTerm i star T}
    (h : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star) :
    ∀F∈P.frozen,NativePersistentLowForks i star U F.tree := by
  induction h with
  | physical h=>exact h.frozenLowForks
  | freeze h ih=>
    intro F hF
    rcases List.mem_append.mp hF with hF|hF
    · exact ih F hF
    · obtain rfl:=List.mem_singleton.mp hF
      exact h.persistentLowForks hi
  | reweight h c ih=>exact ih
  | retarget h ih=>exact ih
  | projection h hl ih=>exact ih
  | markedSwitch h p hp hs hh ih=>exact ih

theorem NativeActualResourceGenerated.centered_generated
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {seed : List NativeResourceMark} {k : ℕ} {P : NativeResourceTerm i star T}
    (h : NativeActualResourceGenerated i star U seed k T P)
    (Q : NativeResourceTerm i star T) (hQ : Q∈P.centered) :
    NativeActualResourceGenerated i star U seed k T Q := by
  simp only [NativeResourceTerm.centered,List.mem_cons,List.not_mem_nil,or_false] at hQ
  rcases hQ with rfl|rfl
  · exact h
  · exact h.freeze

end OAI.SKFluctuations.Hierarchy.ClockTree
