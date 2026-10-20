module

public import ComparisonSignedCavityForestPairedClone

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}

inductive NativePhysicalResourceGenerated (i star U : ℕ) :
    List NativeResourceMark → ℕ → {as : List PositiveMass} →
      (T : ClockTree S as) → NativeResourceTerm i star T → Prop
  | constant (as : List PositiveMass) (hU : U≤as.length) :
      NativePhysicalResourceGenerated i star U [] 0 (single as)
        (.ofLive (nativeResourceConstant (single as) (singleSlot as) i star))
  | seed (as : List PositiveMass) (hU : U≤as.length) (a : ℝ) (mark : NativeResourceMark)
      (hmark : mark=.initial ∨ mark=.oldStar) (hlen : mark.cut i star≤as.length) :
      NativePhysicalResourceGenerated i star U [mark] 0
        (nativeFreshAtSlot (single as) a (singleSlot as) (mark.cut i star)).tree
        (.ofLive (nativeResourceSeed (single as) a (singleSlot as) i star mark hmark hlen))
  | freeze {as : List PositiveMass} {seed : List NativeResourceMark} {k : ℕ} {T : ClockTree S as}
      {P : NativeResourceTerm i star T} (h : NativePhysicalResourceGenerated i star U seed k T P) :
      NativePhysicalResourceGenerated i star U seed k T P.freeze
  | reweight {as : List PositiveMass} {seed : List NativeResourceMark} {k : ℕ} {T : ClockTree S as}
      {P : NativeResourceTerm i star T} (h : NativePhysicalResourceGenerated i star U seed k T P)
      (c : ℝ) : NativePhysicalResourceGenerated i star U seed k T (P.reweight c)
  | retarget {as : List PositiveMass} {seed : List NativeResourceMark} {k : ℕ} {T : ClockTree S as}
      {P : NativeResourceTerm i star T} (h : NativePhysicalResourceGenerated i star U seed k T P)
      (a : ℝ) : NativePhysicalResourceGenerated i star U seed k
        (nativeFreshAtSlot T a P.live.test.target star).tree (P.retarget a)
  | projection {as : List PositiveMass} {seed : List NativeResourceMark} {k : ℕ} {T : ClockTree S as}
      {P : NativeResourceTerm i star T} (h : NativePhysicalResourceGenerated i star U seed k T P)
      (a : ℝ) (hlen : star≤as.length) : NativePhysicalResourceGenerated i star U seed (k+1)
        (nativeFreshAtSlot T a P.live.test.target star).tree (P.projection a k hlen)
  | switch {as : List PositiveMass} {seed : List NativeResourceMark} {k : ℕ} {T : ClockTree S as}
      {P : NativeResourceTerm i star T} (h : NativePhysicalResourceGenerated i star U seed k T P)
      (a : ℝ) (c : T.Slot) (hstar : star<U) (hhigh : U≤T.splitIndex P.live.test.target c) :
      NativePhysicalResourceGenerated i star U seed (k+1)
        (nativeFreshAtSlot T a P.live.test.target star).tree (P.switch a k c hstar hhigh)
  | switchFreshHigh {as : List PositiveMass} {seed : List NativeResourceMark} {k : ℕ}
      {T : ClockTree S as} {P : NativeResourceTerm i star T}
      (h : NativePhysicalResourceGenerated i star U seed k T P) (a : ℝ) (j : ℕ)
      (hjU : U≤j) (hj : j≤as.length) (hstar : star<U) :
      NativePhysicalResourceGenerated i star U seed (k+1)
        (nativeFreshAtSlot (nativeFreshAtSlot T a P.live.test.target j).tree a
          ((nativeFreshAtSlot T a P.live.test.target j).embed P.live.test.target) star).tree
        (P.switchFreshHigh a k j U hjU hj hstar)

theorem NativePhysicalResourceGenerated.to_resource_generated
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {seed : List NativeResourceMark} {k : ℕ} {P : NativeResourceTerm i star T}
    (h : NativePhysicalResourceGenerated i star U seed k T P) :
    NativeResourceGenerated i star seed k T P := by
  induction h with
  | constant as hU=>exact .constant (single as) (singleSlot as)
  | seed as hU a mark hm hl=>exact .seed (single as) a (singleSlot as) mark hm hl
  | freeze h ih=>exact .freeze ih
  | reweight h c ih=>exact .reweight ih c
  | retarget h a ih=>exact .retarget ih a
  | projection h a hl ih=>exact .projection ih a hl
  | switch h a c hs hh ih=>exact .switch ih a c hs hh
  | switchFreshHigh h a j hjU hj hs ih=>exact .switchFreshHigh ih a j U hjU hj hs

theorem NativePhysicalResourceGenerated.persistentLowForks
    {i star U : ℕ} {as : List PositiveMass} {T : ClockTree S as}
    {seed : List NativeResourceMark} {k : ℕ} {P : NativeResourceTerm i star T}
    (h : NativePhysicalResourceGenerated i star U seed k T P) : NativePersistentLowForks i star U T := by
  induction h with
  | constant as hU=>exact native_single_persistentLowForks i star U hU
  | seed as hU a mark hm hl=>
    apply (native_single_persistentLowForks i star U hU).graft a (singleSlot as) (mark.cut i star)
    rcases hm with rfl|rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  | freeze h ih=>exact ih
  | reweight h c ih=>exact ih
  | retarget h a ih=>exact ih.freshStar a _
  | projection h a hl ih=>exact ih.freshStar a _
  | switch h a c hs hh ih=>exact ih.freshStar a _
  | switchFreshHigh h a j hjU hj hs ih=>exact (ih.highRelative a _ hjU).freshStar a _

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
variable [MeasurableSpace S] [StandardBorelSpace S]

theorem native_physical_generated_source_four_tooth
    (pre mid tail : List PositiveMass) {T : ClockTree S (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativePhysicalResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hU : pre.length+mid.length<U)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    NativeClassifiedSourceFourToothLaw pre mid tail T P.live.test.target w φ v q x :=
  native_classified_source_and_four_tooth_disorder pre mid tail T P.live.test.target hU
    hP.persistentLowForks hw φ ho v q x

end OAI.SKFluctuations.Cavity
