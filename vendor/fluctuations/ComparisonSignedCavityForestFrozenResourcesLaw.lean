module

public import ComparisonSignedCavityForestObservedHighLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}

theorem NativePhysicalResourceGenerated.frozenLowForks {i star U k : ℕ}
    {seed : List NativeResourceMark} {T : ClockTree S as} {P : NativeResourceTerm i star T}
    (h : NativePhysicalResourceGenerated i star U seed k T P) :
    ∀F∈P.frozen,NativePersistentLowForks i star U F.tree := by
  induction h with
  | constant as hU=>intro F hF;cases hF
  | seed as hU a mark hm hl=>intro F hF;cases hF
  | freeze h ih=>
    intro F hF
    rcases List.mem_append.mp hF with hF|hF
    · exact ih F hF
    · obtain rfl:=List.mem_singleton.mp hF
      exact h.persistentLowForks
  | reweight h c ih=>exact ih
  | retarget h a ih=>exact ih
  | projection h a hl ih=>exact ih
  | switch h a c hs hh ih=>exact ih
  | switchFreshHigh h a j hjU hj hs ih=>exact ih

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
variable [MeasurableSpace S] [StandardBorelSpace S]

theorem native_physical_generated_frozen_source_four_tooth
    (pre mid tail : List PositiveMass) {T : ClockTree S (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativePhysicalResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hU : pre.length+mid.length<U)
    (F : NativeFrozenResource S (pre++(mid++tail)) pre.length (pre.length+mid.length))
    (hF : F∈P.frozen)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    NativeClassifiedSourceFourToothLaw pre mid tail F.tree F.monomial.test.target w φ v q x :=
  native_classified_source_and_four_tooth_disorder pre mid tail F.tree F.monomial.test.target hU
    (hP.frozenLowForks F hF) hw φ ho v q x

end OAI.SKFluctuations.Cavity
