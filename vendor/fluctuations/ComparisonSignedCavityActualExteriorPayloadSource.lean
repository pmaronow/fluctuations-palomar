module

public import ComparisonSignedCavityTwoLevelExteriorPayload
public import ComparisonSignedCavityActualExpansionSourceLaws

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
variable [MeasurableSpace S] [StandardBorelSpace S]

theorem native_actual_generated_exterior_payload
    (pre mid tail : List PositiveMass) {T : ClockTree S (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length < U)
    (hlen : U ≤ pre.length+mid.length+tail.length)
    {w : S → ℝ} (hw : ∀σ,0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    NativeClassifiedExteriorPayloadLaw pre mid tail T P.live.test.target w φ v q x :=
  native_classified_source_exterior_payload pre mid tail T P.live.test.target hmid hU hlen
    (hP.persistentLowForks (by omega)) hw φ ho v q x

theorem native_actual_initial_expansion_exterior_payload
    (pre mid tail : List PositiveMass) (U : ℕ) (hmid : 0 < mid.length)
    (hU : pre.length+mid.length < U) (hlen : U ≤ (pre++(mid++tail)).length) (a : ℝ)
    (Γ : (st : NativeHighSwitchState S (pre++(mid++tail))) → MarkedPlacement st.tree → ℝ)
    (ops : List NativeActualExpansionOp)
    (Q : NativeActualResourceState S (pre++(mid++tail)) pre.length (pre.length+mid.length))
    (hQ : Q∈nativeActualResourceExpansion Γ hU (by omega) ops
      (nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length) a (by omega)))
    {w : S → ℝ} (hw : ∀σ,0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    NativeClassifiedExteriorPayloadLaw pre mid tail Q.tree Q.term.live.test.target w φ v q x :=
  native_actual_generated_exterior_payload pre mid tail
    (nativeActualInitialExpansion_valid _ _ _ U (by omega) hU hlen a Γ ops Q hQ)
    hmid hU (by simpa only [List.length_append,Nat.add_assoc] using hlen) hw φ ho v q x

theorem native_actual_generated_observed_full_rest_exterior_payload
    (n : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length < U)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (c : T.Slot) (hh : U ≤ p.tree.splitIndex p.mark (p.embed c))
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ) (x : RestCoordinate n → ℝ) :
    NativeClassifiedExteriorPayloadLaw pre mid tail p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed c)) (restWeight n) (restFeature n) v q x := by
  have hSource:=((hP.persistentLowForks (by omega)).observedHigh (by omega) hU a p hp c hh).cavityLeft
  have hlen : U ≤ pre.length+mid.length+tail.length := by
    have h:=p.tree.splitIndex_le_clockLength p.mark (p.embed c)
    simp only [List.length_append] at h
    omega
  exact native_classified_source_exterior_payload pre mid tail p.tree.cavityLeft
    (p.tree.cavityLeftSlot (p.embed c)) hmid hU hlen hSource (restWeight_pos n) (restFeature n)
    ho v q x

end OAI.SKFluctuations.Cavity
