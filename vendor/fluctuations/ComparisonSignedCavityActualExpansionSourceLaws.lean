module

public import ComparisonSignedCavityActualResourceExpansion
public import ComparisonSignedCavityActualSameFreshSourceMarginals

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
variable [MeasurableSpace S] [StandardBorelSpace S]

theorem native_actual_generated_source_four_tooth
    (pre mid tail : List PositiveMass) {T : ClockTree S (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hU : pre.length+mid.length<U)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    NativeClassifiedSourceFourToothLaw pre mid tail T P.live.test.target w φ v q x :=
  native_classified_source_and_four_tooth_disorder pre mid tail T P.live.test.target hU
    (hP.persistentLowForks (by omega)) hw φ ho v q x

theorem native_actual_generated_frozen_source_four_tooth
    (pre mid tail : List PositiveMass) {T : ClockTree S (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hU : pre.length+mid.length<U)
    (F : NativeFrozenResource S (pre++(mid++tail)) pre.length (pre.length+mid.length))
    (hF : F∈P.frozen)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a : ℝ} (ho : MassOrdered a (pre++(mid++tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    NativeClassifiedSourceFourToothLaw pre mid tail F.tree F.monomial.test.target w φ v q x :=
  native_classified_source_and_four_tooth_disorder pre mid tail F.tree F.monomial.test.target hU
    (hP.frozenLowForks (by omega) F hF) hw φ ho v q x

theorem native_actual_initial_expansion_source_four_tooth
    (pre mid tail : List PositiveMass) (U : ℕ) (hU : pre.length+mid.length<U)
    (hlen : U≤(pre++(mid++tail)).length) (a : ℝ)
    (Γ : (st : NativeHighSwitchState S (pre++(mid++tail))) → MarkedPlacement st.tree → ℝ)
    (ops : List NativeActualExpansionOp)
    (Q : NativeActualResourceState S (pre++(mid++tail)) pre.length (pre.length+mid.length))
    (hQ : Q∈nativeActualResourceExpansion Γ hU (by omega) ops
      (nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length) a (by omega)))
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    NativeClassifiedSourceFourToothLaw pre mid tail Q.tree Q.term.live.test.target w φ v q x :=
  native_actual_generated_source_four_tooth pre mid tail
    (nativeActualInitialExpansion_valid _ _ _ U (by omega) hU hlen a Γ ops Q hQ) hU hw φ ho v q x

theorem native_actual_generated_observed_full_fresh_anchor_with_old_moments
    (n : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (c b : T.Slot) (hh : U ≤ p.tree.splitIndex p.mark (p.embed c))
    (hcb : T.splitIndex c b=pre.length)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ) (x : RestCoordinate n → ℝ) :
    NativeActualFullFreshAnchorMomentLaw n pre mid tail p.tree (p.embed c) p.mark (p.embed b) a₀ v q x := by
  have hSource:=(hP.persistentLowForks (by omega)).observedHigh (by omega) hU a p hp c hh
  have hSplit : p.tree.splitIndex (p.embed c) (p.embed b)=pre.length := by
    rw [(T.markedAttach_embed_preserves a p hp).2,hcb]
  have hHigh : U ≤ p.tree.splitIndex (p.embed c) p.mark := by
    rw [p.tree.splitIndex_symm]
    exact hh
  exact native_actual_full_fresh_anchor_with_old_moments n pre mid tail p.tree
    (p.embed c) p.mark (p.embed b) hmid hU hSource hSplit hHigh ho v q x

theorem native_actual_generated_observed_full_same_fresh_anchor_with_old_moments
    (n : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (c b : T.Slot) (hh : U ≤ p.tree.splitIndex p.mark (p.embed c))
    (hcb : T.splitIndex c b=pre.length+mid.length)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ) (x : RestCoordinate n → ℝ) :
    NativeActualFullSameFreshAnchorMomentLaw n pre mid tail p.tree (p.embed c) p.mark (p.embed b) a₀ v q x := by
  have hSource:=(hP.persistentLowForks (by omega)).observedHigh (by omega) hU a p hp c hh
  have hSplit : p.tree.splitIndex (p.embed c) (p.embed b)=pre.length+mid.length := by
    rw [(T.markedAttach_embed_preserves a p hp).2,hcb]
  have hHigh : U ≤ p.tree.splitIndex (p.embed c) p.mark := by
    rw [p.tree.splitIndex_symm]
    exact hh
  exact native_actual_full_same_fresh_anchor_with_old_moments n pre mid tail p.tree
    (p.embed c) p.mark (p.embed b) hmid hU hSource hSplit hHigh ho v q x

theorem native_actual_initial_expansion_observed_full_fresh_anchor_with_old_moments
    (n : ℕ) (pre mid tail : List PositiveMass) (U : ℕ) (hmid : 0 < mid.length)
    (hU : pre.length+mid.length<U) (hlen : U≤(pre++(mid++tail)).length) (a : ℝ)
    (Γ : (st : NativeHighSwitchState (Spin n×Bool) (pre++(mid++tail))) → MarkedPlacement st.tree → ℝ)
    (ops : List NativeActualExpansionOp)
    (Q : NativeActualResourceState (Spin n×Bool) (pre++(mid++tail)) pre.length (pre.length+mid.length))
    (hQ : Q∈nativeActualResourceExpansion Γ hU (by omega) ops
      (nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length) a (by omega)))
    (a₁ : ℝ) (p : MarkedPlacement Q.tree) (hp : p∈Q.tree.markedAttach a₁)
    (c b : Q.tree.Slot) (hh : U ≤ p.tree.splitIndex p.mark (p.embed c))
    (hcb : Q.tree.splitIndex c b=pre.length)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ) (x : RestCoordinate n → ℝ) :
    NativeActualFullFreshAnchorMomentLaw n pre mid tail p.tree (p.embed c) p.mark (p.embed b) a₀ v q x :=
  native_actual_generated_observed_full_fresh_anchor_with_old_moments n pre mid tail
    (nativeActualInitialExpansion_valid _ _ _ U (by omega) hU hlen a Γ ops Q hQ)
    hmid hU a₁ p hp c b hh hcb ho v q x

end OAI.SKFluctuations.Cavity
