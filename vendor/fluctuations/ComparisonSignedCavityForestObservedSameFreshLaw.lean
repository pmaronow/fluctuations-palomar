module

public import ComparisonSignedCavityForestSameFreshLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S B : Type} [Fintype ι] [Fintype S] [Nonempty S]
variable [MeasurableSpace S] [StandardBorelSpace S]

theorem native_physical_generated_observed_same_star_fresh_partner_source
    (pre mid tail : List PositiveMass) {T : ClockTree (S×B) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativePhysicalResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (c b : T.Slot) (hh : U≤p.tree.splitIndex p.mark (p.embed c))
    (hcb : T.splitIndex c b=pre.length+mid.length)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    NativeActualFreshSameArmLaw pre mid tail p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed c)) (p.tree.cavityLeftSlot (p.embed b)) a₀ w φ v q x := by
  have hSource:=hP.persistentLowForks.observedRestHigh (by omega) hU a p hp c hh
  have hSplit : p.tree.cavityLeft.splitIndex
      (p.tree.cavityLeftSlot (p.embed c)) (p.tree.cavityLeftSlot (p.embed b))=pre.length+mid.length := by
    rw [cavityLeft_splitIndex,(T.markedAttach_embed_preserves a p hp).2,hcb]
  have hlen : U≤pre.length+mid.length+tail.length := by
    have HR : U≤p.tree.cavityLeft.splitIndex
        (p.tree.cavityLeftSlot p.mark) (p.tree.cavityLeftSlot (p.embed c)) := by
      simpa only [cavityLeft_splitIndex] using hh
    have H:=HR.trans (p.tree.cavityLeft.splitIndex_le_clockLength
      (p.tree.cavityLeftSlot p.mark) (p.tree.cavityLeftSlot (p.embed c)))
    simpa only [List.length_append,Nat.add_assoc] using H
  exact native_actual_fresh_same_arm_disorder_factory pre mid tail p.tree.cavityLeft
    (p.tree.cavityLeftSlot (p.embed c)) (p.tree.cavityLeftSlot (p.embed b))
    hmid hU hlen hSource hSplit hw φ ho v q x

end OAI.SKFluctuations.Cavity
