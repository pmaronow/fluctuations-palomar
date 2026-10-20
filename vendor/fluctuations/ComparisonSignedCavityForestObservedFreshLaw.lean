module

public import ComparisonSignedCavityForestTwinFreshLaw

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S B : Type}

theorem single_cavityLeft (as : List PositiveMass) :
    (single (S:=S×B) as).cavityLeft=single (S:=S) as := by
  induction as with
  | nil=>rfl
  | cons a as ih=>exact congrArg (fun T=>T.step a) ih

theorem nativeFreshAtSlot_cavityLeft_tree {as : List PositiveMass}
    (T : ClockTree (S×B) as) (a : ℝ) (s : T.Slot) (j : ℕ) :
    (nativeFreshAtSlot T a s j).tree.cavityLeft=
      (nativeFreshAtSlot T.cavityLeft a (T.cavityLeftSlot s) j).tree := by
  induction T generalizing a j with
  | leaf=>simp only [nativeFreshAtSlot,MarkedPlacement.fresh,cavityLeft,single_cavityLeft]
  | step b T ih=>
    cases j with
    | zero=>simp only [nativeFreshAtSlot,MarkedPlacement.fresh,cavityLeft,single_cavityLeft]
    | succ j=>exact congrArg (fun T=>T.step b) (ih b.val s j)
  | fork T V ihT ihV=>
    cases j with
    | zero=>simp only [nativeFreshAtSlot,MarkedPlacement.fresh,cavityLeft,single_cavityLeft]
    | succ j=>cases s with
      | inl s=>exact congrArg (fun Z=>Z.fork V.cavityLeft) (ihT a s (j+1))
      | inr s=>exact congrArg (fun Z=>T.cavityLeft.fork Z) (ihV a s (j+1))

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {ι S B : Type} [Fintype ι] [Fintype S] [Nonempty S]
variable [MeasurableSpace S] [StandardBorelSpace S]

theorem native_physical_generated_observed_fresh_partner_source
    (pre mid tail : List PositiveMass) {T : ClockTree (S×B) (pre++(mid++tail))}
    {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativePhysicalResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (hmid : 0 < mid.length) (hU : pre.length+mid.length<U)
    (a : ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach a)
    (c b : T.Slot) (hh : U≤p.tree.splitIndex p.mark (p.embed c))
    (hcb : T.splitIndex c b=pre.length)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ (pre++(mid++tail)))
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ) :
    NativeActualFreshTwoArmLaw pre mid tail p.tree.cavityLeft
      (p.tree.cavityLeftSlot (p.embed c)) (p.tree.cavityLeftSlot (p.embed b)) a₀ w φ v q x := by
  have hSource:=hP.persistentLowForks.observedRestHigh (by omega) hU a p hp c hh
  have hSplit : p.tree.cavityLeft.splitIndex
      (p.tree.cavityLeftSlot (p.embed c)) (p.tree.cavityLeftSlot (p.embed b))=pre.length := by
    rw [cavityLeft_splitIndex,(T.markedAttach_embed_preserves a p hp).2,hcb]
  exact native_actual_fresh_two_arm_disorder_factory pre mid tail p.tree.cavityLeft
    (p.tree.cavityLeftSlot (p.embed c)) (p.tree.cavityLeftSlot (p.embed b))
    hmid hU hSource hSplit hw φ ho v q x

end OAI.SKFluctuations.Cavity
