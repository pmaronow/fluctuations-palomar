module

public import CavityAttachedTree

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S V ι : Type*} [Fintype S] [Fintype V] [Fintype ι]

 def relabelSpin (e : S ≃ V) : {as : List PositiveMass} → ClockTree S as → ClockTree V as
  | _, .leaf => .leaf
  | _, .step a R => .step a (R.relabelSpin e)
  | _, .fork R U => .fork (R.relabelSpin e) (U.relabelSpin e)

 def relabelAssignment (e : S ≃ V) : {as : List PositiveMass} →
    (R : ClockTree S as) → R.Assignment ≃ (R.relabelSpin e).Assignment
  | _, .leaf => e
  | _, .step _ R => R.relabelAssignment e
  | _, .fork R U => (R.relabelAssignment e).prodCongr (U.relabelAssignment e)

 theorem weight_relabelSpin (e : S ≃ V) (w : V → ℝ)
    (φ : V → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (R : ClockTree S as) (q : ℕ → ι → ℝ≥0) (σ : R.Assignment) (x : ι → ℝ) :
    R.weight (w ∘ e) (φ ∘ e) q σ x =
      (R.relabelSpin e).weight w φ q (R.relabelAssignment e σ) x := by
  induction R generalizing q x with
  | leaf => exact spinWeight_spin_equiv e w φ x σ
  | @step a as R ih =>
    change shiftedMean _ a.val (gaussianHierarchy (w ∘ e) (φ ∘ e) (clockSteps as (fun j => q (j+1))))
      (R.weight (w ∘ e) (φ ∘ e) (fun j => q (j+1)) σ) x =
      shiftedMean _ a.val (gaussianHierarchy w φ (clockSteps as (fun j => q (j+1))))
        ((R.relabelSpin e).weight w φ (fun j => q (j+1)) (R.relabelAssignment e σ)) x
    rw [funext (gaussianHierarchy_spin_equiv e w φ (clockSteps as (fun j => q (j+1))))]
    congr 1
    funext y
    exact ih _ σ y
  | fork R U ihR ihU =>
    change R.weight (w ∘ e) (φ ∘ e) q σ.1 x*U.weight (w ∘ e) (φ ∘ e) q σ.2 x = _
    rw [ihR,ihU]
    rfl

 theorem disorderWeight_relabelSpin (e : S ≃ V) (w : V → ℝ)
    (φ : V → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (R : ClockTree S as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (σ : R.Assignment) (x : ι → ℝ) :
    R.disorderWeight (w ∘ e) (φ ∘ e) v q σ x =
      (R.relabelSpin e).disorderWeight w φ v q (R.relabelAssignment e σ) x := by
  unfold ClockTree.disorderWeight
  simp_rw [weight_relabelSpin]

 theorem disorderExpect_relabelSpin (e : S ≃ V) (w : V → ℝ)
    (φ : V → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (R : ClockTree S as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (P : (R.relabelSpin e).Assignment → ℝ) (x : ι → ℝ) :
    R.disorderExpect (w ∘ e) (φ ∘ e) v q (fun σ => P (R.relabelAssignment e σ)) x =
      (R.relabelSpin e).disorderExpect w φ v q P x := by
  unfold ClockTree.disorderExpect
  simp_rw [disorderWeight_relabelSpin]
  exact (R.relabelAssignment e).sum_comp (fun σ =>
    (R.relabelSpin e).disorderWeight w φ v q σ x*P σ)

 def relabelSlot (e : S ≃ V) : {as : List PositiveMass} →
    (R : ClockTree S as) → R.Slot ≃ (R.relabelSpin e).Slot
  | _, .leaf => Equiv.refl _
  | _, .step _ R => R.relabelSlot e
  | _, .fork R U => (R.relabelSlot e).sumCongr (U.relabelSlot e)

 theorem atSlot_relabel (e : S ≃ V) {as : List PositiveMass}
    (R : ClockTree S as) (σ : R.Assignment) (s : R.Slot) :
    (R.relabelSpin e).atSlot (R.relabelAssignment e σ) (R.relabelSlot e s) = e (R.atSlot σ s) := by
  induction R with
  | leaf => rfl
  | step a R ih => exact ih σ s
  | fork R U ihR ihU =>
    rcases s with s|s
    · exact ihR σ.1 s
    · exact ihU σ.2 s

 theorem splitIndex_relabel (e : S ≃ V) {as : List PositiveMass}
    (R : ClockTree S as) (s t : R.Slot) :
    (R.relabelSpin e).splitIndex (R.relabelSlot e s) (R.relabelSlot e t) = R.splitIndex s t := by
  induction R with
  | leaf => rfl
  | step a R ih => exact congrArg (fun z => 1+z) (ih s t)
  | fork R U ihR ihU =>
    rcases s with s|s <;> rcases t with t|t
    · exact ihR s t
    · rfl
    · rfl
    · exact ihU s t

end OAI.SKFluctuations.Hierarchy.ClockTree
