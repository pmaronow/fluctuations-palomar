module

public import CavityFullRetainedCoefficients

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S B : Type*}

def assignmentOfSlots : {as : List PositiveMass} → (T : ClockTree S as) →
    (T.Slot→S) → T.Assignment
  | _,.leaf,f => f ()
  | _,.step _ T,f => assignmentOfSlots T f
  | _,.fork T V,f => (assignmentOfSlots T (fun s=>f (.inl s)),
      assignmentOfSlots V (fun s=>f (.inr s)))

theorem atSlot_assignmentOfSlots {as : List PositiveMass} (T : ClockTree S as)
    (f : T.Slot→S) (s : T.Slot) : T.atSlot (assignmentOfSlots T f) s=f s := by
  induction T with
  | leaf => cases s; rfl
  | step b T ih => exact ih f s
  | fork T V ihT ihV => cases s <;> first | exact ihT _ _ | exact ihV _ _

theorem assignmentOfSlots_atSlot {as : List PositiveMass} (T : ClockTree S as)
    (σ : T.Assignment) : assignmentOfSlots T (T.atSlot σ)=σ := by
  induction T with
  | leaf => rfl
  | step b T ih => exact ih σ
  | fork T V ihT ihV => exact Prod.ext (ihT σ.1) (ihV σ.2)

theorem assignment_ext {as : List PositiveMass} (T : ClockTree S as)
    {σ τ : T.Assignment} (h : ∀ s, T.atSlot σ s=T.atSlot τ s) : σ=τ := by
  rw [←assignmentOfSlots_atSlot T σ,←assignmentOfSlots_atSlot T τ]
  exact congrArg (assignmentOfSlots T) (funext h)

def cavityLeftSlot : {as : List PositiveMass} → (T : ClockTree (S×B) as) →
    T.Slot≃T.cavityLeft.Slot
  | _,.leaf => Equiv.refl _
  | _,.step _ T => cavityLeftSlot T
  | _,.fork T V => (cavityLeftSlot T).sumCongr (cavityLeftSlot V)

theorem atSlot_cavityLeft {as : List PositiveMass} (T : ClockTree (S×B) as)
    (σ : T.Assignment) (s : T.Slot) :
    T.cavityLeft.atSlot (T.cavityAssignment σ).1 (cavityLeftSlot T s)=(T.atSlot σ s).1 := by
  induction T with
  | leaf => rfl
  | step b T ih => exact ih σ s
  | fork T V ihT ihV => cases s <;> first | exact ihT _ _ | exact ihV _ _

namespace MarkedPlacement

def restRestrict {as : List PositiveMass} {T : ClockTree (S×B) as}
    (p : MarkedPlacement T) (τ : p.tree.cavityLeft.Assignment) : T.cavityLeft.Assignment :=
  assignmentOfSlots T.cavityLeft (fun s=>p.tree.cavityLeft.atSlot τ
    (cavityLeftSlot p.tree (p.embed ((cavityLeftSlot T).symm s))))

def restSpin {as : List PositiveMass} {T : ClockTree (S×B) as}
    (p : MarkedPlacement T) (τ : p.tree.cavityLeft.Assignment) : S :=
  p.tree.cavityLeft.atSlot τ (cavityLeftSlot p.tree p.mark)

theorem restRestrict_at {as : List PositiveMass} {T : ClockTree (S×B) as}
    (p : MarkedPlacement T) (τ : p.tree.cavityLeft.Assignment) (s : T.Slot) :
    T.cavityLeft.atSlot (restRestrict p τ) (cavityLeftSlot T s)=
      p.tree.cavityLeft.atSlot τ (cavityLeftSlot p.tree (p.embed s)) := by
  simp only [restRestrict,atSlot_assignmentOfSlots,Equiv.symm_apply_apply]

theorem restRestrict_actual {as : List PositiveMass} {T : ClockTree (S×B) as}
    (p : MarkedPlacement T) (σ : p.tree.Assignment) :
    (T.cavityAssignment (p.restrict σ)).1=restRestrict p (p.tree.cavityAssignment σ).1 := by
  apply T.cavityLeft.assignment_ext
  intro s
  obtain ⟨s,rfl⟩:=(cavityLeftSlot T).surjective s
  rw [atSlot_cavityLeft,restRestrict_at,atSlot_cavityLeft,p.restrict_at]

theorem restSpin_actual {as : List PositiveMass} {T : ClockTree (S×B) as}
    (p : MarkedPlacement T) (σ : p.tree.Assignment) :
    (p.spin σ).1=restSpin p (p.tree.cavityAssignment σ).1 := by
  rw [restSpin,atSlot_cavityLeft,p.spin_at]

end MarkedPlacement
end OAI.SKFluctuations.Hierarchy.ClockTree
