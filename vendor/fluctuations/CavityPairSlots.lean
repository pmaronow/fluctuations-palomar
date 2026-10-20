module

public import CavityActualStarTransfer

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type*}

 def pairLeftSlot : (as : List PositiveMass) → (j : ℕ) → (pairClock (S:=S) as j).Slot
  | [], _ => Sum.inl ()
  | a::as, 0 => Sum.inl (singleSlot (a::as))
  | _::as, j+1 => pairLeftSlot as j

 def pairRightSlot : (as : List PositiveMass) → (j : ℕ) → (pairClock (S:=S) as j).Slot
  | [], _ => Sum.inr ()
  | a::as, 0 => Sum.inr (singleSlot (a::as))
  | _::as, j+1 => pairRightSlot as j

 theorem pairLeft_atSlot (as : List PositiveMass) (j : ℕ)
    (σ : (pairClock (S:=S) as j).Assignment) :
    (pairClock as j).atSlot σ (pairLeftSlot as j) = (pairSpin as j σ).1 := by
  induction as generalizing j with
  | nil => rfl
  | cons a as ih =>
    cases j with
    | zero => exact single_atSlot (a::as) σ.1
    | succ j => exact ih j σ

 theorem pairRight_atSlot (as : List PositiveMass) (j : ℕ)
    (σ : (pairClock (S:=S) as j).Assignment) :
    (pairClock as j).atSlot σ (pairRightSlot as j) = (pairSpin as j σ).2 := by
  induction as generalizing j with
  | nil => rfl
  | cons a as ih =>
    cases j with
    | zero => exact single_atSlot (a::as) σ.2
    | succ j => exact ih j σ

 theorem pairSlots_distinct (as : List PositiveMass) (j : ℕ) :
    pairLeftSlot (S:=S) as j ≠ pairRightSlot as j := by
  induction as generalizing j with
  | nil => exact Sum.inl_ne_inr
  | cons a as ih =>
    cases j with
    | zero => exact Sum.inl_ne_inr
    | succ j => exact ih j

 theorem pairSlots_splitIndex (as : List PositiveMass) (j : ℕ) :
    (pairClock (S:=S) as j).splitIndex (pairLeftSlot as j) (pairRightSlot as j) =
      min j as.length := by
  induction as generalizing j with
  | nil => simp only [pairClock,pairLeftSlot,pairRightSlot,splitIndex,Sum.elim_inl,
      Sum.elim_inr,List.length_nil,Nat.min_zero]
  | cons a as ih =>
    cases j with
    | zero => simp only [pairClock,pairLeftSlot,pairRightSlot,splitIndex,Sum.elim_inl,
        Sum.elim_inr,Nat.zero_min]
    | succ j =>
      simp only [pairClock,pairLeftSlot,pairRightSlot,splitIndex,List.length_cons]
      rw [ih]
      omega

end OAI.SKFluctuations.Hierarchy.ClockTree
