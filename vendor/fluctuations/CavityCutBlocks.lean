module

public import CavityMomentAllocation

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal

namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type*}

theorem splitIndex_symm {as : List PositiveMass} (T : ClockTree S as) (s t : T.Slot) :
    T.splitIndex s t = T.splitIndex t s := by
  induction T with
  | leaf => rfl
  | step a T ih => exact congrArg (1+·) (ih s t)
  | fork T V ihT ihV => cases s <;> cases t <;> first | rfl | exact ihT _ _ | exact ihV _ _

theorem splitIndex_cut_trans {as : List PositiveMass} (T : ClockTree S as)
    (U : ℕ) (s t r : T.Slot) :
    U ≤ T.splitIndex s t → U ≤ T.splitIndex t r → U ≤ T.splitIndex s r := by
  induction T generalizing U with
  | leaf => simp only [splitIndex]; omega
  | step a T ih =>
    cases U with
    | zero => omega
    | succ U =>
      simpa only [splitIndex, Nat.succ_eq_add_one, Nat.add_comm 1,
        Nat.add_le_add_iff_right] using ih U s t r
  | fork T V ihT ihV =>
    cases s <;> cases t <;> cases r <;> simp only [splitIndex, Sum.elim_inl, Sum.elim_inr]
    all_goals first | exact ihT U _ _ _ | exact ihV U _ _ _ | omega

def cutBlockSetoid {as : List PositiveMass} (T : ClockTree S as) (U : ℕ)
    (hU : U ≤ as.length) : Setoid T.Slot where
  r s t := U ≤ T.splitIndex s t
  iseqv := ⟨fun s => by rw [T.splitIndex_self]; exact hU,
    fun {_ _} h => by rwa [T.splitIndex_symm],
    fun {_ _ _} h₁ h₂ => T.splitIndex_cut_trans U _ _ _ h₁ h₂⟩

abbrev CutBlock {as : List PositiveMass} (T : ClockTree S as) (U : ℕ)
    (hU : U ≤ as.length) := Quotient (T.cutBlockSetoid U hU)

def cutBlock {as : List PositiveMass} (T : ClockTree S as) (U : ℕ)
    (hU : U ≤ as.length) (s : T.Slot) : T.CutBlock U hU := Quotient.mk _ s

theorem cutBlock_eq_iff {as : List PositiveMass} (T : ClockTree S as) (U : ℕ)
    (hU : U ≤ as.length) (s t : T.Slot) :
    T.cutBlock U hU s = T.cutBlock U hU t ↔ U ≤ T.splitIndex s t :=
  Quotient.eq

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy
variable {S : Type*}

theorem blockDegree_eq_count_cutBlock {as : List PositiveMass} (T : ClockTree S as)
    (U : ℕ) (hU : U ≤ as.length) (s : T.Slot) (es : List T.Slot) :
    letI : DecidableEq (T.CutBlock U hU) := Classical.decEq _
    blockDegree T U s es =
      (es.map (T.cutBlock U hU)).count (T.cutBlock U hU s) := by
  classical
  induction es with
  | nil => rfl
  | cons a es ih =>
    simp only [blockDegree, List.map_cons, List.count_cons, ih]
    have heq : T.cutBlock U hU a = T.cutBlock U hU s ↔ U ≤ T.splitIndex s a := by
      rw [T.cutBlock_eq_iff, T.splitIndex_symm]
    by_cases ha : U ≤ T.splitIndex s a
    · simp [ha, heq.mpr ha, Nat.add_comm]
    · have hn : T.cutBlock U hU a ≠ T.cutBlock U hU s := fun h => ha (heq.mp h)
      simp [ha, hn]

end OAI.SKFluctuations.Cavity
