module

public import ComparisonSignedCavitySecondLowUnobservedSourceEntry
public import ComparisonSignedCavityForestObservedHighGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}
set_option maxHeartbeats 30000000

theorem native_second_low_block_split_transport
    (T : ClockTree S as) (U : ℕ) (hU : U ≤ as.length) (u v a c : T.Slot)
    (Hua : T.cutBlock U hU u=T.cutBlock U hU a)
    (Hvc : T.cutBlock U hU v=T.cutBlock U hU c) (Hlow : T.splitIndex u v<U) :
    T.splitIndex u v=T.splitIndex a c := by
  have H1:=T.splitIndex_low_eq_of_high a u v ((T.cutBlock_eq_iff U hU _ _).mp Hua.symm) Hlow
  have Hlow2:T.splitIndex v a<U:=by rw [T.splitIndex_symm v a,H1];exact Hlow
  have H2:=T.splitIndex_low_eq_of_high c v a ((T.cutBlock_eq_iff U hU _ _).mp Hvc.symm) Hlow2
  calc
    _=T.splitIndex a v:=H1.symm
    _=T.splitIndex c a:=by rw [T.splitIndex_symm a v];exact H2.symm
    _=T.splitIndex a c:=T.splitIndex_symm _ _

theorem native_second_low_unordered_block_split_transport
    (T : ClockTree S as) (U : ℕ) (hU : U ≤ as.length) (u v a c : T.Slot)
    (Hlow : T.splitIndex u v<U)
    (Hblocks : (T.cutBlock U hU u=T.cutBlock U hU a ∧ T.cutBlock U hU v=T.cutBlock U hU c) ∨
      (T.cutBlock U hU u=T.cutBlock U hU c ∧ T.cutBlock U hU v=T.cutBlock U hU a)) :
    T.splitIndex u v=T.splitIndex a c := by
  rcases Hblocks with ⟨Hu,Hv⟩ | ⟨Hu,Hv⟩
  · exact native_second_low_block_split_transport T U hU u v a c Hu Hv Hlow
  · rw [T.splitIndex_symm u v]
    exact native_second_low_block_split_transport T U hU v u a c Hv Hu (by rwa [T.splitIndex_symm])

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 30000000

def nativeSecondLowFirstEntrySlot {α : Type*} (j : Fin 8) (f c : α) : α :=
  if nativeSecondLowFirstMiddleIsFirst j then f else c

theorem native_second_low_path_low_splits_eq_entry_departures
    {S : Type} {as : List PositiveMass} (T : ClockTree S as) (U : ℕ) (hU : U ≤ as.length)
    (a z f c e d : T.Slot) (j : Fin 8)
    (Hpath : nativeSecondLowBlockPath j (T.cutBlock U hU a) (T.cutBlock U hU z)
      (T.cutBlock U hU f) (T.cutBlock U hU c) (T.cutBlock U hU e) (T.cutBlock U hU d))
    (Hfirst : T.splitIndex f c<U) (Hsecond : T.splitIndex e d<U) :
    T.splitIndex f c=T.splitIndex (if j.val<4 then a else z) (nativeSecondLowFirstEntrySlot j f c) ∧
    T.splitIndex e d=T.splitIndex (if j.val<4 then z else a) (nativeSecondLowFirstEntrySlot j f c) := by
  have HB1:
      (T.cutBlock U hU f=T.cutBlock U hU (if j.val<4 then a else z) ∧
        T.cutBlock U hU c=T.cutBlock U hU (nativeSecondLowFirstEntrySlot j f c)) ∨
      (T.cutBlock U hU f=T.cutBlock U hU (nativeSecondLowFirstEntrySlot j f c) ∧
        T.cutBlock U hU c=T.cutBlock U hU (if j.val<4 then a else z)) := by
    fin_cases j
    all_goals simp_all [nativeSecondLowBlockPath,nativeSecondLowFirstEntrySlot,nativeSecondLowFirstMiddleIsFirst]
  have HB2:
      (T.cutBlock U hU e=T.cutBlock U hU (if j.val<4 then z else a) ∧
        T.cutBlock U hU d=T.cutBlock U hU (nativeSecondLowFirstEntrySlot j f c)) ∨
      (T.cutBlock U hU e=T.cutBlock U hU (nativeSecondLowFirstEntrySlot j f c) ∧
        T.cutBlock U hU d=T.cutBlock U hU (if j.val<4 then z else a)) := by
    fin_cases j
    all_goals simp_all [nativeSecondLowBlockPath,nativeSecondLowFirstEntrySlot,nativeSecondLowFirstMiddleIsFirst]
  exact ⟨native_second_low_unordered_block_split_transport T U hU _ _ _ _ Hfirst HB1,
    native_second_low_unordered_block_split_transport T U hU _ _ _ _ Hsecond HB2⟩

end OAI.SKFluctuations.Cavity
