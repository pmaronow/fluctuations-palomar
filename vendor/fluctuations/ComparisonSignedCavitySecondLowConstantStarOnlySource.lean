module

public import ComparisonSignedCavitySecondLowMovingErrorEntrySource
public import ComparisonSignedCavitySecondLowSingleGraftObservedZero

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable

theorem native_second_low_unobserved_error_class_eq_star_add_moving
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (star U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (hU : U ≤ as.length)
    (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot) (j : Fin 8) (firstError : Bool) :
    nativeSecondLowUnobservedErrorClassLedger n q U b h K T hU P a z j firstError=
      nativeSecondLowFixedErrorUnobservedClassLedger n q star U b h K T hU P a z j firstError+
      nativeSecondLowMovingErrorUnobservedClassLedger n q star star U b h K T hU P a z j firstError := by
  unfold nativeSecondLowUnobservedErrorClassLedger nativeSecondLowFixedErrorUnobservedClassLedger
    nativeSecondLowMovingErrorUnobservedClassLedger
  rw [←native_second_low_double_average_add]
  apply native_second_low_double_average_congr
  intro p _hp r _hr
  rw [←native_second_low_double_average_add]
  apply native_second_low_double_average_congr
  intro s _hs t _ht
  unfold nativeSecondLowFixedErrorUnobservedWord nativeSecondLowMovingErrorUnobservedWord
  by_cases Hcut:nativeSecondLowErrorCut firstError p r s t=star <;> simp [Hcut]

theorem native_second_low_original_unobserved_class_eq_star_moving
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (star U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU : U ≤ as.length) (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot) (j : Fin 8) :
    nativeSecondLowClassLedger n q U b h K T hU P a z j false=
      nativeSecondLowFixedErrorUnobservedClassLedger n q star U b h K T hU P a z j true+
      nativeSecondLowFixedErrorUnobservedClassLedger n q star U b h K T hU P a z j false+
      nativeSecondLowMovingErrorUnobservedClassLedger n q star star U b h K T hU P a z j true+
      nativeSecondLowMovingErrorUnobservedClassLedger n q star star U b h K T hU P a z j false := by
  rw [native_second_low_original_unobserved_class_eq_error_classes n q U b h K T ho hU P a z j,
    native_second_low_unobserved_error_class_eq_star_add_moving,
    native_second_low_unobserved_error_class_eq_star_add_moving]
  ring

theorem native_second_low_single_fresh_graft_joint_ledger_half_eq_unobserved
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (star U : ℕ) (b h K : ℕ → ℝ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (hU : U ≤ as.length) (hstar : star<U)
    (P : (nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) star).tree.cavityLeft.Assignment → ℝ) :
    let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) star
    nativeSecondLowJointLedger n q U b h K g.tree P [g.embed (singleSlot as),g.mark]/2=
      ∑j : Fin 8,nativeSecondLowClassLedger n q U b h K g.tree hU P (g.embed (singleSlot as)) g.mark j false/2 := by
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) star
  have Hsplit:g.tree.splitIndex (g.embed (singleSlot as)) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,splitIndex_self,Nat.min_eq_left (by omega)]
  have H:=native_second_low_joint_ledger_half_eq_observed_unobserved n q U b h K g.tree ho hU P
    (g.embed (singleSlot as)) g.mark (Hsplit ▸ hstar)
  have HZ (j : Fin 8):nativeSecondLowClassLedger n q U b h K g.tree hU P (g.embed (singleSlot as)) g.mark j true=0:=
    native_second_low_single_fresh_graft_observed_class_zero n q U b h K as hU star P j
  simpa only [HZ,zero_div,Finset.sum_const_zero,zero_add] using H

end OAI.SKFluctuations.Cavity
