module

public import ComparisonSignedCavitySecondLowUnobservedErrorEntrySource
public import ComparisonSignedCavitySecondLowOriginalEntrySplitIndices

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable

def nativeSecondLowErrorEntryAnchor {α : Type*} (a z : α) (j : Fin 8) (firstError : Bool) : α :=
  if firstError then (if j.val<4 then a else z) else (if j.val<4 then z else a)

theorem native_second_low_original_error_cut_eq_entry_departure
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (U : ℕ) (hU : U ≤ as.length) (a z : T.Slot) (j : Fin 8) (firstError : Bool)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (Hpath : nativeSecondLowWordPath U hU a z p r s t j)
    (Hfirst : r.tree.splitIndex (r.embed p.mark) r.mark<U)
    (Hsecond : t.tree.splitIndex (t.embed s.mark) t.mark<U) :
    nativeSecondLowErrorCut firstError p r s t=
      nativeSecondLowEntryDepartureCut (nativeSecondLowErrorEntryAnchor a z j firstError) j p r := by
  have H:=native_second_low_original_word_LOW_indices_eq_entry_departures T U hU a z j
    p r hr s hs t ht Hpath Hfirst Hsecond
  cases firstError
  · by_cases Hj : j.val<4
    · simpa only [nativeSecondLowErrorCut,nativeSecondLowErrorEntryAnchor,Bool.false_eq_true,ite_false,Hj,ite_true] using H.2
    · simpa only [nativeSecondLowErrorCut,nativeSecondLowErrorEntryAnchor,Bool.false_eq_true,ite_false,Hj] using H.2
  · by_cases Hj : j.val<4
    · simpa only [nativeSecondLowErrorCut,nativeSecondLowErrorEntryAnchor,ite_true,Hj] using H.1
    · simpa only [nativeSecondLowErrorCut,nativeSecondLowErrorEntryAnchor,ite_true,Hj,ite_false] using H.1

def nativeSecondLowMovingErrorUnobservedWord (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (i star U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (hU : U ≤ as.length) (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot)
    (j : Fin 8) (firstError : Bool) (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) : ℝ :=
  if nativeSecondLowErrorCut firstError p r s t≠i ∧ nativeSecondLowErrorCut firstError p r s t≠star
    then nativeSecondLowUnobservedErrorWord n q U b h K hU P a z j firstError p r s t else 0

def nativeSecondLowMovingErrorUnobservedClassLedger (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (i star U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (hU : U ≤ as.length) (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot)
    (j : Fin 8) (firstError : Bool) : ℝ :=
  nativeSecondLowDoubleAverage T (fun p r=>nativeSecondLowDoubleAverage r.tree
    (nativeSecondLowMovingErrorUnobservedWord n q i star U b h K hU P a z j firstError p r))

theorem native_second_low_moving_error_unobserved_class_eq_entry
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (i star U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (hU : U ≤ as.length)
    (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot) (j : Fin 8) (firstError : Bool) :
    nativeSecondLowMovingErrorUnobservedClassLedger n q i star U b h K T hU P a z j firstError=
      nativeSecondLowEntryFourAverage T U (nativeSecondLowFirstMiddleIsFirst j)
        (nativeSecondLowMovingErrorUnobservedWord n q i star U b h K hU P a z j firstError) := by
  unfold nativeSecondLowMovingErrorUnobservedClassLedger
  apply native_second_low_four_average_eq_entry_four_average
  intro p hp r hr s hs t ht Hentry
  unfold nativeSecondLowMovingErrorUnobservedWord
  split_ifs
  · exact native_second_low_unobserved_error_word_zero_outside_entry n q U b h K T hU P a z j firstError
      p hp r hr s hs t ht Hentry
  · rfl

theorem native_second_low_unobserved_error_word_eq_split_allocations
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (i star U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} (hU : U ≤ as.length)
    (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot) (j : Fin 8) (firstError : Bool)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) (histar : i≠star) :
    nativeSecondLowUnobservedErrorWord n q U b h K hU P a z j firstError p r s t=
      nativeSecondLowFixedErrorUnobservedWord n q i U b h K hU P a z j firstError p r s t+
      nativeSecondLowFixedErrorUnobservedWord n q star U b h K hU P a z j firstError p r s t+
      nativeSecondLowMovingErrorUnobservedWord n q i star U b h K hU P a z j firstError p r s t := by
  unfold nativeSecondLowFixedErrorUnobservedWord nativeSecondLowMovingErrorUnobservedWord
  by_cases Hi : nativeSecondLowErrorCut firstError p r s t=i
  · simp [Hi,histar]
  · by_cases Hs : nativeSecondLowErrorCut firstError p r s t=star
    · simp [Hs,Ne.symm histar]
    · simp only [Hi,Hs,ne_eq,not_false_eq_true,true_and,ite_true,ite_false,zero_add]

theorem native_second_low_unobserved_error_class_eq_split_allocations
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (i star U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (hU : U ≤ as.length)
    (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot) (j : Fin 8) (firstError : Bool) (histar : i≠star) :
    nativeSecondLowUnobservedErrorClassLedger n q U b h K T hU P a z j firstError=
      nativeSecondLowFixedErrorUnobservedClassLedger n q i U b h K T hU P a z j firstError+
      nativeSecondLowFixedErrorUnobservedClassLedger n q star U b h K T hU P a z j firstError+
      nativeSecondLowMovingErrorUnobservedClassLedger n q i star U b h K T hU P a z j firstError := by
  unfold nativeSecondLowUnobservedErrorClassLedger nativeSecondLowFixedErrorUnobservedClassLedger
    nativeSecondLowMovingErrorUnobservedClassLedger
  rw [←native_second_low_double_average_add,←native_second_low_double_average_add]
  apply native_second_low_double_average_congr
  intro p _hp r _hr
  rw [←native_second_low_double_average_add,←native_second_low_double_average_add]
  apply native_second_low_double_average_congr
  intro s _hs t _ht
  exact native_second_low_unobserved_error_word_eq_split_allocations n q i star U b h K hU P a z
    j firstError p r s t histar

end OAI.SKFluctuations.Cavity
