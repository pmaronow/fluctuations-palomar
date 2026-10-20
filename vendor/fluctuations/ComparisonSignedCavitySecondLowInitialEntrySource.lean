module

public import ComparisonSignedCavitySecondLowEntryFourBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable

theorem native_second_low_four_average_eq_entry_four_average
    {S : Type} {as : List PositiveMass} (T : ClockTree S as) (U : ℕ) (first : Bool)
    (F : (p : MarkedPlacement T) → (r : MarkedPlacement p.tree) →
      (s : MarkedPlacement r.tree) → MarkedPlacement s.tree → ℝ)
    (hzero : ∀ p ∈ T.markedAttach 0, ∀ r ∈ p.tree.markedAttach 0,
      ∀ s ∈ r.tree.markedAttach 0, ∀ t ∈ s.tree.markedAttach 0,
      ¬(if first then p ∈ nativeSecondLowUnobservedEntryRows T U 0
        else r ∈ nativeSecondLowUnobservedEntryRows p.tree U 0) → F p r s t = 0) :
    nativeSecondLowDoubleAverage T (fun p r => nativeSecondLowDoubleAverage r.tree (F p r)) =
      nativeSecondLowEntryFourAverage T U first F := by
  let A := fun (p : MarkedPlacement T) (r : MarkedPlacement p.tree) =>
    nativeSecondLowDoubleAverage r.tree (F p r)
  have Hzero (p : MarkedPlacement T) (hp : p ∈ T.markedAttach 0)
      (r : MarkedPlacement p.tree) (hr : r ∈ p.tree.markedAttach 0)
      (Hentry : ¬(if first then p ∈ nativeSecondLowUnobservedEntryRows T U 0
        else r ∈ nativeSecondLowUnobservedEntryRows p.tree U 0)) : A p r = 0 := by
    dsimp only [A,nativeSecondLowDoubleAverage]
    have Ht (s : MarkedPlacement r.tree) (hs : s ∈ r.tree.markedAttach 0) :
        ((s.tree.markedAttach 0).map (fun t => t.coeff * F p r s t)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hx
      rw [hzero p hp r hr s hs t ht Hentry,mul_zero]
    have Hz : ((r.tree.markedAttach 0).map (fun s => s.coeff *
        ((s.tree.markedAttach 0).map (fun t => t.coeff * F p r s t)).sum)).sum = 0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hx
      rw [Ht s hs,mul_zero]
    rw [Hz,zero_div]
  change nativeSecondLowDoubleAverage T A = _
  unfold nativeSecondLowDoubleAverage nativeSecondLowEntryFourAverage nativeSecondLowBudgetEntryRows
  cases HF : first
  · simp only [Bool.false_eq_true,ite_false,Bool.not_false,ite_true]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    congr 1
    have Hsum := native_second_low_sum_filter_of_zero (p.tree.markedAttach 0)
      (fun r => ∀ v : p.tree.Slot, r.tree.splitIndex (r.embed v) r.mark < U) (fun r => r.coeff * A p r) (by
        intro r hr Hno
        have Hnot : r ∉ nativeSecondLowUnobservedEntryRows p.tree U 0 := by
          rw [mem_nativeSecondLowUnobservedEntryRows]
          simpa only [not_exists,not_le] using fun H : r ∈ p.tree.markedAttach 0 ∧
            (∀ v : p.tree.Slot, r.tree.splitIndex (r.embed v) r.mark < U) => Hno H.2
        rw [Hzero p hp r hr (by simpa only [HF,Bool.false_eq_true,ite_false] using Hnot),mul_zero])
    rw [nativeSecondLowUnobservedEntryRows_eq_filter]
    exact Hsum
  · simp only [ite_true,Bool.not_true,Bool.false_eq_true,ite_false]
    have Hsum := native_second_low_sum_filter_of_zero (T.markedAttach 0)
      (fun p => ∀ v : T.Slot, p.tree.splitIndex (p.embed v) p.mark < U)
      (fun p => p.coeff * ((p.tree.markedAttach 0).map (fun r => r.coeff * A p r)).sum) (by
        intro p hp Hno
        have Hnot : p ∉ nativeSecondLowUnobservedEntryRows T U 0 := by
          rw [mem_nativeSecondLowUnobservedEntryRows]
          simpa only [not_exists,not_le] using fun H : p ∈ T.markedAttach 0 ∧
            (∀ v : T.Slot, p.tree.splitIndex (p.embed v) p.mark < U) => Hno H.2
        have Hz : ((p.tree.markedAttach 0).map (fun r => r.coeff * A p r)).sum = 0 := by
          apply List.sum_eq_zero
          intro x hx
          obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
          rw [Hzero p hp r hr (by simpa only [HF,ite_true] using Hnot),mul_zero]
        rw [Hz,mul_zero])
    rw [nativeSecondLowUnobservedEntryRows_eq_filter]
    exact congrArg (fun x : ℝ => x/2) Hsum

def nativeSecondLowInitialUnobservedWord (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (i U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass} {T : ClockTree (Spin n × Bool) as}
    (hU : U ≤ as.length) (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot) (j : Fin 8)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) : ℝ :=
  if r.tree.splitIndex (r.embed p.mark) r.mark = i ∧ t.tree.splitIndex (t.embed s.mark) t.mark = i
  then nativeSecondLowUnobservedWord n q U b h K hU P a z j p r s t else 0

def nativeSecondLowInitialUnobservedClassLedger (n : ℕ) (q : ℕ → RestCoordinate n → ℝ)
    (i U : ℕ) (b h K : ℕ → ℝ) {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (hU : U ≤ as.length) (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot) (j : Fin 8) : ℝ :=
  nativeSecondLowDoubleAverage T (fun p r => nativeSecondLowDoubleAverage r.tree
    (nativeSecondLowInitialUnobservedWord n q i U b h K hU P a z j p r))

theorem native_second_low_initial_unobserved_class_eq_entry
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (i U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (hU : U ≤ as.length)
    (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot) (j : Fin 8) :
    nativeSecondLowInitialUnobservedClassLedger n q i U b h K T hU P a z j =
      nativeSecondLowEntryFourAverage T U (nativeSecondLowFirstMiddleIsFirst j)
        (nativeSecondLowInitialUnobservedWord n q i U b h K hU P a z j) := by
  unfold nativeSecondLowInitialUnobservedClassLedger
  apply native_second_low_four_average_eq_entry_four_average
  intro p hp r hr s hs t ht Hentry
  unfold nativeSecondLowInitialUnobservedWord
  split_ifs with H
  · exact native_second_low_unobserved_word_zero_outside_entry n q U b h K T hU P a z j p hp r hr s hs t ht Hentry
  · rfl

end OAI.SKFluctuations.Cavity
