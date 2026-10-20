module

public import ComparisonSignedCavitySecondLowUnobservedRowReduction

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open scoped BigOperators
variable {S : Type} {as : List PositiveMass} {T : ClockTree S as}
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable

def nativeSecondLowBudgetEntryRows (T : ClockTree S as) (U : ℕ) (entry : Bool) : List (MarkedPlacement T) :=
  if entry then nativeSecondLowUnobservedEntryRows T U 0 else T.markedAttach 0

theorem native_second_low_budget_entry_rows_subset (T : ClockTree S as) (U : ℕ) (entry : Bool)
    (p : MarkedPlacement T) (hp : p ∈ nativeSecondLowBudgetEntryRows T U entry) : p ∈ T.markedAttach 0 := by
  cases entry with
  | false => exact hp
  | true => exact (mem_nativeSecondLowUnobservedEntryRows T U 0 p).mp hp |>.1

theorem native_second_low_budget_entry_rows_variation
    (T : ClockTree S as) (U : ℕ) (hU : U ≤ as.length) (ho : MassOrdered 0 as)
    (entry : Bool) {r : ℕ} (hT : T.leaves ≤ r) :
    ((nativeSecondLowBudgetEntryRows T U entry).map (fun p => |p.coeff|)).sum ≤
      2*(r:ℝ)*(if entry then partitionPoint 0 as U else 1) := by
  have hmass : 0 ≤ partitionPoint 0 as U := (partitionPoint_mem as ho U).1
  have hleaf : (T.leaves:ℝ) ≤ r := Nat.cast_le.mpr hT
  cases entry with
  | false =>
    simp only [nativeSecondLowBudgetEntryRows,Bool.false_eq_true,ite_false,mul_one,
      markedAttach_variation T ho,sub_zero]
    exact mul_le_mul_of_nonneg_left hleaf (by norm_num)
  | true =>
    have H := native_second_low_unobserved_entry_variation T U hU ho (by norm_num)
    simp only [sub_zero] at H
    exact H.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hleaf (by norm_num)) hmass)

def nativeSecondLowEntryFourAverage (T : ClockTree S as) (U : ℕ) (first : Bool)
    (F : (p : MarkedPlacement T) → (r : MarkedPlacement p.tree) →
      (s : MarkedPlacement r.tree) → MarkedPlacement s.tree → ℝ) : ℝ :=
  ((nativeSecondLowBudgetEntryRows T U first).map fun p => p.coeff *
    ((nativeSecondLowBudgetEntryRows p.tree U (!first)).map fun r => r.coeff *
      OAI.SKFluctuations.Cavity.nativeSecondLowDoubleAverage r.tree (F p r)).sum).sum/2

theorem native_second_low_entry_four_average_abs_le
    (T : ClockTree S as) (U : ℕ) (hU : U ≤ as.length) (ho : MassOrdered 0 as)
    {rBound : ℕ} (hT : T.leaves ≤ rBound) (first : Bool)
    (F : (p : MarkedPlacement T) → (r : MarkedPlacement p.tree) →
      (s : MarkedPlacement r.tree) → MarkedPlacement s.tree → ℝ)
    {D : ℝ} (hD : 0 ≤ D)
    (hF : ∀ p ∈ T.markedAttach 0, ∀ r ∈ p.tree.markedAttach 0,
      ∀ s ∈ r.tree.markedAttach 0, ∀ t ∈ s.tree.markedAttach 0, |F p r s t| ≤ D) :
    |nativeSecondLowEntryFourAverage T U first F| ≤
      (4*(rBound:ℝ)*(rBound+1)*(rBound+2)*(rBound+3))*partitionPoint 0 as U*D := by
  let B := (2*((rBound+2:ℕ):ℝ)*(rBound+3))*D
  have hB : 0 ≤ B := by dsimp [B];positivity
  have hmass : 0 ≤ partitionPoint 0 as U := (partitionPoint_mem as ho U).1
  have Hr (p : MarkedPlacement T) (hp : p ∈ T.markedAttach 0)
      (r : MarkedPlacement p.tree) (hr : r ∈ p.tree.markedAttach 0) :
      |OAI.SKFluctuations.Cavity.nativeSecondLowDoubleAverage r.tree (F p r)| ≤ B := by
    have Hp := T.markedAttach_leaves 0 p hp
    have HR := p.tree.markedAttach_leaves 0 r hr
    have Hleaves : r.tree.leaves ≤ rBound+2 := by omega
    convert marked_pair_weight_abs_le r.tree ho Hleaves (F p r) hD (hF p hp r hr) using 1
    · rfl
    · dsimp only [B]
      push_cast
      ring
  let inner := fun p : MarkedPlacement T =>
    ((nativeSecondLowBudgetEntryRows p.tree U (!first)).map fun r => r.coeff *
      OAI.SKFluctuations.Cavity.nativeSecondLowDoubleAverage r.tree (F p r)).sum
  have Hinner (p : MarkedPlacement T) (hp : p ∈ T.markedAttach 0) :
      |inner p| ≤ 2*((rBound+1:ℕ):ℝ)*(if !first then partitionPoint 0 as U else 1)*B := by
    have Hbound := marked_list_weight_abs_le (nativeSecondLowBudgetEntryRows p.tree U (!first))
      (fun r => OAI.SKFluctuations.Cavity.nativeSecondLowDoubleAverage r.tree (F p r))
      (fun r hr => Hr p hp r (native_second_low_budget_entry_rows_subset p.tree U (!first) r hr))
    have Hp : p.tree.leaves ≤ rBound+1 := (T.markedAttach_leaves 0 p hp).trans (Nat.add_le_add_right hT 1)
    exact Hbound.trans (mul_le_mul_of_nonneg_right
      (native_second_low_budget_entry_rows_variation p.tree U hU ho (!first) Hp) hB)
  have Houter := marked_list_weight_abs_le (nativeSecondLowBudgetEntryRows T U first) inner
    (fun p hp => Hinner p (native_second_low_budget_entry_rows_subset T U first p hp))
  have HBinner : 0 ≤ 2*((rBound+1:ℕ):ℝ)*(if !first then partitionPoint 0 as U else 1)*B := by
    cases first <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_true,ite_false] <;> positivity
  have Hbound := Houter.trans (mul_le_mul_of_nonneg_right
    (native_second_low_budget_entry_rows_variation T U hU ho first hT) HBinner)
  unfold nativeSecondLowEntryFourAverage
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ) < 2)]
  apply (div_le_div_of_nonneg_right Hbound (by norm_num)).trans_eq
  cases first <;> simp only [Bool.not_false,Bool.not_true,Bool.false_eq_true,ite_true,ite_false,B,
    Nat.cast_add,Nat.cast_ofNat] <;> ring

end OAI.SKFluctuations.Hierarchy.ClockTree
