module

public import ComparisonSignedCavitySecondLowObservedFreshOccupiedSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators
set_option maxHeartbeats 45000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

private theorem second_low_observed_sum_restrict {α : Type} [Fintype α]
    (p : α→Prop) (F : α→ℝ) (hzero : ∀x,¬p x→F x=0) :
    (∑x : α,F x)=∑x : {x // p x},F x.val := by
  have H:=Fintype.sum_subtype_add_sum_subtype p F
  have Hzero : (∑x : {x // ¬p x},F x.val)=0:=by
    apply Finset.sum_eq_zero
    intro x _
    exact hzero x.val x.property
  rw [Hzero,add_zero] at H
  exact H.symm

def nativeSecondLowFreshOccupiedUnweightedCSource
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ∑B : NativeSecondLowFreshOccupiedMiddleBlock T s star U hU,
    nativeSecondLowCanonicalUnweightedCSource n q U b h K g.tree
      (fun old=>P (g.restRestrict old)) (g.embed s)
      (nativeSecondLowOccupiedBlockRepresentative g.tree U hU B.val) g.mark

def nativeSecondLowFreshOccupiedResidualSource
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ∑B : NativeSecondLowFreshOccupiedMiddleBlock T s star U hU,
    nativeSecondLowCanonicalObservedResidualSource n q U b h K g.tree
      (fun old=>P (g.restRestrict old)) (g.embed s)
      (nativeSecondLowOccupiedBlockRepresentative g.tree U hU B.val) g.mark

theorem native_second_low_fresh_eight_occupied_half_eq_unweighted_add_residual
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U star : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (hstar : star<U) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ)
    (B : NativeSecondLowFreshOccupiedMiddleBlock T s star U hU) :
    let g:=nativeFreshAtSlot T 0 s star
    let Pg:=fun old=>P (g.restRestrict old)
    let v:=nativeSecondLowOccupiedBlockRepresentative g.tree U hU B.val
    (∑j : Fin 8,nativeSecondLowOccupiedBlockGammaPathLedger n q U b h K g.tree hU Pg (g.embed s) g.mark j B.val/2)=
      ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2*
        nativeSecondLowCanonicalUnweightedCSource n q U b h K g.tree Pg (g.embed s) v g.mark+
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        nativeSecondLowCanonicalObservedResidualSource n q U b h K g.tree Pg (g.embed s) v g.mark := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 s star
  have HAv : g.tree.cutBlock U hU (g.embed s)≠g.tree.cutBlock U hU
      (nativeSecondLowOccupiedBlockRepresentative g.tree U hU B.val):=by
    rw [native_second_low_occupied_block_representative_eq]
    exact B.property.1
  have HZv : g.tree.cutBlock U hU g.mark≠g.tree.cutBlock U hU
      (nativeSecondLowOccupiedBlockRepresentative g.tree U hU B.val):=by
    rw [native_second_low_occupied_block_representative_eq]
    exact B.property.2
  have HAz : g.tree.cutBlock U hU (g.embed s)≠g.tree.cutBlock U hU g.mark:=by
    intro HE
    have H:=(g.tree.cutBlock_eq_iff U hU _ _).mp HE
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self] at H
    omega
  rw [native_second_low_eight_occupied_gamma_half_eq_canonical_raw_source n q U b h K g.tree ho
    (by omega) hU (fun old=>P (g.restRestrict old)) (g.embed s) g.mark B.val HAv HZv HAz]
  have Hslot:=native_second_low_fresh_occupied_old_slot_exact T s star U hU B
  have Hav : T.splitIndex s (nativeSecondLowFreshOccupiedOldSlot T s star U hU B)<U:=by
    have H:=cut_block_ne_split_lt g.tree U hU _ _ HAv
    rw [Hslot,(nativeFreshAtSlot_old_splits T 0 s star).2] at H
    exact H
  have H:=native_second_low_actual_fresh_canonical_source_eq_unweighted_c_add_residual n q U star b h K T ho
    hstar hU P s (nativeSecondLowFreshOccupiedOldSlot T s star U hU B) s Hav
  dsimp only at H
  rw [←Hslot] at H
  exact H

theorem native_second_low_actual_fresh_observed_half_eq_grouped_unweighted_add_residual
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U star : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (hstar : star<U) (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    let Pg:=fun old=>P (g.restRestrict old)
    (∑j : Fin 8,nativeSecondLowClassLedger n q U b h K g.tree hU Pg (g.embed s) g.mark j true/2)=
      ((scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0)^2*
        nativeSecondLowFreshOccupiedUnweightedCSource n q U b h K T s star hU P+
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        nativeSecondLowFreshOccupiedResidualSource n q U b h K T s star hU P := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 s star
  have Haz : g.tree.splitIndex (g.embed s) g.mark<U:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split]
    exact lt_of_le_of_lt (Nat.min_le_left _ _) hstar
  change (∑j : Fin 8,nativeSecondLowClassLedger n q U b h K g.tree hU
    (fun old=>P (g.restRestrict old)) (g.embed s) g.mark j true/2)=_
  simp_rw [native_second_low_observed_class_eq_occupied_gamma_ledgers n q U b h K g.tree ho hU
    (fun old=>P (g.restRestrict old)) (g.embed s) g.mark Haz]
  simp only [Finset.sum_div]
  rw [Finset.sum_comm]
  rw [second_low_observed_sum_restrict
    (fun B=>g.tree.cutBlock U hU (g.embed s)≠B ∧ g.tree.cutBlock U hU g.mark≠B)
    (fun B=>∑j : Fin 8,nativeSecondLowOccupiedBlockGammaPathLedger n q U b h K g.tree hU
      (fun old=>P (g.restRestrict old)) (g.embed s) g.mark j B/2)]
  · unfold nativeSecondLowFreshOccupiedUnweightedCSource nativeSecondLowFreshOccupiedResidualSource
    dsimp only
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    dsimp only [g]
    apply Finset.sum_congr
    · ext B
      simp
    · intro B _
      exact native_second_low_fresh_eight_occupied_half_eq_unweighted_add_residual n q U star b h K T ho s hstar hU P B
  · intro B HB
    simp only [not_and_or,not_not] at HB
    apply Finset.sum_eq_zero
    intro j _
    rw [native_second_low_occupied_gamma_endpoint_block_ledger_zero n q U b h K g.tree ho hU
      (fun old=>P (g.restRestrict old)) (g.embed s) g.mark j B HB,zero_div]

end OAI.SKFluctuations.Cavity
