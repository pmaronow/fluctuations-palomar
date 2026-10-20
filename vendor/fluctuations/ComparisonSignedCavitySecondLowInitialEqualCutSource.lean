module

public import ComparisonSignedCavitySecondLowInitialEqualCutGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable

theorem native_second_low_fixed_initial_error_words_eq_both_initial_word
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (i U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU : U ≤ as.length) (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot)
    (Htarget : i<T.splitIndex a z) (haz : T.splitIndex a z<U) (j : Fin 8)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0) :
    nativeSecondLowFixedErrorUnobservedWord n q i U b h K hU P a z j true p r s t+
      nativeSecondLowFixedErrorUnobservedWord n q i U b h K hU P a z j false p r s t=
      nativeSecondLowInitialUnobservedWord n q i U b h K hU P a z j p r s t := by
  have hiU:i<U:=Htarget.trans haz
  by_cases Hfirst:r.tree.splitIndex (r.embed p.mark) r.mark<U
  · by_cases Hsecond:t.tree.splitIndex (t.embed s.mark) t.mark<U
    · by_cases Hsource:nativeSecondLowWordPath U hU a z p r s t j ∧ ¬nativeSecondLowWordObserved U p r s t j
      · have HE1:(r.tree.splitIndex (r.embed p.mark) r.mark=i) ↔
            (r.tree.splitIndex (r.embed p.mark) r.mark=i ∧ t.tree.splitIndex (t.embed s.mark) t.mark=i):=by
          refine ⟨fun H=>?_,And.left⟩
          exact native_second_low_original_initial_error_cut_forces_both_initial T i U hU a z j true Htarget
            p hp r hr s hs t ht Hsource.1 Hfirst Hsecond H
        have HE2:(t.tree.splitIndex (t.embed s.mark) t.mark=i) ↔
            (r.tree.splitIndex (r.embed p.mark) r.mark=i ∧ t.tree.splitIndex (t.embed s.mark) t.mark=i):=by
          refine ⟨fun H=>?_,And.right⟩
          exact native_second_low_original_initial_error_cut_forces_both_initial T i U hU a z j false Htarget
            p hp r hr s hs t ht Hsource.1 Hfirst Hsecond H
        unfold nativeSecondLowFixedErrorUnobservedWord nativeSecondLowInitialUnobservedWord
          nativeSecondLowUnobservedErrorWord nativeSecondLowUnobservedWord nativeSecondLowErrorWord nativeSecondLowErrorCut
        simp only [ite_true,Bool.false_eq_true,ite_false,Hsource]
        by_cases HB:r.tree.splitIndex (r.embed p.mark) r.mark=i ∧ t.tree.splitIndex (t.embed s.mark) t.mark=i
        · simpa [HB.1,HB.2] using
            (native_second_low_original_word_eq_error_allocations n q U b h K T ho P a z p r s hs t ht).symm
        · have HF:r.tree.splitIndex (r.embed p.mark) r.mark≠i:=fun H=>HB (HE1.mp H)
          have HE:t.tree.splitIndex (t.embed s.mark) t.mark≠i:=fun H=>HB (HE2.mp H)
          simp [HF,HE]
      · simp [nativeSecondLowFixedErrorUnobservedWord,nativeSecondLowInitialUnobservedWord,
          nativeSecondLowUnobservedErrorWord,nativeSecondLowUnobservedWord,Hsource]
    · have Hneq:t.tree.splitIndex (t.embed s.mark) t.mark≠i:=by intro H;rw [H] at Hsecond;exact Hsecond hiU
      have HZ1:=native_second_low_first_error_word_zero_second_high n q U b h K P a z p r s t (not_lt.mp Hsecond)
      have HZ2:=native_second_low_second_error_word_zero_second_high n q U b h K P a z p r s t (not_lt.mp Hsecond)
      simp [nativeSecondLowFixedErrorUnobservedWord,nativeSecondLowInitialUnobservedWord,
        nativeSecondLowUnobservedErrorWord,nativeSecondLowErrorWord,nativeSecondLowErrorCut,HZ1,Hneq]
  · have Hneq:r.tree.splitIndex (r.embed p.mark) r.mark≠i:=by intro H;rw [H] at Hfirst;exact Hfirst hiU
    have HZ1:=native_second_low_first_error_word_zero_first_high n q U b h K P a z p r s hs t ht (not_lt.mp Hfirst)
    have HZ2:=native_second_low_second_error_word_zero_first_high n q U b h K P a z p r s hs t ht (not_lt.mp Hfirst)
    simp [nativeSecondLowFixedErrorUnobservedWord,nativeSecondLowInitialUnobservedWord,
      nativeSecondLowUnobservedErrorWord,nativeSecondLowErrorWord,nativeSecondLowErrorCut,HZ2,Hneq]

theorem native_second_low_fixed_initial_error_classes_eq_both_initial_class
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (i U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU : U ≤ as.length) (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot)
    (Htarget : i<T.splitIndex a z) (haz : T.splitIndex a z<U) (j : Fin 8) :
    nativeSecondLowFixedErrorUnobservedClassLedger n q i U b h K T hU P a z j true+
      nativeSecondLowFixedErrorUnobservedClassLedger n q i U b h K T hU P a z j false=
      nativeSecondLowInitialUnobservedClassLedger n q i U b h K T hU P a z j := by
  unfold nativeSecondLowFixedErrorUnobservedClassLedger nativeSecondLowInitialUnobservedClassLedger
  rw [←native_second_low_double_average_add]
  apply native_second_low_double_average_congr
  intro p hp r hr
  rw [←native_second_low_double_average_add]
  apply native_second_low_double_average_congr
  intro s hs t ht
  exact native_second_low_fixed_initial_error_words_eq_both_initial_word n q i U b h K T ho hU P a z Htarget haz j
    p hp r hr s hs t ht

theorem native_second_low_fresh_star_fixed_initial_error_classes_eq_both_initial_class
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (i star U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU : U ≤ as.length) (s : T.Slot) (hi : i<star) (hstar : star<U)
    (P : (nativeFreshAtSlot T 0 s star).tree.cavityLeft.Assignment → ℝ) (j : Fin 8) :
    let g:=nativeFreshAtSlot T 0 s star
    nativeSecondLowFixedErrorUnobservedClassLedger n q i U b h K g.tree hU P (g.embed s) g.mark j true+
      nativeSecondLowFixedErrorUnobservedClassLedger n q i U b h K g.tree hU P (g.embed s) g.mark j false=
      nativeSecondLowInitialUnobservedClassLedger n q i U b h K g.tree hU P (g.embed s) g.mark j := by
  let g:=nativeFreshAtSlot T 0 s star
  have Hsplit:g.tree.splitIndex (g.embed s) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left (by omega)]
  exact native_second_low_fixed_initial_error_classes_eq_both_initial_class n q i U b h K g.tree ho hU P
    (g.embed s) g.mark (Hsplit ▸ hi) (Hsplit ▸ hstar) j

theorem native_second_low_original_unobserved_class_eq_initial_star_moving
    (n : ℕ) (q : ℕ → RestCoordinate n → ℝ) (i star U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU : U ≤ as.length) (P : T.cavityLeft.Assignment → ℝ) (a z : T.Slot)
    (Htarget : i<T.splitIndex a z) (haz : T.splitIndex a z<U) (histar : i≠star) (j : Fin 8) :
    nativeSecondLowClassLedger n q U b h K T hU P a z j false=
      nativeSecondLowInitialUnobservedClassLedger n q i U b h K T hU P a z j+
      nativeSecondLowFixedErrorUnobservedClassLedger n q star U b h K T hU P a z j true+
      nativeSecondLowFixedErrorUnobservedClassLedger n q star U b h K T hU P a z j false+
      nativeSecondLowMovingErrorUnobservedClassLedger n q i star U b h K T hU P a z j true+
      nativeSecondLowMovingErrorUnobservedClassLedger n q i star U b h K T hU P a z j false := by
  rw [native_second_low_original_unobserved_class_eq_error_classes n q U b h K T ho hU P a z j,
    native_second_low_unobserved_error_class_eq_split_allocations n q i star U b h K T hU P a z j true histar,
    native_second_low_unobserved_error_class_eq_split_allocations n q i star U b h K T hU P a z j false histar,
    ←native_second_low_fixed_initial_error_classes_eq_both_initial_class n q i U b h K T ho hU P a z Htarget haz j]
  ring

end OAI.SKFluctuations.Cavity
