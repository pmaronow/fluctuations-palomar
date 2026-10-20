module

public import ComparisonSignedCavitySecondLowMovingErrorEntrySource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}
set_option maxHeartbeats 30000000

theorem native_second_low_high_target_pair_equal_low_departures
    (T : ClockTree S as) (a z w : T.Slot) (i : ℕ) (Htarget : i<T.splitIndex a z)
    (H : T.splitIndex a w=i ∨ T.splitIndex z w=i) :
    T.splitIndex a w=i ∧ T.splitIndex z w=i := by
  rcases H with HA | HZ
  · refine ⟨HA,?_⟩
    exact (T.splitIndex_low_eq_of_high z a w (U:=i+1)
      (by rw [T.splitIndex_symm];omega) (by rw [HA];omega)).trans HA
  · refine ⟨?_,HZ⟩
    exact (T.splitIndex_low_eq_of_high a z w (U:=i+1)
      (by omega) (by rw [HZ];omega)).trans HZ

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 30000000

theorem native_second_low_original_initial_error_cut_forces_both_initial
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (i U : ℕ) (hU : U ≤ as.length) (a z : T.Slot) (j : Fin 8) (firstError : Bool)
    (Htarget : i<T.splitIndex a z)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (Hpath : nativeSecondLowWordPath U hU a z p r s t j)
    (Hfirst : r.tree.splitIndex (r.embed p.mark) r.mark<U)
    (Hsecond : t.tree.splitIndex (t.embed s.mark) t.mark<U)
    (Hindex : nativeSecondLowErrorCut firstError p r s t=i) :
    r.tree.splitIndex (r.embed p.mark) r.mark=i ∧ t.tree.splitIndex (t.embed s.mark) t.mark=i := by
  have HG:=native_second_low_original_word_LOW_indices_eq_entry_departures T U hU a z j
    p r hr s hs t ht Hpath Hfirst Hsecond
  have Hsame:(nativeSecondLowEntryDepartureCut a j p r=i ∨ nativeSecondLowEntryDepartureCut z j p r=i) →
      nativeSecondLowEntryDepartureCut a j p r=i ∧ nativeSecondLowEntryDepartureCut z j p r=i:=by
    intro HH
    unfold nativeSecondLowEntryDepartureCut at HH ⊢
    cases HM:nativeSecondLowFirstMiddleIsFirst j
    · simp only [HM,Bool.false_eq_true,ite_false] at HH ⊢
      have Htarget2:i<r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed z)):=by
        rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2]
        exact Htarget
      exact native_second_low_high_target_pair_equal_low_departures r.tree _ _ _ i Htarget2 HH
    · simp only [HM,ite_true] at HH ⊢
      have Htarget2:i<p.tree.splitIndex (p.embed a) (p.embed z):=by
        rw [(T.markedAttach_embed_preserves 0 p hp).2]
        exact Htarget
      exact native_second_low_high_target_pair_equal_low_departures p.tree _ _ _ i Htarget2 HH
  have HE:nativeSecondLowEntryDepartureCut a j p r=i ∨ nativeSecondLowEntryDepartureCut z j p r=i:=by
    by_cases Hj:j.val<4
    · simp only [Hj,ite_true] at HG
      cases firstError
      · exact Or.inr (HG.2.symm.trans Hindex)
      · exact Or.inl (HG.1.symm.trans Hindex)
    · simp only [Hj,ite_false] at HG
      cases firstError
      · exact Or.inl (HG.2.symm.trans Hindex)
      · exact Or.inr (HG.1.symm.trans Hindex)
  obtain ⟨HA,HZ⟩:=Hsame HE
  simpa only [HA,HZ,ite_self] using HG

end OAI.SKFluctuations.Cavity
