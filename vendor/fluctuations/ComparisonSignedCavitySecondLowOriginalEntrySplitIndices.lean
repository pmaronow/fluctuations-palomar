module

public import ComparisonSignedCavitySecondLowPathEntrySplitGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 30000000

def nativeSecondLowEntryDepartureCut {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (a : T.Slot) (j : Fin 8)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) : ℕ :=
  if nativeSecondLowFirstMiddleIsFirst j then p.tree.splitIndex (p.embed a) p.mark
    else r.tree.splitIndex (r.embed (p.embed a)) r.mark

theorem native_second_low_final_entry_split_eq_original
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (a : T.Slot) (j : Fin 8) (p : MarkedPlacement T)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0) :
    t.tree.splitIndex (t.embed (s.embed (r.embed (p.embed a))))
      (nativeSecondLowFirstEntrySlot j (t.embed (s.embed (r.embed p.mark))) (t.embed (s.embed r.mark)))=
      nativeSecondLowEntryDepartureCut a j p r := by
  unfold nativeSecondLowFirstEntrySlot nativeSecondLowEntryDepartureCut
  cases HF : nativeSecondLowFirstMiddleIsFirst j
  · simp only [Bool.false_eq_true,ite_false]
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
      (r.tree.markedAttach_embed_preserves 0 s hs).2]
  · simp only [ite_true]
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
      (r.tree.markedAttach_embed_preserves 0 s hs).2,
      (p.tree.markedAttach_embed_preserves 0 r hr).2]

theorem native_second_low_original_word_LOW_indices_eq_entry_departures
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (U : ℕ) (hU : U ≤ as.length) (a z : T.Slot) (j : Fin 8)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (Hpath : nativeSecondLowWordPath U hU a z p r s t j)
    (Hfirst : r.tree.splitIndex (r.embed p.mark) r.mark<U)
    (Hsecond : t.tree.splitIndex (t.embed s.mark) t.mark<U) :
    r.tree.splitIndex (r.embed p.mark) r.mark=
      (if j.val<4 then nativeSecondLowEntryDepartureCut a j p r else nativeSecondLowEntryDepartureCut z j p r) ∧
    t.tree.splitIndex (t.embed s.mark) t.mark=
      (if j.val<4 then nativeSecondLowEntryDepartureCut z j p r else nativeSecondLowEntryDepartureCut a j p r) := by
  let af:=t.embed (s.embed (r.embed (p.embed a)))
  let zf:=t.embed (s.embed (r.embed (p.embed z)))
  let f:=t.embed (s.embed (r.embed p.mark))
  let c:=t.embed (s.embed r.mark)
  let e:=t.embed s.mark
  let d:=t.mark
  have Hfc:t.tree.splitIndex f c=r.tree.splitIndex (r.embed p.mark) r.mark:=by
    dsimp [f,c]
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,
      (r.tree.markedAttach_embed_preserves 0 s hs).2]
  have H:=native_second_low_path_low_splits_eq_entry_departures t.tree U hU af zf f c e d j
    Hpath (Hfc ▸ Hfirst) Hsecond
  rw [Hfc] at H
  have HA:=native_second_low_final_entry_split_eq_original a j p r hr s hs t ht
  have HZ:=native_second_low_final_entry_split_eq_original z j p r hr s hs t ht
  by_cases Hj : j.val<4
  · simp only [Hj,ite_true] at H ⊢
    exact ⟨H.1.trans HA,H.2.trans HZ⟩
  · simp only [Hj,ite_false] at H ⊢
    exact ⟨H.1.trans HZ,H.2.trans HA⟩

end OAI.SKFluctuations.Cavity
