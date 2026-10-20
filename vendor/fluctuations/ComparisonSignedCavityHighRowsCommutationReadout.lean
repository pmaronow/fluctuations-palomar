module

public import ComparisonSignedCavityHighRowsCommutation

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}

theorem native_sum_map_flatMap {A B : Type} (l : List A) (f : A→List B) (F : B→ℝ) :
    ((l.flatMap f).map F).sum=(l.map fun a=>((f a).map F).sum).sum := by
  induction l with
  | nil=>rfl
  | cons a l ih=>simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]

theorem native_two_high_nested_signed_rows_commute {as : List PositiveMass}
    (T : ClockTree S as) (a b : T.Slot) (star : ℕ) (aRow : ℝ)
    (hab : T.splitIndex a b ≤ star)
    (F : (V : ClockTree S as)→(V.Assignment→T.Assignment)→(T.Slot→V.Slot)→V.Slot→V.Slot→ℝ) :
    ((nativeHighMarkedRows T a star aRow).map (fun p=>p.coeff*
      ((nativeHighMarkedRows p.tree (p.embed b) star aRow).map (fun r=>r.coeff*
        F r.tree (fun σ=>p.restrict (r.restrict σ)) (fun c=>r.embed (p.embed c))
          (r.embed p.mark) r.mark)).sum)).sum=
    ((nativeHighMarkedRows T b star aRow).map (fun p=>p.coeff*
      ((nativeHighMarkedRows p.tree (p.embed a) star aRow).map (fun r=>r.coeff*
        F r.tree (fun σ=>p.restrict (r.restrict σ)) (fun c=>r.embed (p.embed c))
          r.mark (r.embed p.mark))).sum)).sum := by
  have H:=native_two_high_signed_placements_commute T a b star aRow hab
    (fun p=>p.coeff*F p.tree p.restrict p.embed p.markA p.markB)
  unfold nativeTwoHighPlacements at H
  rw [native_sum_map_flatMap,native_sum_map_flatMap] at H
  simp only [List.map_map,Function.comp_def,NativeTwoHighPlacement.ofTwo,NativeTwoHighPlacement.swap,
    mul_assoc,List.sum_map_mul_left] at H
  exact H

end OAI.SKFluctuations.Hierarchy.ClockTree
