module

public import ComparisonSignedCavityHighRowsCommutationReadout

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}

theorem native_sum_filter_of_zero {A : Type} (l : List A) (p : A→Bool) (F : A→ℝ)
    (hF : ∀a∈l,p a=false → F a=0) :
    ((l.filter p).map F).sum=(l.map F).sum := by
  induction l with
  | nil=>rfl
  | cons a l ih=>
    have H:=ih (by intro b hb;exact hF b (List.mem_cons_of_mem a hb))
    cases hp : p a with
    | false=>simp only [List.filter_cons,hp,Bool.false_eq_true,not_false_eq_true,ite_eq_right,
        List.map_cons,List.sum_cons,hF a (List.mem_cons_self) hp,zero_add,H]
    | true=>simp only [List.filter_cons,hp,ite_true,List.map_cons,List.sum_cons,H]

theorem native_high_row_sum_eq_full_of_support {as : List PositiveMass}
    (T : ClockTree S as) (a : T.Slot) (star : ℕ) (aRow : ℝ)
    (F : MarkedPlacement T→ℝ)
    (hF : ∀p∈T.markedAttach aRow,¬star < p.tree.splitIndex (p.embed a) p.mark → F p=0) :
    ((nativeHighMarkedRows T a star aRow).map F).sum=((T.markedAttach aRow).map F).sum := by
  classical
  rw [nativeHighMarkedRows_eq_filter]
  apply native_sum_filter_of_zero
  intro p hp hf
  exact hF p hp (by simpa only [decide_eq_false_iff_not] using hf)

theorem native_two_high_nested_full_of_support {as : List PositiveMass}
    (T : ClockTree S as) (a b : T.Slot) (star : ℕ) (aRow : ℝ)
    (F : (p : MarkedPlacement T)→MarkedPlacement p.tree→ℝ)
    (hF₁ : ∀p∈T.markedAttach aRow,∀r∈p.tree.markedAttach aRow,
      ¬star < p.tree.splitIndex (p.embed a) p.mark → F p r=0)
    (hF₂ : ∀p∈T.markedAttach aRow,∀r∈p.tree.markedAttach aRow,
      ¬star < r.tree.splitIndex (r.embed (p.embed b)) r.mark → F p r=0) :
    ((nativeHighMarkedRows T a star aRow).map (fun p=>p.coeff*
      ((nativeHighMarkedRows p.tree (p.embed b) star aRow).map (fun r=>r.coeff*F p r)).sum)).sum=
      ((T.markedAttach aRow).map (fun p=>p.coeff*
        ((p.tree.markedAttach aRow).map (fun r=>r.coeff*F p r)).sum)).sum := by
  have HI (p : MarkedPlacement T) (hp : p∈T.markedAttach aRow) :
      ((nativeHighMarkedRows p.tree (p.embed b) star aRow).map (fun r=>r.coeff*F p r)).sum=
        ((p.tree.markedAttach aRow).map (fun r=>r.coeff*F p r)).sum := by
    apply native_high_row_sum_eq_full_of_support
    intro r hr hh
    rw [hF₂ p hp r hr hh,mul_zero]
  have HE : ((nativeHighMarkedRows T a star aRow).map (fun p=>p.coeff*
      ((nativeHighMarkedRows p.tree (p.embed b) star aRow).map (fun r=>r.coeff*F p r)).sum)).sum=
    ((nativeHighMarkedRows T a star aRow).map (fun p=>p.coeff*
      ((p.tree.markedAttach aRow).map (fun r=>r.coeff*F p r)).sum)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    rw [HI p ((mem_nativeHighMarkedRows T a star aRow p).mp hp).1]
  rw [HE]
  apply native_high_row_sum_eq_full_of_support
  intro p hp hh
  have HR : ((p.tree.markedAttach aRow).map (fun r=>r.coeff*F p r)).sum=0 := by
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hz
    rw [hF₁ p hp r hr hh,mul_zero]
  rw [HR,mul_zero]

end OAI.SKFluctuations.Hierarchy.ClockTree
