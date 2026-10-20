module

public import ComparisonSignedCavityOutsideMarkedRows

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}
set_option maxHeartbeats 24000000
attribute [local instance] Classical.propDecidable

def nativeSecondLowEntryWitness : {as : List PositiveMass}→(T : ClockTree S as)→T.Slot
  | _,.leaf=>()
  | _,.step _ T=>nativeSecondLowEntryWitness T
  | _,.fork T _=>Sum.inl (nativeSecondLowEntryWitness T)

def nativeSecondLowUnobservedEntryRows : {as : List PositiveMass}→(T : ClockTree S as)→ℕ→ℝ→List (MarkedPlacement T)
  | _,_,0,_=>[]
  | _,.leaf,_+1,a=>ClockTree.leaf.markedAttach a
  | _,.step b T,U+1,a=>MarkedPlacement.fresh (T.step b) (a-b.val)::
      (nativeSecondLowUnobservedEntryRows T U b.val).map (fun p=>p.step b)
  | _,.fork T V,U+1,a=>MarkedPlacement.fresh (T.fork V) (-a)::
      ((nativeSecondLowUnobservedEntryRows T (U+1) a).map (fun p=>p.left V)++
       (nativeSecondLowUnobservedEntryRows V (U+1) a).map (fun p=>p.right T))

theorem nativeSecondLowEntry_left_test {as : List PositiveMass} {T : ClockTree S as}
    (V : ClockTree S as) (p : MarkedPlacement T) (U : ℕ) :
    (∀v:(T.fork V).Slot,(p.left V).tree.splitIndex ((p.left V).embed v) (p.left V).mark<U+1) ↔
      ∀v:T.Slot,p.tree.splitIndex (p.embed v) p.mark<U+1 := by
  change (∀v:T.Slot⊕V.Slot,(p.tree.fork V).splitIndex (Sum.map p.embed id v) (Sum.inl p.mark)<U+1) ↔ _
  simp only [Sum.forall,Sum.map_inl,Sum.map_inr,splitIndex,Sum.elim_inl,Sum.elim_inr,
    Nat.zero_lt_succ]
  exact ⟨fun H=>H.1,fun H=>⟨H,fun _=>True.intro⟩⟩

theorem nativeSecondLowEntry_right_test {as : List PositiveMass} (T : ClockTree S as)
    {V : ClockTree S as} (p : MarkedPlacement V) (U : ℕ) :
    (∀v:(T.fork V).Slot,(p.right T).tree.splitIndex ((p.right T).embed v) (p.right T).mark<U+1) ↔
      ∀v:V.Slot,p.tree.splitIndex (p.embed v) p.mark<U+1 := by
  change (∀v:T.Slot⊕V.Slot,(T.fork p.tree).splitIndex (Sum.map id p.embed v) (Sum.inr p.mark)<U+1) ↔ _
  simp only [Sum.forall,Sum.map_inl,Sum.map_inr,splitIndex,Sum.elim_inl,Sum.elim_inr,
    Nat.zero_lt_succ]
  exact ⟨fun H=>H.2,fun H=>⟨fun _=>True.intro,H⟩⟩

theorem nativeSecondLowEntry_fresh_test {as : List PositiveMass} (T : ClockTree S as)
    (U : ℕ) (a : ℝ) :
    ∀v:T.Slot,(MarkedPlacement.fresh T a).tree.splitIndex
      ((MarkedPlacement.fresh T a).embed v) (MarkedPlacement.fresh T a).mark<U+1 := by
  intro v
  change 0<U+1
  omega

theorem nativeSecondLowUnobservedEntryRows_eq_filter {as : List PositiveMass}
    (T : ClockTree S as) (U : ℕ) (a : ℝ) :
    nativeSecondLowUnobservedEntryRows T U a=
      (T.markedAttach a).filter (fun p=>decide (∀v:T.Slot,p.tree.splitIndex (p.embed v) p.mark<U)) := by
  induction T generalizing U a with
  | leaf=>
    cases U <;> simp [nativeSecondLowUnobservedEntryRows,markedAttach,
      MarkedPlacement.coincide,MarkedPlacement.fresh,splitIndex]
  | step b T ih=>
    let : Nonempty T.Slot:=⟨nativeSecondLowEntryWitness T⟩
    cases U with
    | zero=>simp [nativeSecondLowUnobservedEntryRows]
    | succ U=>
      rw [nativeSecondLowUnobservedEntryRows,ih]
      simp [markedAttach,MarkedPlacement.fresh,MarkedPlacement.step,splitIndex,
        List.filter_map,Function.comp_def]
      simp only [Nat.add_comm 1]
      rfl
  | fork T V ihT ihV=>
    let : Nonempty T.Slot:=⟨nativeSecondLowEntryWitness T⟩
    let : Nonempty V.Slot:=⟨nativeSecondLowEntryWitness V⟩
    cases U with
    | zero=>simp [nativeSecondLowUnobservedEntryRows]
    | succ U=>
      rw [nativeSecondLowUnobservedEntryRows,ihT,ihV]
      have HL : (fun p : MarkedPlacement T=>decide
          (∀v:(T.fork V).Slot,(p.left V).tree.splitIndex ((p.left V).embed v) (p.left V).mark<U+1))=
          (fun p : MarkedPlacement T=>decide (∀v:T.Slot,p.tree.splitIndex (p.embed v) p.mark<U+1)) := by
        funext p
        exact congrArg (fun P : Prop=>@decide P (Classical.propDecidable P))
          (propext (nativeSecondLowEntry_left_test V p U))
      have HR : (fun p : MarkedPlacement V=>decide
          (∀v:(T.fork V).Slot,(p.right T).tree.splitIndex ((p.right T).embed v) (p.right T).mark<U+1))=
          (fun p : MarkedPlacement V=>decide (∀v:V.Slot,p.tree.splitIndex (p.embed v) p.mark<U+1)) := by
        funext p
        exact congrArg (fun P : Prop=>@decide P (Classical.propDecidable P))
          (propext (nativeSecondLowEntry_right_test T p U))
      simp only [markedAttach,List.filter_cons,List.filter_append,List.filter_map,Function.comp_def,
        nativeSecondLowEntry_fresh_test,forall_const,decide_true,ite_true]
      rw [HL,HR]

theorem mem_nativeSecondLowUnobservedEntryRows {as : List PositiveMass}
    (T : ClockTree S as) (U : ℕ) (a : ℝ) (p : MarkedPlacement T) :
    p∈nativeSecondLowUnobservedEntryRows T U a ↔
      p∈T.markedAttach a ∧ ¬∃v:T.Slot,U≤p.tree.splitIndex (p.embed v) p.mark := by
  rw [nativeSecondLowUnobservedEntryRows_eq_filter]
  simp only [List.mem_filter,decide_eq_true_eq,not_exists,not_le]

theorem native_second_low_unobserved_entry_variation {as : List PositiveMass}
    (T : ClockTree S as) (U : ℕ) (hU : U≤as.length) {a : ℝ}
    (ha : MassOrdered a as) (ha0 : 0≤a) :
    ((nativeSecondLowUnobservedEntryRows T U a).map (fun p=>|p.coeff|)).sum≤
      2*(T.leaves:ℝ)*partitionPoint a as U-a := by
  induction T generalizing U a with
  | leaf=>
    have HU : U=0:=by simpa using hU
    subst U
    simp only [nativeSecondLowUnobservedEntryRows,List.map_nil,List.sum_nil,leaves,
      Nat.cast_one,partitionPoint,partitionValues_zero,id_eq]
    linarith
  | step b T ih=>
    cases U with
    | zero=>
      simp only [nativeSecondLowUnobservedEntryRows,List.map_nil,List.sum_nil,
        partitionPoint,partitionValues_zero,id_eq,leaves]
      have hleaf : (1:ℝ)≤T.leaves := by exact_mod_cast T.leaves_pos
      nlinarith
    | succ U=>
      have H:=ih U (by simp only [List.length_cons] at hU;omega) ha.2.2 b.property.le
      simp only [nativeSecondLowUnobservedEntryRows,List.map_cons,List.map_map,
        List.sum_cons,Function.comp_def,MarkedPlacement.fresh,MarkedPlacement.step,leaves]
      rw [abs_of_nonpos (sub_nonpos.mpr ha.2.1)]
      simp only [partitionPoint,partitionValues] at H ⊢
      linarith
  | fork T V ihT ihV=>
    cases U with
    | zero=>
      simp only [nativeSecondLowUnobservedEntryRows,List.map_nil,List.sum_nil,
        partitionPoint,partitionValues_zero,id_eq]
      have hleaf : (1:ℝ)≤(T.fork V).leaves := by exact_mod_cast (T.fork V).leaves_pos
      nlinarith
    | succ U=>
      have HT:=ihT (U+1) hU ha ha0
      have HV:=ihV (U+1) hU ha ha0
      simp only [nativeSecondLowUnobservedEntryRows,List.map_cons,List.map_append,
        List.map_map,List.sum_cons,List.sum_append,Function.comp_def,
        MarkedPlacement.fresh,MarkedPlacement.left,MarkedPlacement.right,leaves,Nat.cast_add]
      rw [abs_neg,abs_of_nonneg ha0]
      linarith

end OAI.SKFluctuations.Hierarchy.ClockTree
