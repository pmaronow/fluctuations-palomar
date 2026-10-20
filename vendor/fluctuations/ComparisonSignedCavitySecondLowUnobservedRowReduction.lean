module

public import ComparisonSignedCavitySecondLowUnobservedSourceEntry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped BigOperators
set_option maxHeartbeats 26000000
attribute [local instance] Classical.propDecidable

theorem native_second_low_sum_filter_of_zero {α : Type*} (L : List α) (P : α→Prop) (F : α→ℝ)
    (h : ∀x∈L,¬P x→F x=0) :
    (L.map F).sum=((L.filter (fun x=>decide (P x))).map F).sum := by
  induction L with
  | nil=>rfl
  | cons x L ih=>
    have H:=ih (fun y hy=>h y (List.mem_cons_of_mem x hy))
    by_cases HP : P x
    · simp only [List.map_cons,List.sum_cons,List.filter_cons,HP,decide_true,ite_true,H]
    · simp only [List.map_cons,List.sum_cons,List.filter_cons,HP,decide_false,Bool.false_eq_true,ite_false,
        h x List.mem_cons_self HP,zero_add,H]

def nativeSecondLowUnobservedWord (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (j : Fin 8)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree)
    (s : MarkedPlacement r.tree) (t : MarkedPlacement s.tree) : ℝ :=
  if nativeSecondLowWordPath U hU a z p r s t j ∧ ¬nativeSecondLowWordObserved U p r s t j
    then nativeSecondLowWordValue n q U b h K P a z p r s t else 0

theorem native_second_low_unobserved_word_zero_outside_entry (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (hU : U≤as.length)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (j : Fin 8)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0)
    (Hentry : ¬(if nativeSecondLowFirstMiddleIsFirst j then p∈nativeSecondLowUnobservedEntryRows T U 0
      else r∈nativeSecondLowUnobservedEntryRows p.tree U 0)) :
    nativeSecondLowUnobservedWord n q U b h K hU P a z j p r s t=0 := by
  unfold nativeSecondLowUnobservedWord
  split_ifs with H
  · rcases H with ⟨Hpath,Hunobs⟩
    by_contra HV
    have Hlow : r.tree.splitIndex (r.embed p.mark) r.mark<U := by
      by_contra HH
      have HZ:=native_second_low_joint_rest_test_zero_of_first_high n U b h K P p r s t (not_lt.mp HH)
      apply HV
      unfold nativeSecondLowWordValue
      rw [HZ]
      simp [disorderExpect]
    exact Hentry (native_second_low_unobserved_source_entry T U hU a z p hp r hr s hs t ht j Hpath Hunobs Hlow)
  · rfl

def nativeSecondLowUnobservedEntryLedger (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (hU : U≤as.length) (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (j : Fin 8) : ℝ :=
  let first:=nativeSecondLowFirstMiddleIsFirst j
  let ps:=if first then nativeSecondLowUnobservedEntryRows T U 0 else T.markedAttach 0
  (ps.map fun p=>p.coeff*
    ((if first then p.tree.markedAttach 0 else nativeSecondLowUnobservedEntryRows p.tree U 0).map fun r=>
      r.coeff*nativeSecondLowDoubleAverage r.tree (fun s t=>
        nativeSecondLowUnobservedWord n q U b h K hU P a z j p r s t)).sum).sum/2

theorem native_second_low_unobserved_class_eq_entry_ledger (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (hU : U≤as.length)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (j : Fin 8) :
    nativeSecondLowClassLedger n q U b h K T hU P a z j false=
      nativeSecondLowUnobservedEntryLedger n q U b h K T hU P a z j := by
  let F:=fun (p : MarkedPlacement T) (r : MarkedPlacement p.tree)=>
    nativeSecondLowDoubleAverage r.tree (fun s t=>nativeSecondLowUnobservedWord n q U b h K hU P a z j p r s t)
  have Hzero (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
      (Hentry : ¬(if nativeSecondLowFirstMiddleIsFirst j then p∈nativeSecondLowUnobservedEntryRows T U 0
        else r∈nativeSecondLowUnobservedEntryRows p.tree U 0)) : F p r=0 := by
    dsimp only [F,nativeSecondLowDoubleAverage]
    have Ht (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0) :
        ((s.tree.markedAttach 0).map (fun t=>t.coeff*
          nativeSecondLowUnobservedWord n q U b h K hU P a z j p r s t)).sum=0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hx
      rw [native_second_low_unobserved_word_zero_outside_entry n q U b h K T hU P a z j p hp r hr s hs t ht Hentry,
        mul_zero]
    have Hz : ((r.tree.markedAttach 0).map (fun s=>s.coeff*
        ((s.tree.markedAttach 0).map (fun t=>t.coeff*
          nativeSecondLowUnobservedWord n q U b h K hU P a z j p r s t)).sum)).sum=0 := by
      apply List.sum_eq_zero
      intro x hx
      obtain ⟨s,hs,rfl⟩:=List.mem_map.mp hx
      rw [Ht s hs,mul_zero]
    rw [Hz,zero_div]
  have Hclass : nativeSecondLowClassLedger n q U b h K T hU P a z j false=
      nativeSecondLowDoubleAverage T F := by
    simp only [nativeSecondLowClassLedger,F,nativeSecondLowUnobservedWord,Bool.false_eq_true,iff_false]
  rw [Hclass]
  unfold nativeSecondLowDoubleAverage nativeSecondLowUnobservedEntryLedger
  cases HF : nativeSecondLowFirstMiddleIsFirst j
  · simp only [Bool.false_eq_true,↓reduceIte]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    congr 1
    have Hsum:=native_second_low_sum_filter_of_zero (p.tree.markedAttach 0)
      (fun r=>∀v:p.tree.Slot,r.tree.splitIndex (r.embed v) r.mark<U) (fun r=>r.coeff*F p r) (by
        intro r hr Hno
        have Hnot : r∉nativeSecondLowUnobservedEntryRows p.tree U 0 := by
          rw [mem_nativeSecondLowUnobservedEntryRows]
          simpa only [not_exists,not_le] using fun H : r∈p.tree.markedAttach 0 ∧
            (∀v:p.tree.Slot,r.tree.splitIndex (r.embed v) r.mark<U)=>Hno H.2
        rw [Hzero p hp r hr (by simpa only [HF,Bool.false_eq_true,↓reduceIte] using Hnot),mul_zero])
    rw [nativeSecondLowUnobservedEntryRows_eq_filter]
    exact Hsum
  · simp only [↓reduceIte]
    have Hsum:=native_second_low_sum_filter_of_zero (T.markedAttach 0)
      (fun p=>∀v:T.Slot,p.tree.splitIndex (p.embed v) p.mark<U)
      (fun p=>p.coeff*((p.tree.markedAttach 0).map (fun r=>r.coeff*F p r)).sum) (by
        intro p hp Hno
        have Hnot : p∉nativeSecondLowUnobservedEntryRows T U 0 := by
          rw [mem_nativeSecondLowUnobservedEntryRows]
          simpa only [not_exists,not_le] using fun H : p∈T.markedAttach 0 ∧
            (∀v:T.Slot,p.tree.splitIndex (p.embed v) p.mark<U)=>Hno H.2
        have Hz : ((p.tree.markedAttach 0).map (fun r=>r.coeff*F p r)).sum=0 := by
          apply List.sum_eq_zero
          intro x hx
          obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hx
          rw [Hzero p hp r hr (by simpa only [HF,↓reduceIte] using Hnot),mul_zero]
        rw [Hz,mul_zero])
    rw [nativeSecondLowUnobservedEntryRows_eq_filter]
    exact congrArg (fun x : ℝ=>x/2) Hsum

end OAI.SKFluctuations.Cavity
