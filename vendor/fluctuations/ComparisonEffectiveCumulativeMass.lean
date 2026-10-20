module

public import ComparisonFiniteWholeUnitPartition

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open Set Hierarchy
open scoped BigOperators NNReal

theorem finite_unit_coordinate_eq_cumulative {K:ℕ} (x:ℕ→ℝ) (mu:Fin K→ℝ)
    (h0:x 0=0) (hdiff:∀u:Fin K,x (u.val+1)-x u.val=mu u)
    (j:ℕ) (hj:j ≤ K) : x j=∑u:Fin K,if u.val < j then mu u else 0 := by
  have hstep (i:ℕ) (hi:i < K) :
      (∑u:Fin K,if u.val < i+1 then mu u else 0)-
        (∑u:Fin K,if u.val < i then mu u else 0)=mu ⟨i,hi⟩ := by
    rw [←Finset.sum_sub_distrib]
    have ht (u:Fin K) :
        (if u.val < i+1 then mu u else 0)-(if u.val < i then mu u else 0)=
          if u=⟨i,hi⟩ then mu ⟨i,hi⟩ else 0 := by
      by_cases hu:u=⟨i,hi⟩
      · subst u
        simp
      · have hne:u.val≠i:=fun he=> hu (Fin.ext he)
        by_cases hlt:u.val < i  <;>  simp [hu,hlt,show (u.val < i+1)↔u.val < i by omega]
    simp_rw [ht]
    simp
  induction j with
  | zero=> simp [h0]
  | succ j ih=> 
    have hjK:j < K:=by omega
    have hh:=hdiff ⟨j,hjK⟩
    have hi:=ih (by omega)
    have hs:=hstep j hjK
    simp only [Nat.succ_eq_add_one] at *
    linarith

theorem selected_effective_coordinate_eq_mass_before_unit {ι:Type} {K:ℕ}
    (steps:List (GaussianStep ι)) (J:Finset (Fin (steps.length+1)))
    (unit:Fin (steps.length+1)→Fin K) (x:ℕ→ℝ) (h0:x 0=0)
    (hmass:∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u.val)
    (u:Fin K) :
    x u.val=∑i:Fin (steps.length+1),pathMassDifferences steps 0 i*
      (if i∈J ∧ unit i < u then 1 else 0) := by
  have hx:=finite_unit_coordinate_eq_cumulative x (physicalSelectedUnitMass steps J unit) h0
    (fun v=> (hmass v).symm) u.val u.isLt.le
  have hg:=selected_mass_grouping steps J unit (fun v=> if v < u then 1 else 0)
  have he:(∑i:Fin (steps.length+1),pathMassDifferences steps 0 i*
      (if i∈J ∧ unit i < u then 1 else 0))=
      ∑i:Fin (steps.length+1),pathMassDifferences steps 0 i*
        (if i∈J then (if unit i < u then 1 else 0) else 0) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi:i∈J  <;>  simp [hi]
  rw [he,hg]
  exact hx.trans (by apply Finset.sum_congr rfl;intro v _;simp only [mul_ite,mul_one,mul_zero,Fin.lt_iff_val_lt_val])

theorem selected_effective_contact_coordinate_eq_mass_before_row {ι:Type} {K:ℕ}
    (steps:List (GaussianStep ι)) (J:Finset (Fin (steps.length+1)))
    (unit:Fin (steps.length+1)→Fin K) (x:ℕ→ℝ) (h0:x 0=0)
    (hmass:∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u.val)
    (horder:MonotoneOn unit (J:Set (Fin (steps.length+1))))
    (i:Fin (steps.length+1)) (hi:i∈J)
    (hsingle:∀j∈J,unit j=unit i→j=i) :
    x (unit i).val=∑j:Fin (steps.length+1),pathMassDifferences steps 0 j*
      (if j∈J ∧ j < i then 1 else 0) := by
  rw [selected_effective_coordinate_eq_mass_before_unit steps J unit x h0 hmass]
  apply Finset.sum_congr rfl
  intro j _
  have he:(j∈J ∧ unit j < unit i)↔(j∈J ∧ j < i) := by
    constructor
    · intro hj
      refine ⟨hj.1,?_⟩
      by_contra hji
      exact (not_le_of_gt hj.2) (horder hi hj.1 (le_of_not_gt hji))
    · intro hj
      have hh:=horder hj.1 hi hj.2.le
      refine ⟨hj.1,lt_of_le_of_ne hh ?_⟩
      intro he
      exact (ne_of_lt hj.2) (hsingle j hj.1 he)
  simp only [he]

end OAI.SKFluctuations.WholeUnitSideKernel
