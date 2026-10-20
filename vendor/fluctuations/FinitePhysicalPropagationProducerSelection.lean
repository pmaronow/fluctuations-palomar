module

public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set

def physicalPropagationBadMasses (r : ℝ → ℝ) (A c C : ℝ) : Set ℝ :=
  {u | u ∈ Icc A 1 ∧ ¬ (c*u ≤ r u ∧ r u ≤ C*u)}

theorem physical_propagation_select_last_bad_mass
    {r : ℝ → ℝ} {A c C : ℝ} (hA : 0 < A)
    (hbad : (physicalPropagationBadMasses r A c C).Nonempty) :
    ∃ x ∈ physicalPropagationBadMasses r A c C,
      0 < x ∧ ∀ u ∈ Icc A 1, 2*x ≤ u → c*u ≤ r u ∧ r u ≤ C*u := by
  let S := physicalPropagationBadMasses r A c C
  have hbounded : BddAbove S := ⟨1,by
    intro u hu
    exact hu.1.2⟩
  have hSn : S.Nonempty := hbad
  obtain ⟨u,hu⟩ := hbad
  have hspos : 0 < sSup S := (hA.trans_le hu.1.1).trans_le (le_csSup hbounded hu)
  obtain ⟨x,hx,hxlarge⟩ := exists_lt_of_lt_csSup hSn
    (show sSup S/2 < sSup S by linarith)
  refine ⟨x,hx,hA.trans_le hx.1.1,?_⟩
  intro v hv hlarge
  by_contra hfail
  have hvS : v ∈ S := ⟨hv,hfail⟩
  have hvbound := le_csSup hbounded hvS
  linarith

theorem physical_propagation_upward_separation_interval
    {r z : ℝ → ℝ} (hr : Monotone r) (hz : Monotone z)
    {a b lo hi : ℝ} (hab : a ≤ b)
    (hrb : r b ≤ lo) (hza : hi ≤ z a) :
    ∀ u ∈ Icc a b, r u ≤ lo ∧ hi ≤ z u := by
  intro u hu
  exact ⟨(hr hu.2).trans hrb,hza.trans (hz hu.1)⟩

theorem physical_propagation_downward_separation_interval
    {r z : ℝ → ℝ} (hr : Monotone r) (hz : Monotone z)
    {a b lo hi : ℝ} (hab : a ≤ b)
    (hra : hi ≤ r a) (hzb : z b ≤ lo) :
    ∀ u ∈ Icc a b, hi ≤ r u ∧ z u ≤ lo := by
  intro u hu
  exact ⟨hra.trans (hr hu.1),(hz hu.2).trans hzb⟩

theorem physical_propagation_finite_descendant_selection
    {Family : Type*} (Bad : Family → Prop) (Child : Family → Family → Prop)
    (next : ∀ p, Bad p → ∃ q, Bad q ∧ Child p q)
    (root : Family) (hroot : Bad root) (depth : ℕ) :
    ∃ chain : Fin (depth+1) → Family,
      chain 0 = root ∧ (∀ j, Bad (chain j)) ∧
      ∀ j : Fin depth, Child (chain j.castSucc) (chain j.succ) := by
  induction depth with
  | zero =>
      refine ⟨fun _ => root,rfl,fun _ => hroot,?_⟩
      intro j
      exact Fin.elim0 j
  | succ depth ih =>
      obtain ⟨chain,hzero,hbad,hchild⟩ := ih
      obtain ⟨q,hq,hnext⟩ := next (chain (Fin.last depth)) (hbad _)
      refine ⟨Fin.snoc chain q,?_,?_,?_⟩
      · simpa using hzero
      · intro j
        refine Fin.lastCases ?_ ?_ j
        · simpa only [Fin.snoc_last] using hq
        · intro i
          simpa only [Fin.snoc_castSucc] using hbad i
      · intro j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa using hnext
        · simpa only [← Fin.castSucc_succ,Fin.snoc_castSucc] using hchild i

theorem physical_propagation_no_bad_root_of_local_child
    {Family : Type*} (Bad : Family → Prop) (Child : Family → Family → Prop)
    (depth : ℕ)
    (next : ∀ p, Bad p → ∃ q, Bad q ∧ Child p q)
    (obstruction : ∀ chain : Fin (depth+1) → Family,
      (∀ j, Bad (chain j)) →
      (∀ j : Fin depth, Child (chain j.castSucc) (chain j.succ)) → False) :
    ∀ p, ¬ Bad p := by
  intro p hp
  obtain ⟨chain,_,hbad,hchild⟩ :=
    physical_propagation_finite_descendant_selection Bad Child next p hp depth
  exact obstruction chain hbad hchild

end OAI.SKFluctuations.LaplaceWindowFormalization
