module

public import CavityMomentAllocation

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal

namespace OAI.SKFluctuations.Cavity

def joins {B : Type*} (a b c d : B) : Prop :=
  (c = a ∧ d = b) ∨ (c = b ∧ d = a)

theorem one_low_edge_selection {B : Type*} [DecidableEq B] (a b c d : B)
    (hab : a ≠ b) (hcd : c ≠ d)
    (heven : ∀ z, Even ([a,b,c,d].count z)) : joins a b c d := by
  have hba := Ne.symm hab
  have hdc := Ne.symm hcd
  have ha := heven a
  have hb := heven b
  clear heven
  simp only [List.count_cons, List.count_nil, Nat.even_iff] at ha hb
  by_cases hca : c = a <;> by_cases hda : d = a <;>
    by_cases hcb : c = b <;> by_cases hdb : d = b
  all_goals subst_vars <;> simp_all [joins]

private theorem two_edges_at_first_target {B : Type*} [DecidableEq B]
    (a b d e f : B) (hab : a ≠ b) (hda : d ≠ a) (hea : e ≠ a)
    (hfa : f ≠ a) (hef : e ≠ f)
    (heven : ∀ z, Even ([a,b,a,d,e,f].count z)) :
    ∃ z, z ≠ a ∧ z ≠ b ∧ joins a z a d ∧ joins z b e f := by
  have hba := Ne.symm hab
  have had := Ne.symm hda
  have hae := Ne.symm hea
  have haf := Ne.symm hfa
  have hfe := Ne.symm hef
  have hb := heven b
  have hd := heven d
  have he := heven e
  have hf := heven f
  clear heven
  simp only [List.count_cons, List.count_nil, Nat.even_iff] at hb hd he hf
  by_cases hdb : d = b <;> by_cases heb : e = b <;> by_cases hfb : f = b <;>
    by_cases hed : e = d <;> by_cases hfd : f = d
  all_goals subst_vars
  all_goals simp_all [joins]
  all_goals aesop

theorem two_low_edges_selection {B : Type*} [DecidableEq B] (a b c d e f : B)
    (hab : a ≠ b) (hcd : c ≠ d) (hef : e ≠ f)
    (heven : ∀ z, Even ([a,b,c,d,e,f].count z)) :
    ∃ z, z ≠ a ∧ z ≠ b ∧
      ((joins a z c d ∧ joins z b e f) ∨ (joins a z e f ∧ joins z b c d)) := by
  have hba := Ne.symm hab
  have hdc := Ne.symm hcd
  have hfe := Ne.symm hef
  have ha := heven a
  simp only [List.count_cons, List.count_nil, Nat.even_iff] at ha
  have casesAtA :
      (c = a ∧ d ≠ a ∧ e ≠ a ∧ f ≠ a) ∨
      (d = a ∧ c ≠ a ∧ e ≠ a ∧ f ≠ a) ∨
      (e = a ∧ c ≠ a ∧ d ≠ a ∧ f ≠ a) ∨
      (f = a ∧ c ≠ a ∧ d ≠ a ∧ e ≠ a) := by
    by_cases hca : c = a <;> by_cases hda : d = a <;>
      by_cases hea : e = a <;> by_cases hfa : f = a
    all_goals simp_all
  rcases casesAtA with ⟨hca,hda,hea,hfa⟩ | ⟨hda,hca,hea,hfa⟩ |
    ⟨hea,hca,hda,hfa⟩ | ⟨hfa,hca,hda,hea⟩
  · subst c
    obtain ⟨z,hza,hzb,haz,hzb'⟩ := two_edges_at_first_target a b d e f hab hda hea hfa hef heven
    exact ⟨z,hza,hzb,Or.inl ⟨haz,hzb'⟩⟩
  · subst d
    have heven' : ∀ z, Even ([a,b,a,c,e,f].count z) := by
      intro z
      have h := heven z
      simp only [List.count_cons, List.count_nil, Nat.even_iff] at h ⊢
      omega
    obtain ⟨z,hza,hzb,haz,hzb'⟩ := two_edges_at_first_target a b c e f hab hca hea hfa hef heven'
    refine ⟨z,hza,hzb,Or.inl ⟨?_,hzb'⟩⟩
    simpa only [joins, and_comm, or_comm] using haz
  · subst e
    have heven' : ∀ z, Even ([a,b,a,f,c,d].count z) := by
      intro z
      have h := heven z
      simp only [List.count_cons, List.count_nil, Nat.even_iff] at h ⊢
      omega
    obtain ⟨z,hza,hzb,haz,hzb'⟩ := two_edges_at_first_target a b f c d hab hfa hca hda hcd heven'
    exact ⟨z,hza,hzb,Or.inr ⟨haz,hzb'⟩⟩
  · subst f
    have heven' : ∀ z, Even ([a,b,a,e,c,d].count z) := by
      intro z
      have h := heven z
      simp only [List.count_cons, List.count_nil, Nat.even_iff] at h ⊢
      omega
    obtain ⟨z,hza,hzb,haz,hzb'⟩ := two_edges_at_first_target a b e c d hab hea hca hda hcd heven'
    refine ⟨z,hza,hzb,Or.inr ⟨?_,hzb'⟩⟩
    simpa only [joins, and_comm, or_comm] using haz

end OAI.SKFluctuations.Cavity
