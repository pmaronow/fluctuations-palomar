module

public import Mathlib.Tactic

public section
noncomputable section
open scoped Classical

namespace SKConstants

@[expose] def cutMass {V : Type*} (pi : V → ℝ) (S : Finset V) : ℝ :=
  ∑ x ∈ S, pi x

@[expose] def cutFlow {V : Type*} (q : V → V → ℝ) (S T : Finset V) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ T, q x y

@[simp] theorem cutMass_empty {V : Type*} (pi : V → ℝ) : cutMass pi ∅ = 0 := by
  simp [cutMass]

@[simp] theorem cutFlow_empty_left {V : Type*} (q : V → V → ℝ) (T : Finset V) :
    cutFlow q ∅ T = 0 := by simp [cutFlow]

@[simp] theorem cutFlow_empty_right {V : Type*} (q : V → V → ℝ) (S : Finset V) :
    cutFlow q S ∅ = 0 := by simp [cutFlow]

theorem cutMass_nonneg {V : Type*} (pi : V → ℝ) (S : Finset V)
    (hpi : ∀ x, 0 ≤ pi x) : 0 ≤ cutMass pi S :=
  Finset.sum_nonneg (fun x _ ↦ hpi x)

theorem cutMass_mono {V : Type*} (pi : V → ℝ) {S T : Finset V}
    (hpi : ∀ x, 0 ≤ pi x) (hST : S ⊆ T) : cutMass pi S ≤ cutMass pi T :=
  Finset.sum_le_sum_of_subset_of_nonneg hST (fun x _ _ ↦ hpi x)

theorem cutMass_union {V : Type*} [DecidableEq V] (pi : V → ℝ)
    {S T : Finset V} (hdis : Disjoint S T) :
    cutMass pi (S ∪ T) = cutMass pi S + cutMass pi T :=
  Finset.sum_union hdis

theorem cutMass_compl {V : Type*} [Fintype V] [DecidableEq V]
    (pi : V → ℝ) (S : Finset V) (hpi_sum : ∑ x, pi x = 1) :
    cutMass pi Sᶜ = 1 - cutMass pi S := by
  have h := Finset.sum_add_sum_compl S pi
  rw [hpi_sum] at h
  unfold cutMass
  linarith

theorem cutMass_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (pi : V → ℝ) (S : Finset V) (hpi : ∀ x, 0 ≤ pi x)
    (hpi_sum : ∑ x, pi x = 1) : cutMass pi S ≤ 1 := by
  have h := cutMass_mono pi hpi S.subset_univ
  simpa only [cutMass, hpi_sum] using h

theorem cutFlow_nonneg {V : Type*} (q : V → V → ℝ) (S T : Finset V)
    (hq : ∀ x y, 0 ≤ q x y) : 0 ≤ cutFlow q S T :=
  Finset.sum_nonneg (fun x _ ↦ Finset.sum_nonneg (fun y _ ↦ hq x y))

theorem cutFlow_mono_right {V : Type*} (q : V → V → ℝ) (S : Finset V)
    {T U : Finset V} (hq : ∀ x y, 0 ≤ q x y) (hTU : T ⊆ U) :
    cutFlow q S T ≤ cutFlow q S U := by
  apply Finset.sum_le_sum
  intro x _
  exact Finset.sum_le_sum_of_subset_of_nonneg hTU (fun y _ _ ↦ hq x y)

theorem cutFlow_union_left {V : Type*} [DecidableEq V]
    (q : V → V → ℝ) {S T : Finset V} (U : Finset V) (hdis : Disjoint S T) :
    cutFlow q (S ∪ T) U = cutFlow q S U + cutFlow q T U :=
  Finset.sum_union hdis

theorem cutFlow_remove_union_le {V : Type*} [Fintype V] [DecidableEq V]
    (q : V → V → ℝ) (A U : Finset V) (hq : ∀ x y, 0 ≤ q x y)
    (hU : U ⊆ Aᶜ) :
    cutFlow q (A ∪ U) (A ∪ U)ᶜ ≤
      cutFlow q A Aᶜ + cutFlow q U (Aᶜ \ U) := by
  have hdis : Disjoint A U := by
    apply Finset.disjoint_left.mpr
    intro x hxA hxU
    exact (Finset.mem_compl.mp (hU hxU)) hxA
  have hcomp : (A ∪ U)ᶜ = Aᶜ \ U := by
    ext x
    simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_sdiff]
    tauto
  rw [cutFlow_union_left q _ hdis, hcomp]
  exact add_le_add
    (cutFlow_mono_right q A hq Finset.sdiff_subset) le_rfl

theorem finite_balanced_flow_pruning {V : Type*} [Fintype V] [DecidableEq V]
    (pi : V → ℝ) (q : V → V → ℝ) (epsilon B : ℝ)
    (hpi : ∀ x, 0 < pi x) (hpi_sum : ∑ x, pi x = 1)
    (hq : ∀ x y, 0 ≤ q x y) (hepsilon : 0 < epsilon)
    (hepsilon_third : epsilon < 1 / 3) (hB : 0 < B)
    (hbalanced : ∀ S : Finset V, epsilon ≤ cutMass pi S →
      cutMass pi S ≤ 1 - epsilon → B < cutFlow q S Sᶜ) :
    ∃ C : Finset V, 1 - epsilon < cutMass pi C ∧
      ∀ U : Finset V, U ⊆ C → cutMass pi U ≤ cutMass pi C / 2 →
        B * cutMass pi U ≤ cutFlow q U (C \ U) := by
  let choices : Finset (Finset V) := Finset.univ.filter (fun A ↦
    cutMass pi A < epsilon ∧ cutFlow q A Aᶜ ≤ B * cutMass pi A)
  have hchoices : choices.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [choices, hepsilon]
  obtain ⟨A, hAmem, hAmax⟩ := Finset.exists_max_image choices Finset.card hchoices
  have hA := (Finset.mem_filter.mp hAmem).2
  refine ⟨Aᶜ, ?_, ?_⟩
  · rw [cutMass_compl pi A hpi_sum]
    linarith [hA.1]
  · intro U hU hhalf
    by_contra hnot
    have hbad : cutFlow q U (Aᶜ \ U) < B * cutMass pi U := lt_of_not_ge hnot
    have hU_nonempty : U.Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hbad
      simp at hbad
    have hdis : Disjoint A U := by
      apply Finset.disjoint_left.mpr
      intro x hxA hxU
      exact (Finset.mem_compl.mp (hU hxU)) hxA
    have hnewflow : cutFlow q (A ∪ U) (A ∪ U)ᶜ < B * cutMass pi (A ∪ U) := by
      have h := (cutFlow_remove_union_le q A U hq hU).trans_lt
        (add_lt_add_of_le_of_lt hA.2 hbad)
      rw [cutMass_union pi hdis]
      nlinarith
    have hnewupper : cutMass pi (A ∪ U) < 1 - epsilon := by
      rw [cutMass_union pi hdis]
      rw [cutMass_compl pi A hpi_sum] at hhalf
      linarith [hA.1]
    have hnewsmall : cutMass pi (A ∪ U) < epsilon := by
      by_contra hlarge
      have hbal := hbalanced (A ∪ U) (le_of_not_gt hlarge) hnewupper.le
      have hmass := cutMass_le_one pi (A ∪ U) (fun x ↦ (hpi x).le) hpi_sum
      have hflow_le : B * cutMass pi (A ∪ U) ≤ B := by
        nlinarith
      exact (not_lt_of_ge (hnewflow.le.trans hflow_le)) hbal
    have hnewmem : A ∪ U ∈ choices := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnewsmall, hnewflow.le⟩
    have hcard : A.card < (A ∪ U).card := by
      apply Finset.card_lt_card
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨Finset.subset_union_left, ?_⟩
      intro heq
      obtain ⟨x, hxU⟩ := hU_nonempty
      have hxA : x ∈ A := by
        rw [heq]
        exact Finset.mem_union_right A hxU
      exact (Finset.mem_compl.mp (hU hxU)) hxA
    exact (not_lt_of_ge (hAmax (A ∪ U) hnewmem)) hcard

end SKConstants
