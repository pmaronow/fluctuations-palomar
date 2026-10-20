module

public import Mathlib

@[expose] public section

namespace SKOptimized

open Finset

noncomputable section

def RetainedSuffix (A D : Finset ℕ) : Prop :=
  D ⊆ A ∧ ∀ ⦃i j : ℕ⦄, i ∈ D → j ∈ A → i ≤ j → j ∈ D

def laterRetained (A : Finset ℕ) (i : ℕ) : Finset ℕ :=
  A.filter (fun j => i < j)

def retainedSuccessor (A : Finset ℕ) (i : ℕ) : ℕ :=
  if h : (laterRetained A i).Nonempty then (laterRetained A i).min' h else i

theorem retainedSuccessor_mem {A : Finset ℕ} {i : ℕ}
    (h : (laterRetained A i).Nonempty) : retainedSuccessor A i ∈ A := by
  classical
  unfold retainedSuccessor
  rw [dite_eq_left h]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).1

theorem lt_retainedSuccessor {A : Finset ℕ} {i : ℕ}
    (h : (laterRetained A i).Nonempty) : i < retainedSuccessor A i := by
  classical
  unfold retainedSuccessor
  rw [dite_eq_left h]
  exact (Finset.mem_filter.mp (Finset.min'_mem _ h)).2

theorem retainedSuccessor_le {A : Finset ℕ} {i a : ℕ}
    (ha : a ∈ A) (hia : i < a) : retainedSuccessor A i ≤ a := by
  classical
  have hmem : a ∈ laterRetained A i := Finset.mem_filter.mpr ⟨ha, hia⟩
  have h : (laterRetained A i).Nonempty := ⟨a, hmem⟩
  unfold retainedSuccessor
  rw [dite_eq_left h]
  exact Finset.min'_le _ _ hmem

theorem retainedSuccessor_eq_of_least {A : Finset ℕ} {i a : ℕ}
    (ha : a ∈ A) (hia : i < a)
    (hmin : ∀ k ∈ A, i < k → a ≤ k) : retainedSuccessor A i = a := by
  classical
  have h : (laterRetained A i).Nonempty :=
    ⟨a, Finset.mem_filter.mpr ⟨ha, hia⟩⟩
  apply le_antisymm (retainedSuccessor_le ha hia)
  exact hmin _ (retainedSuccessor_mem h) (lt_retainedSuccessor h)

theorem retainedSuccessor_eq_add_one {A : Finset ℕ} {i : ℕ}
    (h : i + 1 ∈ A) : retainedSuccessor A i = i + 1 := by
  apply retainedSuccessor_eq_of_least h (by omega)
  intro k _ hik
  omega

theorem retainedSuccessor_preserved {A D : Finset ℕ} {i j : ℕ}
    (h : (laterRetained A i).Nonempty)
    (ha : retainedSuccessor A i ∉ D)
    (hj : ∀ k ∈ A, k < j) :
    retainedSuccessor (insert j (A \ D)) i = retainedSuccessor A i := by
  classical
  have ham : retainedSuccessor A i ∈ A := retainedSuccessor_mem h
  have hia : i < retainedSuccessor A i := lt_retainedSuccessor h
  apply retainedSuccessor_eq_of_least
    (Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨ham, ha⟩)) hia
  intro k hk hik
  rcases Finset.mem_insert.mp hk with rfl | hk
  · exact (hj _ ham).le
  · exact retainedSuccessor_le (Finset.mem_sdiff.mp hk).1 hik

theorem all_later_deleted_of_successor_deleted {A D : Finset ℕ} {i : ℕ}
    (hD : RetainedSuffix A D)
    (ha : retainedSuccessor A i ∈ D) :
    ∀ k ∈ A, i < k → k ∈ D := by
  intro k hk hik
  exact hD.2 ha hk (retainedSuccessor_le hk hik)

theorem retainedSuccessor_rewired {A D : Finset ℕ} {i j : ℕ}
    (hD : RetainedSuffix A D)
    (ha : retainedSuccessor A i ∈ D)
    (hij : i < j) :
    retainedSuccessor (insert j (A \ D)) i = j := by
  classical
  apply retainedSuccessor_eq_of_least (Finset.mem_insert_self _ _) hij
  intro k hk hik
  rcases Finset.mem_insert.mp hk with rfl | hk
  · exact le_rfl
  · exact False.elim ((Finset.mem_sdiff.mp hk).2
      (all_later_deleted_of_successor_deleted hD ha k
        (Finset.mem_sdiff.mp hk).1 hik))

theorem retainedSuffix_preserves_prefix {A D : Finset ℕ} {s B H k i : ℕ}
    (hD : RetainedSuffix A D) (hcard : D.card ≤ H) (hk : H + k < B)
    (hblock : Finset.Ico s (s + B) ⊆ A)
    (hi : i ∈ A) (his : i ≤ s + k) : i ∈ A \ D := by
  classical
  refine Finset.mem_sdiff.mpr ⟨hi, ?_⟩
  intro hid
  have hsub : Finset.Ico (s + k) (s + B) ⊆ D := by
    intro a ha
    have hsa := Finset.mem_Ico.mp ha
    apply hD.2 hid
    · apply hblock
      exact Finset.mem_Ico.mpr ⟨by omega, hsa.2⟩
    · omega
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Ico] at hc
  omega

theorem retainedSuffix_preserves_first_two {A D : Finset ℕ} {s B H : ℕ}
    (hD : RetainedSuffix A D) (hcard : D.card ≤ H) (hB : H + 2 ≤ B)
    (hblock : Finset.Ico s (s + B) ⊆ A) :
    s ∈ A \ D ∧ s + 1 ∈ A \ D := by
  have hBpos : 0 < B := by omega
  constructor
  · apply retainedSuffix_preserves_prefix hD hcard (k := 0) (by omega) hblock
    · exact hblock (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
    · omega
  · apply retainedSuffix_preserves_prefix hD hcard (k := 1) (by omega) hblock
    · exact hblock (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
    · omega

theorem replacement_anchor_is_original {A D : Finset ℕ} {s B H : ℕ}
    (hD : RetainedSuffix A D) (hcard : D.card ≤ H) (hB : H + 2 ≤ B)
    (hblock : Finset.Ico s (s + B) ⊆ A) :
    retainedSuccessor (A \ D) s = s + 1 := by
  exact retainedSuccessor_eq_add_one
    (retainedSuffix_preserves_first_two hD hcard hB hblock).2

theorem first_exit_gap_original {ρ ε η d r q ri ra : ℝ}
    (hη : 0 ≤ η)
    (hr : r ≤ ri + ε + 2 * η + 3 * d / 2)
    (hq : ra - 4 * ε - 4 * η - 2 * d ≤ q)
    (hsep : ρ + 5 * ε + 8 * η + 7 * d / 2 ≤ ra - ri) :
    ρ ≤ q - r := by
  linarith

theorem first_exit_gap_rewired {ρ ε η d r q ri ra : ℝ}
    (hη : 0 ≤ η)
    (hr : r ≤ ri + 3 * ε + 4 * η + 3 * d / 2)
    (hq : ra - 2 * ε - 2 * η - 2 * d ≤ q)
    (hsep : ρ + 5 * ε + 8 * η + 7 * d / 2 ≤ ra - ri) :
    ρ ≤ q - r := by
  linarith

theorem first_exit_gap {ρ ε η d r q ri ra : ℝ} {originalI originalA : Prop}
    (hη : 0 ≤ η) (hclass : originalI ∨ originalA)
    (hrOriginal : originalI → r ≤ ri + ε + 2 * η + 3 * d / 2)
    (hr : r ≤ ri + 3 * ε + 4 * η + 3 * d / 2)
    (hqOriginal : originalA → ra - 2 * ε - 2 * η - 2 * d ≤ q)
    (hq : ra - 4 * ε - 4 * η - 2 * d ≤ q)
    (hsep : ρ + 5 * ε + 8 * η + 7 * d / 2 ≤ ra - ri) :
    ρ ≤ q - r := by
  rcases hclass with hi | ha
  · exact first_exit_gap_original hη (hrOriginal hi) hq hsep
  · exact first_exit_gap_rewired hη hr (hqOriginal ha) hsep

end

end SKOptimized
