module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Filter

theorem nonnegative_sequence_bounded_or_divergent_subsequence
    (f : ℕ→ℝ) (hf : ∀n,0 ≤ f n) :
    (∃φ : ℕ→ℕ,StrictMono φ ∧ ∃K : ℝ,0 ≤ K ∧ ∀n,f (φ n) ≤ K) ∨
    (∃φ : ℕ→ℕ,StrictMono φ ∧ Tendsto (fun n=>f (φ n)) atTop atTop) := by
  classical
  by_cases h : ∃K : ℝ,∃ᶠn in atTop,f n ≤ K
  · obtain ⟨K,hK⟩ := h
    obtain ⟨φ,hφ,hbound⟩ := extraction_of_frequently_atTop hK
    exact Or.inl ⟨φ,hφ,K,(hf (φ 0)).trans (hbound 0),hbound⟩
  · refine Or.inr ⟨id,strictMono_id,tendsto_atTop.mpr ?_⟩
    intro b
    have hn : ∀ᶠn in atTop,¬f n ≤ b := not_frequently.mp (fun hb=>h ⟨b,hb⟩)
    exact hn.mono (fun _ hn=>(lt_of_not_ge hn).le)

end OAI.SKFluctuations.LaplaceWindowFormalization
