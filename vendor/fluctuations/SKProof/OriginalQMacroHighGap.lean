module

public import SKProof.Restore.ComparisonActualHighWallThetaZeroMacroWeakHighGapNumerics

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open Set Filter
open scoped Topology

theorem eventually_original_q_macro_high_gap
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ} {N : ℕ → ℕ}
    (hc0 : 0 < c0) (hc0T : c0^2 < T/4)
    (M : (j : ℕ) → ActualThetaZeroOverlapMinimum (N j+1)
      m delta cl cu Az C0 Ct D Bclock)
    (hxs : ∀ j, (M j).xs ≤ 1)
    (hweak : Tendsto (fun j => laplaceComparisonStrength
      (M j).data.d (M j).lam (M j).xs / (M j).xs^2) atTop (𝓝 0))
    (heps : ∀ᶠ j in atTop, T/4 ≤ (M j).data.epsilon) :
    ∃ k : ℕ, ∀ j : ℕ, ∀ u ∈ Ico (0 : ℝ) (M (j+k)).data.s,
      (M (j+k)).changedBare u + (c0*(M (j+k)).xs)^2 ≤
        (M (j+k)).changedBare (M (j+k)).data.s := by
  obtain ⟨k, hk⟩ := eventually_atTop.mp
    (eventually_theta_zero_high_only_gap_of_weak_bounded_test hc0 hc0T M hxs hweak heps)
  exact ⟨k, fun j => hk (j+k) (Nat.le_add_left k j)⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
