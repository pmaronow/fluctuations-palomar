module

public import SKBarriers2.Corner.FrozenRemainder
public import SKBarriers2.Corner.CoreIdentity

@[expose] public section

noncomputable section
open OAI.SK.Analytic SKOptimized.Overshoot Set

namespace SKBarriers2.Corner

def frozenPenalty (α : ℝ → ℝ) (s h k : ℝ) (N : ℕ) : ℝ :=
  matrixChainPenalty (OW.window (fun _ => α s) (1 / 2) s h k N) (fun _ _ => s) -
    matrixChainPenalty (OW.window (fun _ => α s) (1 / 2) s h 0 N) (fun _ _ => s)

theorem frozenPenalty_eq (α : ℝ → ℝ) (s h k : ℝ) {N : ℕ} (hN : 0 < N)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2) :
    frozenPenalty α s h k N = h ^ 2 * α s * penaltyPolynomial (1 / 2) k := by
  simpa only [frozenPenalty, penaltyPolynomial_half] using
    frozen_penalty_difference_half (α s) s h k hN hh hk

theorem transportedFrozenPolynomial_eq (β : ℝ) (α : ℝ → ℝ) (s h k z : ℝ) :
    transportedFrozenPolynomial β α s h k z =
      cornerQuadratic β α s z * (h ^ 2 * α s * penaltyPolynomial (1 / 2) k) +
        h ^ 3 * cornerCubic β α s k z := by
  unfold transportedFrozenPolynomial frozenJetPolynomial
  rw [FJ_coefficient₁, FJ_coefficient₂, FJ_coefficient₃]
  have hc := FJ_terminal_shift_cancellation k (α s) (β ^ 2)
    (jet β α 1 s z) (jet β α 2 s z) (jet β α 3 s z) (jet β α 4 s z)
  unfold frozenJetShift cornerQuadratic cornerCubic
  linear_combination h ^ 3 * hc

def FrozenCoreBound (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h₀ κ : ℝ, 0 < C ∧ 0 < h₀ ∧ 0 < κ ∧ κ ≤ 1 / 2 ∧
    ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ κ → ∀ z : ℝ,
      |frozenDifference β α (α (r - h)) (r - h) h k z -
        (cornerQuadratic β α (r - h) z * frozenPenalty α (r - h) h k 1 +
          h ^ 3 * cornerCubic β α (r - h) k z)| ≤ C * frozenError h k

theorem frozenCoreBound_of_remainder {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (H : FrozenRemainderBound β α I) : FrozenCoreBound β α I := by
  rcases H with ⟨C, h₀, κ, hC, hh₀, hκ, hκ₂, H⟩
  refine ⟨C, h₀, κ, hC, hh₀, hκ, hκ₂, ?_⟩
  intro r hr h hh hhsmall k hk z
  have hb := H r hr h hh hhsmall k hk z
  rw [transportedFrozenPolynomial_eq] at hb
  rw [frozenPenalty_eq α (r - h) h k (by decide) hh.le (hk.trans hκ₂)]
  exact hb

theorem frozenCore_finite_of_remainder {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ}
    (H : FrozenRemainderBound β α I) :
    ∃ C h₀ κ : ℝ, 0 < C ∧ 0 < h₀ ∧ 0 < κ ∧ κ ≤ 1 / 2 ∧
      ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ k : ℝ, |k| ≤ κ →
        ∀ N : ℕ, 0 < N → BoundedDerivs (Phi β α ((r - h) + 4 * h)) → ∀ z : ℝ,
          |(frozenBoundary β α (α (r - h)) (1 / 2) (r - h) h k N z -
              frozenBoundary β α (α (r - h)) (1 / 2) (r - h) h 0 N z) -
            (cornerQuadratic β α (r - h) z * frozenPenalty α (r - h) h k N +
              h ^ 3 * cornerCubic β α (r - h) k z)| ≤ C * frozenError h k := by
  rcases H with ⟨C, h₀, κ, hC, hh₀, hκ, hκ₂, H⟩
  refine ⟨C, h₀, κ, hC, hh₀, hκ, hκ₂, ?_⟩
  intro r hr h hh hhsmall k hk N hN hΦ z
  have hb := H r hr h hh hhsmall k hk z
  rw [transportedFrozenPolynomial_eq,
    frozenDifference_eq_boundary_sub β α (α (r - h)) (r - h) h k z hN hh.le (hk.trans hκ₂) hΦ] at hb
  rw [frozenPenalty_eq α (r - h) h k hN hh.le (hk.trans hκ₂)]
  exact hb

theorem frozenCore_finite_of_remainder_and_jets {β a₀ B : ℝ} {α : ℝ → ℝ} {I J : Set ℝ}
    (H : FrozenRemainderBound β α I) (HJ : FrozenJetHypotheses β α J a₀ B) :
    ∃ C h₀ κ : ℝ, 0 < C ∧ 0 < h₀ ∧ 0 < κ ∧ κ ≤ 1 / 2 ∧
      ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h₀ → (r - h) + 4 * h ∈ J →
        ∀ k : ℝ, |k| ≤ κ → ∀ N : ℕ, 0 < N → ∀ z : ℝ,
          |(frozenBoundary β α (α (r - h)) (1 / 2) (r - h) h k N z -
              frozenBoundary β α (α (r - h)) (1 / 2) (r - h) h 0 N z) -
            (cornerQuadratic β α (r - h) z * frozenPenalty α (r - h) h k N +
              h ^ 3 * cornerCubic β α (r - h) k z)| ≤ C * frozenError h k := by
  rcases frozenCore_finite_of_remainder H with ⟨C, h₀, κ, hC, hh₀, hκ, hκ₂, HC⟩
  refine ⟨C, h₀, κ, hC, hh₀, hκ, hκ₂, ?_⟩
  intro r hr h hh hhsmall ht k hk N hN z
  exact HC r hr h hh hhsmall k hk N hN (HJ.terminal_regular ht) z

end SKBarriers2.Corner
