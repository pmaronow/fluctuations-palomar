module

public import SKBarriers2.Overshoot.Schedule

@[expose] public section

noncomputable section
open OAI.SK.Analytic

namespace SKBarriers2.Corner

theorem vectorStep_neg {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℝ) (v : E) (f : E → ℝ) : vectorStep m (-v) f = vectorStep m v f := by
  exact OW.vectorStep_neg_direction m v f

theorem vectorStep_comm {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : BoundedDerivs f) (m : ℝ) (v w : E) :
    vectorStep m v (vectorStep m w f) = vectorStep m w (vectorStep m v f) := by
  exact OW.vectorStep_equal_mass_comm hf m v w

theorem boundary_even (β : ℝ) (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ)
    (hΦ : BoundedDerivs (Phi β α (s + 4 * h))) (z : ℝ) :
    OW.boundary β α p s h (-k) N z = OW.boundary β α p s h k N z := by
  exact OW.boundary_even β α p s h k N hΦ z

theorem penalty_even (γ α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ) :
    OW.penalty γ α p s h (-k) N = OW.penalty γ α p s h k N := by
  exact OW.penalty_even γ α p s h k N

theorem trialValue_even (β : ℝ) (γ α : ℝ → ℝ) (r d δ : ℝ) (N : ℕ)
    (hΦ : BoundedDerivs (Phi β α (r - 2 * d + 4 * (2 * d)))) :
    OW.trialValue β γ α r d (-δ) N = OW.trialValue β γ α r d δ N := by
  exact OW.trialValue_even β γ α r d δ N hΦ

def interpolatedProfile (α : ℝ → ℝ) (a lam : ℝ) : ℝ → ℝ :=
  fun t => a + lam * (α t - a)

theorem interpolated_chain_even (β : ℝ) (α : ℝ → ℝ) (a lam p s h k : ℝ) (N : ℕ)
    {f : (Fin 3 → ℝ) → ℝ} (hf : BoundedDerivs f)
    (hsym : f ∘ OW.swap23 = f) (z : ℝ) :
    vectorIncrementChain ((OW.window (interpolatedProfile α a lam) p s h (-k) N).map
      (fun u => (u.1, β • u.2))) f (fun _ => z) =
    vectorIncrementChain ((OW.window (interpolatedProfile α a lam) p s h k N).map
      (fun u => (u.1, β • u.2))) f (fun _ => z) := by
  exact OW.window_chain_even β (interpolatedProfile α a lam) p s h k N hf hsym z

end SKBarriers2.Corner
