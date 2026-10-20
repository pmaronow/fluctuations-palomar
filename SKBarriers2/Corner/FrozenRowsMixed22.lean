module

public import SKBarriers2.Corner.FrozenRowsMixed19

@[expose] public section

noncomputable section
open scoped Topology
namespace SKBarriers2
local notation "X" => (Fin 3 → ℝ)

theorem moving_noise_score_profiles {r : ℕ} {B δ : ℝ}
    {f₁ f₂ : ℝ → X → ℝ} {Df Dg : ℝ → X → X →L[ℝ] ℝ}
    {D₂f : ℝ → X → X →L[ℝ] X →L[ℝ] ℝ}
    {u₀ u₁ a₀ a₁ : ℝ → X → X}
    (hB : 0 ≤ B)
    (hf₁ : ContDiff ℝ r (Function.uncurry f₁)) (hf₂ : ContDiff ℝ r (Function.uncurry f₂))
    (hDf : ContDiff ℝ r (Function.uncurry Df)) (hDg : ContDiff ℝ r (Function.uncurry Dg))
    (hD₂f : ContDiff ℝ r (Function.uncurry D₂f))
    (hu₀ : ContDiff ℝ r (Function.uncurry u₀)) (hu₁ : ContDiff ℝ r (Function.uncurry u₁))
    (ha₀ : ContDiff ℝ r (Function.uncurry a₀)) (ha₁ : ContDiff ℝ r (Function.uncurry a₁))
    (hf₁j : ∀ t, WJets r (B*(1+|t|)) 0 (f₁ t))
    (hf₂j : ∀ t, WJets r (B*(1+|t|)) 0 (f₂ t))
    (hDfj : ∀ t, WJets r (B*(1+|t|)) 0 (Df t))
    (hDgj : ∀ t, WJets r (B*(1+|t|)) 0 (Dg t))
    (hD₂fj : ∀ t, WJets r (B*(1+|t|)) 0 (D₂f t))
    (hu₀j : ∀ t, WJets r (B*(1+|t|)) 0 (u₀ t))
    (hu₁j : ∀ t, WJets r (B*(1+|t|)) 1 (u₁ t))
    (ha₀j : ∀ t, WJets r (B*(1+|t|)) 0 (a₀ t))
    (ha₁j : ∀ t, WJets r (B*(1+|t|)) 1 (a₁ t)) :
    ∃ s₀ s₁ t₀ t₁ t₂ : ℝ → X → ℝ,
      (ContDiff ℝ r (Function.uncurry s₀) ∧ ContDiff ℝ r (Function.uncurry s₁) ∧
        ContDiff ℝ r (Function.uncurry t₀) ∧ ContDiff ℝ r (Function.uncurry t₁) ∧
        ContDiff ℝ r (Function.uncurry t₂)) ∧
      (∀ t, WJets r (movingScoreProfileBudget r B*(1+|t|)^3) 0 (s₀ t) ∧
        WJets r (movingScoreProfileBudget r B*(1+|t|)^3) 1 (s₁ t) ∧
        WJets r (movingScoreProfileBudget r B*(1+|t|)^3) 0 (t₀ t) ∧
        WJets r (movingScoreProfileBudget r B*(1+|t|)^3) 1 (t₁ t) ∧
        WJets r (movingScoreProfileBudget r B*(1+|t|)^3) 2 (t₂ t)) ∧
      (∀ t y, f₁ t y+Df t y (u₀ t y+δ • u₁ t y) = s₀ t y+δ*s₁ t y) ∧
      (∀ t y, f₂ t y+2*Dg t y (u₀ t y+δ • u₁ t y)+
        D₂f t y (u₀ t y+δ • u₁ t y) (u₀ t y+δ • u₁ t y)+
        Df t y (a₀ t y+δ • a₁ t y) = t₀ t y+δ*t₁ t y+δ^2*t₂ t y) := by
  let s₀ := fun t => movingScoreFirst0 (f₁ t) (Df t) (u₀ t)
  let s₁ := fun t => movingScoreFirst1 (Df t) (u₁ t)
  let t₀ := fun t => movingScoreSecond0 (f₂ t) (Df t) (Dg t) (D₂f t) (u₀ t) (a₀ t)
  let t₁ := fun t => movingScoreSecond1 (Df t) (Dg t) (D₂f t) (u₀ t) (u₁ t) (a₁ t)
  let t₂ := fun t => movingScoreSecond2 (D₂f t) (u₁ t)
  have hjoint := moving_endpoint_score_profiles_contDiff hf₁ hf₂ hDf hDg hD₂f hu₀ hu₁ ha₀ ha₁
  have hslice (t : ℝ) := moving_endpoint_score_profiles_explicit (δ := δ)
    (hf₁j t) (hf₂j t) (hDfj t) (hDgj t) (hD₂fj t) (hu₀j t) (hu₁j t) (ha₀j t) (ha₁j t)
  refine ⟨s₀,s₁,t₀,t₁,t₂,?_,?_,?_,?_⟩
  · exact hjoint
  · intro t
    have hbudget := movingScoreProfileBudget_mul_le r hB (by linarith [abs_nonneg t] : 1 ≤ 1+|t|)
    have H := hslice t
    exact ⟨H.1.mono hbudget le_rfl,H.2.1.mono hbudget le_rfl,H.2.2.1.mono hbudget le_rfl,
      H.2.2.2.1.mono hbudget le_rfl,H.2.2.2.2.1.mono hbudget le_rfl⟩
  · intro t y
    exact (hslice t).2.2.2.2.2.1 y
  · intro t y
    exact (hslice t).2.2.2.2.2.2 y

end SKBarriers2
