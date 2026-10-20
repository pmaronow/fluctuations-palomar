module

public import SKBarriers2.Corner.FrozenRowsMixed7

@[expose] public section

noncomputable section
open scoped BigOperators Topology

namespace SKBarriers2

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def movingScoreProfileBudget (r : ℕ) (B : ℝ) : ℝ :=
  1 + B + 4 * (2 : ℝ) ^ r * B ^ 2 + 3 * ((2 : ℝ) ^ r) ^ 2 * B ^ 3

theorem moving_endpoint_score_profiles {r : ℕ} {B δ : ℝ}
    {f₁ f₂ : E → ℝ} {Df Dg : E → V →L[ℝ] ℝ}
    {D₂f : E → V →L[ℝ] V →L[ℝ] ℝ}
    {u₀ u₁ a₀ a₁ : E → V}
    (hf₁ : WJets r B 0 f₁) (hf₂ : WJets r B 0 f₂)
    (hDf : WJets r B 0 Df) (hDg : WJets r B 0 Dg)
    (hD₂f : WJets r B 0 D₂f)
    (hu₀ : WJets r B 0 u₀) (hu₁ : WJets r B 1 u₁)
    (ha₀ : WJets r B 0 a₀) (ha₁ : WJets r B 1 a₁) :
    ∃ s₀ s₁ t₀ t₁ t₂ : E → ℝ,
      WJets r (movingScoreProfileBudget r B) 0 s₀ ∧
      WJets r (movingScoreProfileBudget r B) 1 s₁ ∧
      WJets r (movingScoreProfileBudget r B) 0 t₀ ∧
      WJets r (movingScoreProfileBudget r B) 1 t₁ ∧
      WJets r (movingScoreProfileBudget r B) 2 t₂ ∧
      (∀ x, f₁ x + Df x (u₀ x + δ • u₁ x) = s₀ x + δ * s₁ x) ∧
      (∀ x, f₂ x + 2 * Dg x (u₀ x + δ • u₁ x) +
          D₂f x (u₀ x + δ • u₁ x) (u₀ x + δ • u₁ x) +
          Df x (a₀ x + δ • a₁ x) = t₀ x + δ * t₁ x + δ ^ 2 * t₂ x) := by
  let S : ℝ := (2 : ℝ) ^ r
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hB := hf₁.nonneg
  have h₂ : 0 ≤ S * B ^ 2 := by positivity
  have h₃ : 0 ≤ S ^ 2 * B ^ 3 := by positivity
  have hFu₀ : WJets r (S * B ^ 2) 0 (fun x => Df x (u₀ x)) := by
    convert hDf.clm_apply hu₀ using 1
    dsimp only [S]
    ring
  have hFu₁ : WJets r (S * B ^ 2) 1 (fun x => Df x (u₁ x)) := by
    convert hDf.clm_apply hu₁ using 1
    dsimp only [S]
    ring
  have hFa₀ : WJets r (S * B ^ 2) 0 (fun x => Df x (a₀ x)) := by
    convert hDf.clm_apply ha₀ using 1
    dsimp only [S]
    ring
  have hFa₁ : WJets r (S * B ^ 2) 1 (fun x => Df x (a₁ x)) := by
    convert hDf.clm_apply ha₁ using 1
    dsimp only [S]
    ring
  have hGu₀ : WJets r (S * B ^ 2) 0 (fun x => Dg x (u₀ x)) := by
    convert hDg.clm_apply hu₀ using 1
    dsimp only [S]
    ring
  have hGu₁ : WJets r (S * B ^ 2) 1 (fun x => Dg x (u₁ x)) := by
    convert hDg.clm_apply hu₁ using 1
    dsimp only [S]
    ring
  have hH₀₀ : WJets r (S ^ 2 * B ^ 3) 0 (fun x => D₂f x (u₀ x) (u₀ x)) := by
    convert (hD₂f.clm_apply hu₀).clm_apply hu₀ using 1
    dsimp only [S]
    ring
  have hH₀₁ : WJets r (S ^ 2 * B ^ 3) 1 (fun x => D₂f x (u₀ x) (u₁ x)) := by
    convert (hD₂f.clm_apply hu₀).clm_apply hu₁ using 1
    dsimp only [S]
    ring
  have hH₁₀ : WJets r (S ^ 2 * B ^ 3) 1 (fun x => D₂f x (u₁ x) (u₀ x)) := by
    convert (hD₂f.clm_apply hu₁).clm_apply hu₀ using 1
    dsimp only [S]
    ring
  have hH₁₁ : WJets r (S ^ 2 * B ^ 3) 2 (fun x => D₂f x (u₁ x) (u₁ x)) := by
    convert (hD₂f.clm_apply hu₁).clm_apply hu₁ using 1
    dsimp only [S]
    ring
  let s₀ : E → ℝ := fun x => f₁ x + Df x (u₀ x)
  let s₁ : E → ℝ := fun x => Df x (u₁ x)
  let t₀ : E → ℝ := fun x => f₂ x + 2 * Dg x (u₀ x) +
    D₂f x (u₀ x) (u₀ x) + Df x (a₀ x)
  let t₁ : E → ℝ := fun x => 2 * Dg x (u₁ x) +
    D₂f x (u₀ x) (u₁ x) + D₂f x (u₁ x) (u₀ x) + Df x (a₁ x)
  let t₂ : E → ℝ := fun x => D₂f x (u₁ x) (u₁ x)
  refine ⟨s₀, s₁, t₀, t₁, t₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hf₁.add hFu₀).mono (by dsimp only [movingScoreProfileBudget]; nlinarith) le_rfl
  · exact hFu₁.mono (by dsimp only [movingScoreProfileBudget]; nlinarith) le_rfl
  · have H := ((hf₂.add (hGu₀.const_smul 2)).add hH₀₀).add hFa₀
    change WJets r _ 0 (fun x => f₂ x + 2 * Dg x (u₀ x) + D₂f x (u₀ x) (u₀ x) + Df x (a₀ x))
    apply H.mono _ le_rfl
    norm_num
    dsimp only [movingScoreProfileBudget]
    change B + 2 * (S * B ^ 2) + S ^ 2 * B ^ 3 + S * B ^ 2 ≤ _
    nlinarith
  · have H := (((hGu₁.const_smul 2).add hH₀₁).add hH₁₀).add hFa₁
    change WJets r _ 1 (fun x => 2 * Dg x (u₁ x) + D₂f x (u₀ x) (u₁ x) + D₂f x (u₁ x) (u₀ x) + Df x (a₁ x))
    apply H.mono _ le_rfl
    norm_num
    dsimp only [movingScoreProfileBudget]
    change 2 * (S * B ^ 2) + S ^ 2 * B ^ 3 + S ^ 2 * B ^ 3 + S * B ^ 2 ≤ _
    nlinarith
  · exact hH₁₁.mono (by dsimp only [movingScoreProfileBudget]; nlinarith) le_rfl
  · intro x
    dsimp only [s₀, s₁]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  · intro x
    dsimp only [t₀, t₁, t₂]
    simp only [map_add, map_smul, add_apply,
      smul_apply, smul_eq_mul]
    ring

def affineEndpointScoreCoefficient (r : ℕ) (B : ℝ)
    (A U V : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
    (u₀ a₀ d e : Fin 3 → ℝ) : ℝ :=
  1 + B * max 1 ‖A‖ ^ r + ‖u₀‖ + ‖a₀‖ + ‖U‖ + ‖d‖ + ‖V‖ + ‖e‖

theorem affine_endpoint_score_profiles {r : ℕ} {B δ : ℝ}
    {f g h : (Fin 3 → ℝ) → ℝ}
    (hf : QPotential (r + 2) B f) (hg : QBoundedJets (r + 1) B g)
    (hh : QBoundedJets r B h)
    (A U V : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
    (b u₀ a₀ d e : Fin 3 → ℝ) :
    let C := affineEndpointScoreCoefficient r B A U V u₀ a₀ d e
    ∃ s₀ s₁ t₀ t₁ t₂ : (Fin 3 → ℝ) → ℝ,
      WJets r (movingScoreProfileBudget r C) 0 s₀ ∧
      WJets r (movingScoreProfileBudget r C) 1 s₁ ∧
      WJets r (movingScoreProfileBudget r C) 0 t₀ ∧
      WJets r (movingScoreProfileBudget r C) 1 t₁ ∧
      WJets r (movingScoreProfileBudget r C) 2 t₂ ∧
      (∀ y, g (A y + b) + fderiv ℝ f (A y + b) (u₀ + δ • (U y + d)) =
        s₀ y + δ * s₁ y) ∧
      (∀ y, h (A y + b) + 2 * fderiv ℝ g (A y + b) (u₀ + δ • (U y + d)) +
          fderiv ℝ (fderiv ℝ f) (A y + b) (u₀ + δ • (U y + d)) (u₀ + δ • (U y + d)) +
          fderiv ℝ f (A y + b) (a₀ + δ • (V y + e)) =
        t₀ y + δ * t₁ y + δ ^ 2 * t₂ y) := by
  let C := affineEndpointScoreCoefficient r B A U V u₀ a₀ d e
  have hB := hf.nonneg
  have hD : 0 ≤ B * max 1 ‖A‖ ^ r := by positivity
  have hBC : B * max 1 ‖A‖ ^ r ≤ C := by
    dsimp only [C, affineEndpointScoreCoefficient]
    linarith [norm_nonneg u₀, norm_nonneg a₀, norm_nonneg U, norm_nonneg d,
      norm_nonneg V, norm_nonneg e]
  have hGc : WJets r C 0 (fun y => g (A y + b)) := by
    apply (((hg.of_le (by omega : r ≤ r + 1)).weighted (p := 0)).comp_affine A b).mono _ le_rfl
    simpa only [pow_zero, mul_one] using hBC
  have hHc : WJets r C 0 (fun y => h (A y + b)) := by
    apply ((hh.weighted (p := 0)).comp_affine A b).mono _ le_rfl
    simpa only [pow_zero, mul_one] using hBC
  have hFc : WJets r C 0 (fun y => fderiv ℝ f (A y + b)) := by
    have HD : QBoundedJets r B (fderiv ℝ f) := hf.derivativeJets.of_le (by omega)
    apply ((HD.weighted (p := 0)).comp_affine A b).mono _ le_rfl
    simpa only [pow_zero, mul_one] using hBC
  have hDgc : WJets r C 0 (fun y => fderiv ℝ g (A y + b)) := by
    apply ((hg.derivativeJets.weighted (p := 0)).comp_affine A b).mono _ le_rfl
    simpa only [pow_zero, mul_one] using hBC
  have hHessc : WJets r C 0 (fun y => fderiv ℝ (fderiv ℝ f) (A y + b)) := by
    apply ((hf.derivativeJets.derivativeJets.weighted (p := 0)).comp_affine A b).mono _ le_rfl
    simpa only [pow_zero, mul_one] using hBC
  have hu₀ : WJets r C 0 (fun _ : Fin 3 → ℝ => u₀) := by
    apply (WJets.const r u₀).mono _ le_rfl
    dsimp only [C, affineEndpointScoreCoefficient]
    linarith [norm_nonneg a₀, norm_nonneg U, norm_nonneg d, norm_nonneg V, norm_nonneg e]
  have ha₀ : WJets r C 0 (fun _ : Fin 3 → ℝ => a₀) := by
    apply (WJets.const r a₀).mono _ le_rfl
    dsimp only [C, affineEndpointScoreCoefficient]
    linarith [norm_nonneg u₀, norm_nonneg U, norm_nonneg d, norm_nonneg V, norm_nonneg e]
  have hu₁ : WJets r C 1 (fun y => U y + d) := by
    apply (WJets.affine r U d).mono _ le_rfl
    dsimp only [C, affineEndpointScoreCoefficient]
    linarith [norm_nonneg u₀, norm_nonneg a₀, norm_nonneg V, norm_nonneg e]
  have ha₁ : WJets r C 1 (fun y => V y + e) := by
    apply (WJets.affine r V e).mono _ le_rfl
    dsimp only [C, affineEndpointScoreCoefficient]
    linarith [norm_nonneg u₀, norm_nonneg a₀, norm_nonneg U, norm_nonneg d]
  exact moving_endpoint_score_profiles hGc hHc hFc hDgc hHessc hu₀ hu₁ ha₀ ha₁

end SKBarriers2
