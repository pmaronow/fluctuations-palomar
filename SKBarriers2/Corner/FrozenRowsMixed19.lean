module

public import SKBarriers2.Corner.FrozenRowsMixed8

@[expose] public section

noncomputable section
open scoped Topology
namespace SKBarriers2
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem movingScoreProfileBudget_mul_le (r : ℕ) {B W : ℝ}
    (hB : 0 ≤ B) (hW : 1 ≤ W) :
    movingScoreProfileBudget r (B*W) ≤ movingScoreProfileBudget r B*W^3 := by
  have hW₁ : 1 ≤ W^3 := one_le_pow₀ hW
  have hW₂ : W^2 ≤ W^3 := pow_le_pow_right₀ hW (by omega)
  have hW₃ : W ≤ W^3 := by
    simpa only [pow_one] using (pow_le_pow_right₀ hW (by omega : 1 ≤ 3))
  calc
    _ = 1+B*W+4*(2:ℝ)^r*B^2*W^2+3*((2:ℝ)^r)^2*B^3*W^3 := by
      dsimp only [movingScoreProfileBudget]
      ring
    _ ≤ W^3+B*W^3+4*(2:ℝ)^r*B^2*W^3+3*((2:ℝ)^r)^2*B^3*W^3 := by
      apply add_le_add _ le_rfl
      apply add_le_add
      · exact add_le_add hW₁ (mul_le_mul_of_nonneg_left hW₃ hB)
      · exact mul_le_mul_of_nonneg_left hW₂ (by positivity)
    _ = _ := by
      dsimp only [movingScoreProfileBudget]
      ring

def movingScoreFirst0 (f₁ : E → ℝ) (Df : E → V →L[ℝ] ℝ) (u₀ : E → V) : E → ℝ :=
  fun x => f₁ x + Df x (u₀ x)
def movingScoreFirst1 (Df : E → V →L[ℝ] ℝ) (u₁ : E → V) : E → ℝ :=
  fun x => Df x (u₁ x)
def movingScoreSecond0 (f₂ : E → ℝ) (Df Dg : E → V →L[ℝ] ℝ)
    (D₂f : E → V →L[ℝ] V →L[ℝ] ℝ) (u₀ a₀ : E → V) : E → ℝ :=
  fun x => f₂ x + 2 * Dg x (u₀ x) + D₂f x (u₀ x) (u₀ x) + Df x (a₀ x)
def movingScoreSecond1 (Df Dg : E → V →L[ℝ] ℝ)
    (D₂f : E → V →L[ℝ] V →L[ℝ] ℝ) (u₀ u₁ a₁ : E → V) : E → ℝ :=
  fun x => 2 * Dg x (u₁ x) + D₂f x (u₀ x) (u₁ x) + D₂f x (u₁ x) (u₀ x) + Df x (a₁ x)
def movingScoreSecond2 (D₂f : E → V →L[ℝ] V →L[ℝ] ℝ) (u₁ : E → V) : E → ℝ :=
  fun x => D₂f x (u₁ x) (u₁ x)

theorem moving_endpoint_score_profiles_explicit {r : ℕ} {B δ : ℝ}
    {f₁ f₂ : E → ℝ} {Df Dg : E → V →L[ℝ] ℝ}
    {D₂f : E → V →L[ℝ] V →L[ℝ] ℝ}
    {u₀ u₁ a₀ a₁ : E → V}
    (hf₁ : WJets r B 0 f₁) (hf₂ : WJets r B 0 f₂)
    (hDf : WJets r B 0 Df) (hDg : WJets r B 0 Dg)
    (hD₂f : WJets r B 0 D₂f)
    (hu₀ : WJets r B 0 u₀) (hu₁ : WJets r B 1 u₁)
    (ha₀ : WJets r B 0 a₀) (ha₁ : WJets r B 1 a₁) :
    WJets r (movingScoreProfileBudget r B) 0 (movingScoreFirst0 f₁ Df u₀) ∧
      WJets r (movingScoreProfileBudget r B) 1 (movingScoreFirst1 Df u₁) ∧
      WJets r (movingScoreProfileBudget r B) 0 (movingScoreSecond0 f₂ Df Dg D₂f u₀ a₀) ∧
      WJets r (movingScoreProfileBudget r B) 1 (movingScoreSecond1 Df Dg D₂f u₀ u₁ a₁) ∧
      WJets r (movingScoreProfileBudget r B) 2 (movingScoreSecond2 D₂f u₁) ∧
      (∀ x, f₁ x + Df x (u₀ x + δ • u₁ x) =
        movingScoreFirst0 f₁ Df u₀ x + δ * movingScoreFirst1 Df u₁ x) ∧
      (∀ x, f₂ x + 2 * Dg x (u₀ x + δ • u₁ x) +
          D₂f x (u₀ x + δ • u₁ x) (u₀ x + δ • u₁ x) +
          Df x (a₀ x + δ • a₁ x) = movingScoreSecond0 f₂ Df Dg D₂f u₀ a₀ x +
          δ * movingScoreSecond1 Df Dg D₂f u₀ u₁ a₁ x + δ ^ 2 * movingScoreSecond2 D₂f u₁ x) := by
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
    dsimp only [movingScoreFirst0, movingScoreFirst1]
    simp only [map_add, map_smul, smul_eq_mul]
    ring
  · intro x
    dsimp only [movingScoreSecond0, movingScoreSecond1, movingScoreSecond2]
    simp only [map_add, map_smul, add_apply,
      smul_apply, smul_eq_mul]
    ring

theorem moving_endpoint_score_profiles_contDiff {r : ℕ}
    {f₁ f₂ : E → ℝ} {Df Dg : E → V →L[ℝ] ℝ}
    {D₂f : E → V →L[ℝ] V →L[ℝ] ℝ} {u₀ u₁ a₀ a₁ : E → V}
    (hf₁ : ContDiff ℝ r f₁) (hf₂ : ContDiff ℝ r f₂)
    (hDf : ContDiff ℝ r Df) (hDg : ContDiff ℝ r Dg) (hD₂f : ContDiff ℝ r D₂f)
    (hu₀ : ContDiff ℝ r u₀) (hu₁ : ContDiff ℝ r u₁)
    (ha₀ : ContDiff ℝ r a₀) (ha₁ : ContDiff ℝ r a₁) :
    ContDiff ℝ r (movingScoreFirst0 f₁ Df u₀) ∧
      ContDiff ℝ r (movingScoreFirst1 Df u₁) ∧
      ContDiff ℝ r (movingScoreSecond0 f₂ Df Dg D₂f u₀ a₀) ∧
      ContDiff ℝ r (movingScoreSecond1 Df Dg D₂f u₀ u₁ a₁) ∧
      ContDiff ℝ r (movingScoreSecond2 D₂f u₁) := by
  refine ⟨hf₁.add (hDf.clm_apply hu₀), hDf.clm_apply hu₁, ?_, ?_,
    (hD₂f.clm_apply hu₁).clm_apply hu₁⟩
  · unfold movingScoreSecond0
    simpa only [smul_eq_mul] using
      (((hf₂.add ((hDg.clm_apply hu₀).const_smul (2 : ℝ))).add
        ((hD₂f.clm_apply hu₀).clm_apply hu₀)).add (hDf.clm_apply ha₀))
  · unfold movingScoreSecond1
    simpa only [smul_eq_mul] using
      (((((hDg.clm_apply hu₁).const_smul (2 : ℝ)).add
        ((hD₂f.clm_apply hu₀).clm_apply hu₁)).add
        ((hD₂f.clm_apply hu₁).clm_apply hu₀)).add (hDf.clm_apply ha₁))

end SKBarriers2
