module

public import SKBarriers2.Corner.FrozenRowsPotential21
public import SKBarriers2.Corner.FrozenRowsMixed22

@[expose] public section

noncomputable section
open scoped Topology

namespace SKBarriers2.Corner
local notation "V3" => (Fin 3 → ℝ)

set_option maxHeartbeats 0 in
theorem joint_affine_fine_score_profiles {r : ℕ} {B L σ δ : ℝ}
    {f G H : V3 → ℝ} (hf : QPotential (r + 2) B f)
    (hG : QBoundedJets (r + 1) B G) (hH : QBoundedJets r B H)
    (hL : 0 ≤ L) (hσ : |σ| ≤ 1)
    (A U V : V3 →L[ℝ] V3) (b u₀ a₀ : ℝ → V3)
    (hb : ContDiff ℝ r b) (hu₀ : ContDiff ℝ r u₀) (ha₀ : ContDiff ℝ r a₀)
    (hA : ‖A‖ ≤ L) (hU : ‖U‖ ≤ L) (hV : ‖V‖ ≤ L)
    (hu : ∀ t, ‖u₀ t‖ ≤ L * (1 + |t|))
    (ha : ∀ t, ‖a₀ t‖ ≤ L * (1 + |t|)) :
    let K := 1 + B * max 1 L ^ r + L
    ∃ s₀ s₁ t₀ t₁ t₂ : ℝ → V3 → ℝ,
      (ContDiff ℝ r (Function.uncurry s₀) ∧ ContDiff ℝ r (Function.uncurry s₁) ∧
        ContDiff ℝ r (Function.uncurry t₀) ∧ ContDiff ℝ r (Function.uncurry t₁) ∧
        ContDiff ℝ r (Function.uncurry t₂)) ∧
      (∀ t, WJets r (movingScoreProfileBudget r K * (1 + |t|) ^ 3) 0 (s₀ t) ∧
        WJets r (movingScoreProfileBudget r K * (1 + |t|) ^ 3) 1 (s₁ t) ∧
        WJets r (movingScoreProfileBudget r K * (1 + |t|) ^ 3) 0 (t₀ t) ∧
        WJets r (movingScoreProfileBudget r K * (1 + |t|) ^ 3) 1 (t₁ t) ∧
        WJets r (movingScoreProfileBudget r K * (1 + |t|) ^ 3) 2 (t₂ t)) ∧
      (∀ t y, σ * G (A y + b t) +
        fderiv ℝ f (A y + b t) (u₀ t + δ • U y) = s₀ t y + δ * s₁ t y) ∧
      (∀ t y, σ ^ 2 * H (A y + b t) +
        2 * (σ • fderiv ℝ G (A y + b t)) (u₀ t + δ • U y) +
        fderiv ℝ (fderiv ℝ f) (A y + b t) (u₀ t + δ • U y) (u₀ t + δ • U y) +
        fderiv ℝ f (A y + b t) (a₀ t + δ • V y) =
          t₀ t y + δ * t₁ t y + δ ^ 2 * t₂ t y) := by
  let C := B * max 1 L ^ r
  let K := 1 + C + L
  have hB := hf.nonneg
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hCK : C ≤ K := by dsimp only [K]; linarith
  have hLK : L ≤ K := by dsimp only [K]; linarith
  have hCT (t : ℝ) : C ≤ K * (1 + |t|) := hCK.trans
    (le_mul_of_one_le_right hK (by linarith [abs_nonneg t]))
  have hLT (t : ℝ) : L ≤ K * (1 + |t|) := hLK.trans
    (le_mul_of_one_le_right hK (by linarith [abs_nonneg t]))
  have hGT (t : ℝ) : L * (1 + |t|) ≤ K * (1 + |t|) :=
    mul_le_mul_of_nonneg_right hLK (by positivity)
  have hcompose {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
      {g : V3 → Y} (hg : QBoundedJets r B g) (t : ℝ) :
      WJets r C 0 (fun y => g (A y + b t)) := by
    have HC : B * max 1 ‖A‖ ^ r ≤ C :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
        (max_le_max_left 1 hA) r) hB
    exact ((by simpa only [pow_zero,mul_one] using
      (hg.weighted (p := 0)).comp_affine A (b t)) :
        WJets r (B * max 1 ‖A‖ ^ r) 0 (fun y => g (A y + b t))).mono HC le_rfl
  have hG₀ := hG.of_le (Nat.le_succ r)
  have hDf : QBoundedJets r B (fderiv ℝ f) := (hf.of_le (Nat.le_succ (r + 1))).derivativeJets
  have hDg := hG.derivativeJets
  have hD₂f := hf.derivativeJets.derivativeJets
  have hY : ContDiff ℝ r (fun Z : ℝ × V3 => A Z.2 + b Z.1) :=
    (A.contDiff.comp contDiff_snd).add (hb.comp contDiff_fst)
  have hσ₂ : |σ ^ 2| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg σ) hσ
  let f₁ := fun t y => σ * G (A y + b t)
  let f₂ := fun t y => σ ^ 2 * H (A y + b t)
  let Df := fun t y => fderiv ℝ f (A y + b t)
  let Dg := fun t y => σ • fderiv ℝ G (A y + b t)
  let D₂f := fun t y => fderiv ℝ (fderiv ℝ f) (A y + b t)
  have hf₁ : ContDiff ℝ r (Function.uncurry f₁) :=
    contDiff_const.mul (hG₀.smooth.comp hY)
  have hf₂ : ContDiff ℝ r (Function.uncurry f₂) :=
    contDiff_const.mul (hH.smooth.comp hY)
  have hdf : ContDiff ℝ r (Function.uncurry Df) := hDf.smooth.comp hY
  have hdg : ContDiff ℝ r (Function.uncurry Dg) := (hDg.smooth.comp hY).const_smul σ
  have hddf : ContDiff ℝ r (Function.uncurry D₂f) := hD₂f.smooth.comp hY
  have hf₁j (t : ℝ) : WJets r (K * (1 + |t|)) 0 (f₁ t) := by
    exact ((hcompose hG₀ t).const_smul σ).mono
      ((mul_le_of_le_one_left hC hσ).trans (hCT t)) le_rfl
  have hf₂j (t : ℝ) : WJets r (K * (1 + |t|)) 0 (f₂ t) := by
    exact ((hcompose hH t).const_smul (σ ^ 2)).mono
      ((mul_le_of_le_one_left hC hσ₂).trans (hCT t)) le_rfl
  have hdfj (t : ℝ) := (hcompose hDf t).mono (hCT t) le_rfl
  have hdgj (t : ℝ) : WJets r (K * (1 + |t|)) 0 (Dg t) :=
    ((hcompose hDg t).const_smul σ).mono ((mul_le_of_le_one_left hC hσ).trans (hCT t)) le_rfl
  have hddfj (t : ℝ) := (hcompose hD₂f t).mono (hCT t) le_rfl
  have hu₀j (t : ℝ) : WJets r (K * (1 + |t|)) 0 (fun _ : V3 => u₀ t) := (WJets.const r (u₀ t)).mono ((hu t).trans (hGT t)) le_rfl
  have ha₀j (t : ℝ) : WJets r (K * (1 + |t|)) 0 (fun _ : V3 => a₀ t) := (WJets.const r (a₀ t)).mono ((ha t).trans (hGT t)) le_rfl
  have hu₁j (t : ℝ) : WJets r (K * (1 + |t|)) 1 (fun y => U y) := by
    have HS := (WJets.affine r U (0 : V3)).mono (show ‖U‖ + ‖(0 : V3)‖ ≤ K * (1 + |t|) from by
      simpa only [norm_zero,add_zero] using hU.trans (hLT t)) le_rfl
    simpa only [add_zero] using HS
  have ha₁j (t : ℝ) : WJets r (K * (1 + |t|)) 1 (fun y => V y) := by
    have HS := (WJets.affine r V (0 : V3)).mono (show ‖V‖ + ‖(0 : V3)‖ ≤ K * (1 + |t|) from by
      simpa only [norm_zero,add_zero] using hV.trans (hLT t)) le_rfl
    simpa only [add_zero] using HS
  exact moving_noise_score_profiles hK hf₁ hf₂ hdf hdg hddf
    (hu₀.comp contDiff_fst) (U.contDiff.comp contDiff_snd)
    (ha₀.comp contDiff_fst) (V.contDiff.comp contDiff_snd)
    hf₁j hf₂j hdfj hdgj hddfj hu₀j hu₁j ha₀j ha₁j

end SKBarriers2.Corner
