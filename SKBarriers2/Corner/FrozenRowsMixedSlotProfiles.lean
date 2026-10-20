module

public import SKBarriers2.Corner.FrozenRowsMixedValue2
public import SKBarriers2.Analysis.SmallScalePowers

@[expose] public section

noncomputable section
open scoped Topology
open SKOptimized.Overshoot

namespace SKBarriers2
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure IntrinsicTestProfiles (r : ℕ) (C : ℝ) (p : ℕ) (δ : ℝ)
    (f a b : E → ℝ) : Prop where
  value : WJets (r+2) C p f
  first : WJets (r+1) C p a
  second : WJets r C p b
  coarse_value : WQ (r+1) C (p-2) (fun x => δ*f x)
  coarse_gradient : WJets r C (p-2) (fun x => δ • fderiv ℝ f x)
  coarse_hessian : WJets r C (p-2) (fun x => δ • fderiv ℝ (fderiv ℝ f) x)
  coarse_first : WJets r C (p-1) (fun x => δ*a x)
  coarse_first_gradient : WJets r C (p-1) (fun x => δ • fderiv ℝ a x)

private theorem wJets_div_of_one_le {r p : ℕ} {C W : ℝ} {f : E → ℝ}
    (hf : WJets r C p f) (hW : 1 ≤ W) : WJets r C p (fun x => f x/W) := by
  have hW0 : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hi : |W⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (inv_nonneg.mpr hW0.le), inv_eq_one_div]
    exact (div_le_iff₀ hW0).mpr (by simpa only [one_mul] using hW)
  have H := (hf.const_smul W⁻¹).mono (mul_le_of_le_one_left hf.nonneg hi) le_rfl
  simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using H

namespace Corner.MomentKJet

theorem intrinsicTestProfiles_of_fine_coarse {r N : ℕ} {Df Db Mc M ρ W : ℝ}
    {J : Vec3 → MomentKJet} (hN : 1 ≤ N) (hN3 : N ≤ 3)
    (hDf : 0 ≤ Df) (hDb : 0 ≤ Db) (hMc : 0 ≤ Mc)
    (hM : 1 ≤ M) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hW : 1 ≤ W)
    (hfine : SpatialBound (r+2) (Df*M^N) (3*N) J)
    (hcoarse : FirstDegreeBound (r+2) (Db*(Mc/ρ)^N) (2*N-1) J) :
    IntrinsicTestProfiles r ((Df+Db*(max 1 Mc)^3)*M^N) (3*N) (ρ^3/W)
      (fun x => (J x).value) (fun x => (J x).first/W) (fun x => (J x).second/W^2) := by
  let C := (Df+Db*(max 1 Mc)^3)*M^N
  let Cb := Db*(Mc/ρ)^N
  let δ := ρ^3/W
  let f := fun x => (J x).value
  let a := fun x => (J x).first/W
  have hMn : 0 ≤ M^N := pow_nonneg (zero_le_one.trans hM) N
  have hK : 0 ≤ (max 1 Mc)^3 := pow_nonneg (zero_le_one.trans (le_max_left _ _)) 3
  have hFine : Df*M^N ≤ C :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg hDb hK)) hMn
  have hCb : 0 ≤ Cb := mul_nonneg hDb (pow_nonneg (div_nonneg hMc hρ.le) N)
  have hW0 : 0 < W := lt_of_lt_of_le zero_lt_one hW
  have hδ : 0 ≤ δ := div_nonneg (pow_nonneg hρ.le 3) hW0.le
  have hδle : δ ≤ ρ^3 :=
    (div_le_iff₀ hW0).mpr (le_mul_of_one_le_right (pow_nonneg hρ.le 3) hW)
  have hScale : |δ| * Cb ≤ C := by
    rw [abs_of_nonneg hδ]
    calc
      δ*Cb ≤ ρ^3*Cb := mul_le_mul_of_nonneg_right hδle hCb
      _ = Db*(ρ^3*(Mc/ρ)^N) := by dsimp only [Cb]; ring
      _ ≤ Db*((max 1 Mc)^3*M^N) := mul_le_mul_of_nonneg_left
        (cube_mul_normalized_power_le hρ hρ1 hMc hM hN3) hDb
      _ = (Db*(max 1 Mc)^3)*M^N := by ring
      _ ≤ C := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hDf) hMn
  have hDegree : 2*N-1 ≤ 3*N-2 := by omega
  have hFirstDegree : (2*N-1)+1 ≤ 3*N-1 := by omega
  have hPositive : WQ (r+2) Cb (2*N-1) f := hcoarse.value.positive
  have hGradient : WJets (r+1) Cb (2*N-1) (fderiv ℝ f) := hPositive.derivativeJets
  have hHessian : WJets r Cb (2*N-1) (fderiv ℝ (fderiv ℝ f)) := hGradient.derivativeJets
  have hFirst : WJets (r+2) Cb ((2*N-1)+1) a := wJets_div_of_one_le hcoarse.first hW
  have hFirstGradient : WJets (r+1) Cb ((2*N-1)+1) (fderiv ℝ a) := hFirst.derivativeJets
  refine ⟨hfine.1.mono hFine le_rfl,
    (wJets_div_of_one_le hfine.2.1 hW).of_le (by omega) |>.mono hFine le_rfl,
    (wJets_div_of_one_le (W := W^2) hfine.2.2 (one_le_pow₀ hW)).of_le (by omega) |>.mono hFine le_rfl,
    ?_,?_,?_,?_,?_⟩
  · simpa only [smul_eq_mul] using
      ((hPositive.const_smul δ).mono hScale hDegree).of_le (by omega : r+1 ≤ r+2)
  · exact ((hGradient.const_smul δ).mono hScale hDegree).of_le (by omega)
  · exact (hHessian.const_smul δ).mono hScale hDegree
  · simpa only [smul_eq_mul] using
      ((hFirst.const_smul δ).mono hScale hFirstDegree).of_le (by omega : r ≤ r+2)
  · exact ((hFirstGradient.const_smul δ).mono hScale hFirstDegree).of_le (by omega)

end Corner.MomentKJet
end SKBarriers2
