module

public import SKConstants.Completion.SJ7.MGFLimit

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKConstants.Completion.SJ7
variable {B : Type*} [MeasurableSpace B] {μ : Measure B}

theorem localQuadraticMGF_add {X Y : B → ℝ} {vX vY radius : ℝ}
    (hXm : Measurable X) (hYm : Measurable Y)
    (hX : Concentration.LocalQuadraticMGF X μ vX radius)
    (hY : Concentration.LocalQuadraticMGF Y μ vY radius) :
    Concentration.LocalQuadraticMGF (fun u => X u + Y u) μ (2 * (vX + vY)) (radius / 2) := by
  have hresult (θ : ℝ) (hθ : |θ| ≤ radius / 2) :
      Integrable (fun u => Real.exp (θ * (X u + Y u))) μ ∧
      mgf (fun u => X u + Y u) μ θ ≤ Real.exp ((2 * (vX + vY)) * θ ^ 2) := by
    have h2 : |2 * θ| ≤ radius := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith
    have he (z : ℝ) : Real.exp ((2 * θ) * z) = (Real.exp (θ * z)) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hF : MemLp (fun u => Real.exp (θ * X u)) 2 μ := by
      apply (memLp_two_iff_integrable_sq (hXm.const_mul θ).exp.aestronglyMeasurable).mpr
      exact (hX.integrable_exp_mul (2 * θ) h2).congr (ae_of_all _ (fun u => he (X u)))
    have hG : MemLp (fun u => Real.exp (θ * Y u)) 2 μ := by
      apply (memLp_two_iff_integrable_sq (hYm.const_mul θ).exp.aestronglyMeasurable).mpr
      exact (hY.integrable_exp_mul (2 * θ) h2).congr (ae_of_all _ (fun u => he (Y u)))
    have hi : Integrable (fun u => Real.exp (θ * (X u + Y u))) μ := by
      refine (hF.integrable_mul hG).congr (ae_of_all _ (fun u => ?_))
      change Real.exp (θ * X u) * Real.exp (θ * Y u) = Real.exp (θ * (X u + Y u))
      rw [← Real.exp_add]
      congr 1
      ring
    refine ⟨hi, ?_⟩
    have hcs := SKConstantsOAI.SK.Analytic.abs_integral_mul_le_sqrt
      (fun u => Real.exp (θ * X u)) (fun u => Real.exp (θ * Y u)) hF hG
    have hFX : (∫ u, (Real.exp (θ * X u)) ^ 2 ∂μ) = mgf X μ (2 * θ) :=
      integral_congr_ae (ae_of_all _ (fun u => (he (X u)).symm))
    have hGY : (∫ u, (Real.exp (θ * Y u)) ^ 2 ∂μ) = mgf Y μ (2 * θ) :=
      integral_congr_ae (ae_of_all _ (fun u => (he (Y u)).symm))
    rw [hFX, hGY] at hcs
    calc
      _ = ∫ u, Real.exp (θ * X u) * Real.exp (θ * Y u) ∂μ := by
        simp only [mgf, mul_add, Real.exp_add]
      _ ≤ Real.sqrt (mgf X μ (2 * θ)) * Real.sqrt (mgf Y μ (2 * θ)) :=
        (le_abs_self _).trans hcs
      _ ≤ Real.sqrt (Real.exp (vX * (2 * θ) ^ 2)) *
          Real.sqrt (Real.exp (vY * (2 * θ) ^ 2)) :=
        mul_le_mul (Real.sqrt_le_sqrt (hX.mgf_le _ h2)) (Real.sqrt_le_sqrt (hY.mgf_le _ h2))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by
        rw [← Real.exp_half, ← Real.exp_half, ← Real.exp_add]
        congr 1
        ring
  exact ⟨fun θ hθ => (hresult θ hθ).1, fun θ hθ => (hresult θ hθ).2⟩

theorem localQuadraticMGF_four {X₁ X₂ X₃ X₄ : B → ℝ} {v₁ v₂ v₃ v₄ radius : ℝ}
    (h₁m : Measurable X₁) (h₂m : Measurable X₂) (h₃m : Measurable X₃) (h₄m : Measurable X₄)
    (h₁ : Concentration.LocalQuadraticMGF X₁ μ v₁ radius)
    (h₂ : Concentration.LocalQuadraticMGF X₂ μ v₂ radius)
    (h₃ : Concentration.LocalQuadraticMGF X₃ μ v₃ radius)
    (h₄ : Concentration.LocalQuadraticMGF X₄ μ v₄ radius) :
    Concentration.LocalQuadraticMGF (fun u => X₁ u + X₂ u + X₃ u + X₄ u) μ
      (4 * (v₁ + v₂ + v₃ + v₄)) (radius / 4) := by
  have h12 := localQuadraticMGF_add h₁m h₂m h₁ h₂
  have h34 := localQuadraticMGF_add h₃m h₄m h₃ h₄
  have h := localQuadraticMGF_add (h₁m.add h₂m) (h₃m.add h₄m) h12 h34
  have hv : 2 * (2 * (v₁ + v₂) + 2 * (v₃ + v₄)) = 4 * (v₁ + v₂ + v₃ + v₄) := by ring
  have hr : radius / 2 / 2 = radius / 4 := by ring
  rw [hv, hr] at h
  exact h.congr_ae (ae_of_all _ (fun u => by
    change X₁ u + X₂ u + X₃ u + X₄ u = (X₁ u + X₂ u) + (X₃ u + X₄ u)
    ring))

end SKConstants.Completion.SJ7
