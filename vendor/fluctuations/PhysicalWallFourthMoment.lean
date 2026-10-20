module

public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalPinnedWindow

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations

open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem physical_wall_window_variance_le (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length + 1)))
    (r : Fin (steps.length + 2) → ℝ) (hr : Monotone r)
    (hc : ∀ j, physicalWindowCellMass steps 0 J j ≠ 0 → r j.castSucc < r j.succ) :
    variance (fun z => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 (physicalWindowWeight steps 0 J) z.1 z.2).1)
        (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤
      (physicalWindowMass steps 0 J)⁻¹ ^ 2 *
        (∫ z, physicalSusceptibilityMassIntegral n steps id
          (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
            (physicalWindowCellMass steps 0 J)) (radiusGridCut r) z
          ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) := by
  let d := Fintype.card (Fin (steps.length + 1) × FeatureIndex n)
  let e : Fin d ≃ Fin (steps.length + 1) × FeatureIndex n := (Fintype.equivFin _).symm
  have h := physical_planted_variance_le q₀ steps ha e (physicalWindowWeight steps 0 J)
  dsimp only [Function.uncurry] at h
  have heq (z : PhysicalPathState (FeatureIndex n → ℝ) n steps) :
      (physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
        steps 0 (physicalWindowWeight steps 0 J) z.1 z.2).2 =
      (physicalWindowMass steps 0 J)⁻¹ ^ 2 *
        physicalSusceptibilityMassIntegral n steps id
          (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
            (physicalWindowCellMass steps 0 J)) (radiusGridCut r) z := by
    simpa only [id_eq] using physical_radius_window_energy n steps ha J r hr hc id z
  simp_rw [heq] at h
  rw [integral_const_mul] at h
  exact h

theorem fourth_moment_from_quarter_root_bound {I M A : ℝ}
    (hI : 0 ≤ I) (hA : 0 ≤ A)
    (h : (I ^ ((4 : ℝ)⁻¹)) ^ 2 ≤ M + 2 * Real.sqrt A) :
    I ≤ 2 * M ^ 2 + 8 * A := by
  have hroot : ((I ^ ((4 : ℝ)⁻¹)) ^ 2) ^ 2 = I := by
    rw [← pow_mul, ← Real.rpow_mul_natCast hI]
    norm_num
  have hsquare := pow_le_pow_left₀ (sq_nonneg (I ^ ((4 : ℝ)⁻¹))) h 2
  rw [hroot] at hsquare
  have hsqrt := Real.sq_sqrt hA
  nlinarith [sq_nonneg (M - 2 * Real.sqrt A)]

theorem physical_wall_fourth_moment_le (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length + 1)))
    (hv : 0 < physicalWindowMass steps 0 J)
    (r : Fin (steps.length + 2) → ℝ) (hr : Monotone r)
    (hc : ∀ j, physicalWindowCellMass steps 0 J j ≠ 0 → r j.castSucc < r j.succ)
    {i : ℕ} (hi : ∀ j ∈ J, i ≤ j.val) {M W : ℝ} (hW : 0 ≤ W)
    (hS : ∀ j ∈ J,
      (∫ z, ‖actualSpinPath n steps id j.val z‖ ^ 2
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤ M)
    (henergy :
      (∫ z, physicalSusceptibilityMassIntegral n steps id
        (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
          (physicalWindowCellMass steps 0 J)) (radiusGridCut r) z
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤ W) :
    (∫ z, ‖actualSpinPath n steps id i z‖ ^ 4
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤
        2 * M ^ 2 + (56 / 3 : ℝ) * (physicalWindowMass steps 0 J)⁻¹ ^ 2 * W := by
  have h := physical_raw_window_bound n 1 (by norm_num) steps ha q₀ J hv
    r hr hc hi hS
  dsimp only at h
  norm_num at h
  simp only [← inv_pow, one_div] at h
  have hI : 0 ≤ (∫ z, ‖actualSpinPath n steps id i z‖ ^ 4
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) :=
    integral_nonneg fun z => pow_nonneg (norm_nonneg _) _
  have hcoeff : 0 ≤ (7 / 3 : ℝ) * (physicalWindowMass steps 0 J)⁻¹ ^ 2 := by
    positivity
  have hupper := mul_le_mul_of_nonneg_left henergy hcoeff
  have hsqrt := Real.sqrt_le_sqrt hupper
  have h' : ((∫ z, ‖actualSpinPath n steps id i z‖ ^ 4
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ^
        ((4 : ℝ)⁻¹)) ^ 2 ≤
      M + 2 * Real.sqrt ((7 / 3 : ℝ) * (physicalWindowMass steps 0 J)⁻¹ ^ 2 * W) := by
    apply h.trans
    simpa only [add_comm] using
      add_le_add_left (mul_le_mul_of_nonneg_left hsqrt (by norm_num : (0 : ℝ) ≤ 2)) M
  have hfinal := fourth_moment_from_quarter_root_bound hI
    (mul_nonneg hcoeff hW) h'
  convert hfinal using 1 <;> ring

end OAI.SKFluctuations
