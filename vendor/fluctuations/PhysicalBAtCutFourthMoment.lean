module

public import PhysicalCapActualLaw
public import PhysicalWallFourthMoment
public import PhysicalOverlapBandDecomposition

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem physicalSpinTraceCovSq_smooth (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps) :
    BddSmooth 0 (physicalSpinTraceCovSq n steps) := by
  apply BddSmooth.sum Finset.univ
  intro i _
  apply BddSmooth.sum Finset.univ
  intro j _
  simpa only [physicalSpinCovariance, pow_two] using
    (hierarchyCovariance_smooth (uniformWeight_pos n) (finiteFeature n)
      (fun σ => normalizedSpin n σ i) (fun σ => normalizedSpin n σ j) steps ha 0).mul
    (hierarchyCovariance_smooth (uniformWeight_pos n) (finiteFeature n)
      (fun σ => normalizedSpin n σ i) (fun σ => normalizedSpin n σ j) steps ha 0)

theorem physical_B_at_cut_le_fourth_and_covariance (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n)))
    (ha : OrderedSteps 0 (pre ++ tail)) (q₀ : FeatureIndex n → ℝ≥0) :
    stepPairDisorder (uniformWeight n) (finiteFeature n) q₀ pre tail
      (fun σ τ => (orderedOverlap n σ τ)^2) 0 ≤
      2*(∫ p, ‖actualSpinPath n (pre ++ tail) id pre.length p‖^4
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ (pre ++ tail)) +
      2*(∫ p, physicalSpinTraceCovSq n tail (actualCutField pre tail p.1 p.2)
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ (pre ++ tail)) := by
  let htail := ha.suffix pre tail
  let μ := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ (pre ++ tail)
  let B := hierarchyPairMean (uniformWeight n) (finiteFeature n)
    (fun σ τ => (orderedOverlap n σ τ)^2) tail
  have hB : BddSmooth 0 B := hierarchyPairMean_smooth (uniformWeight_pos n)
    (finiteFeature n) _ tail htail 0
  have hcov := physicalSpinTraceCovSq_smooth n tail htail
  have := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q₀ (pre ++ tail) ha
  have hmap := actualCutField_measurable_joint (S := Spin n) pre tail
  have hiB : Integrable (fun p => B (actualCutField pre tail p.1 p.2)) μ :=
    hB.integrable_comp_measurable hmap
  have hiC : Integrable (fun p => physicalSpinTraceCovSq n tail
      (actualCutField pre tail p.1 p.2)) μ := hcov.integrable_comp_measurable hmap
  have hiX : Integrable (fun p => ‖actualSpinPath n (pre ++ tail) id pre.length p‖^4) μ := by
    have h := physicalCutNormPower_integrable n (pre ++ tail) ha
      (Measure.pi fun i => gaussianReal 0 (q₀ i)) id measurable_id pre.length 4
    rw [← rootedHierarchyPathLaw_eq_physical] at h
    exact h
  have hpoint (p : PhysicalPathState (FeatureIndex n → ℝ) n (pre ++ tail)) :
      B (actualCutField pre tail p.1 p.2) ≤
        2*‖actualSpinPath n (pre ++ tail) id pre.length p‖^4 +
          2*physicalSpinTraceCovSq n tail (actualCutField pre tail p.1 p.2) := by
    have hh := physical_overlap_second_le_fourth_mean n tail htail (actualCutField pre tail p.1 p.2)
    have hsq : ‖actualSpinPath n (pre ++ tail) id pre.length p‖^2 =
        ∑ i, (actualSpinMean n tail (actualCutField pre tail p.1 p.2) i)^2 := by
      rw [actualSpinPath_norm_sq_at_cut n pre tail ha,
        hierarchyPairMean_overlap_eq_norm n tail htail, EuclideanSpace.norm_sq_eq]
      simp only [actualSpinMean, Real.norm_eq_abs, sq_abs]
    have hfour : ‖actualSpinPath n (pre ++ tail) id pre.length p‖^4 =
        (∑ i, (actualSpinMean n tail (actualCutField pre tail p.1 p.2) i)^2)^2 := by
      rw [show (4 : ℕ) = 2*2 by norm_num, pow_mul, hsq]
    rw [hfour]
    exact hh
  have h := integral_mono hiB ((hiX.const_mul 2).add (hiC.const_mul 2)) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (hiX.const_mul 2) (hiC.const_mul 2), integral_const_mul, integral_const_mul] at h
  change _ ≤ _
  rw [stepPairDisorder,
    stepPairMean_eq_levelPairMean (uniformWeight_pos n) (finiteFeature n) _ pre tail htail,
    levelPairMean_prefix,
    physicalPrefixTest_eq_rootedCutExpectation n pre tail ha q₀ B hB]
  exact h

theorem physical_B_at_cut_le_window (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n)))
    (ha : OrderedSteps 0 (pre ++ tail)) (q₀ : FeatureIndex n → ℝ≥0)
    (J : Finset (Fin ((pre ++ tail).length+1)))
    (hv : 0 < physicalWindowMass (pre ++ tail) 0 J)
    (r : Fin ((pre ++ tail).length+2) → ℝ) (hr : Monotone r)
    (hc : ∀ j, physicalWindowCellMass (pre ++ tail) 0 J j ≠ 0 → r j.castSucc < r j.succ)
    (hi : ∀ j ∈ J, pre.length ≤ j.val) {M W C : ℝ} (hW : 0 ≤ W)
    (hS : ∀ j ∈ J,
      (∫ p, ‖actualSpinPath n (pre ++ tail) id j.val p‖^2
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ (pre ++ tail)) ≤ M)
    (henergy : (∫ p, physicalSusceptibilityMassIntegral n (pre ++ tail) id
      (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
        (physicalWindowCellMass (pre ++ tail) 0 J)) (radiusGridCut r) p
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ (pre ++ tail)) ≤ W)
    (hcov : (∫ p, physicalSpinTraceCovSq n tail (actualCutField pre tail p.1 p.2)
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ (pre ++ tail)) ≤ C) :
    stepPairDisorder (uniformWeight n) (finiteFeature n) q₀ pre tail
      (fun σ τ => (orderedOverlap n σ τ)^2) 0 ≤
      4*M^2+(112/3 : ℝ)*(physicalWindowMass (pre ++ tail) 0 J)⁻¹^2*W+2*C := by
  have hfour := physical_wall_fourth_moment_le n (pre ++ tail) ha q₀ J hv r hr hc hi hW hS henergy
  have hB := physical_B_at_cut_le_fourth_and_covariance n pre tail ha q₀
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
