module

public import PhysicalCutCovarianceTrace
public import PhysicalBFiniteMassSum
public import PhysicalWallFourthMoment

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem physicalRootLevelB_le_fourth_and_covariance (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (k : ℕ) (hk : k ≤ steps.length) :
    rootLevelPairMean (uniformWeight n) (finiteFeature n) q₀
      (fun σ τ => (orderedOverlap n σ τ)^2) steps k ≤
      2*(∫ p, ‖actualSpinPath n steps id k p‖^4
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) +
      2*(∫ p, physicalCutSpinTraceCovSq n steps id k p
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) := by
  have horder : OrderedSteps 0 (steps.take k ++ steps.drop k) := by
    simpa only [List.take_append_drop] using ha
  have hB := physical_B_at_cut_le_fourth_and_covariance n (steps.take k) (steps.drop k) horder q₀
  have hC := physicalCutSpinTraceCovSq_eq_actualCut n (steps.take k) (steps.drop k) (P := FeatureIndex n → ℝ) id
  simp only [List.length_take,min_eq_left hk,id_eq] at hB hC
  simp_rw [← hC] at hB
  let response (l : List (GaussianStep (FeatureIndex n))) : ℝ :=
    2*(∫ p, ‖actualSpinPath n l id k p‖^4
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ l) +
    2*(∫ p, physicalCutSpinTraceCovSq n l id k p
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ l)
  have heq : response (steps.take k++steps.drop k)=response steps :=
    congrArg response (List.take_append_drop k steps)
  change _ ≤ response (steps.take k++steps.drop k) at hB
  rw [heq] at hB
  rw [physicalRootLevelB_eq_stepPairDisorder n steps ha q₀ k hk]
  exact hB

theorem physicalRootLevelB_le_window_and_square (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (k : ℕ) (hk : k ≤ steps.length)
    (J : Finset (Fin (steps.length+1))) (hv : 0 < physicalWindowMass steps 0 J)
    (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (hc : ∀ j, physicalWindowCellMass steps 0 J j ≠ 0 → r j.castSucc < r j.succ)
    (hi : ∀ j ∈ J, k ≤ j.val) {a M W : ℝ} (ha0 : 0 < a)
    (hacut : a ≤ physicalCutMass 0 steps k) (hW : 0 ≤ W)
    (hS : ∀ j ∈ J, (∫ p, ‖actualSpinPath n steps id j.val p‖^2
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤ M)
    (henergy : (∫ p, physicalSusceptibilityMassIntegral n steps id
      (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
        (physicalWindowCellMass steps 0 J)) (radiusGridCut r) p
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤ W) :
    rootLevelPairMean (uniformWeight n) (finiteFeature n) q₀
      (fun σ τ => (orderedOverlap n σ τ)^2) steps k ≤
      4*M^2+(112/3:ℝ)*(physicalWindowMass steps 0 J)⁻¹^2*W +
      2*(∫ p, physicalCutSourceSquareTrace n steps id k p
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps)/a^2 := by
  have hB := physicalRootLevelB_le_fourth_and_covariance n steps ha q₀ k hk
  have hfour := physical_wall_fourth_moment_le n steps ha q₀ J hv r hr hc hi hW hS henergy
  have hcov := physicalCutSpinTraceCovSq_integral_le_square_of_cutMass n steps ha ha0
    (Measure.pi fun i => gaussianReal 0 (q₀ i)) id measurable_id k hacut
  simp only [Kernel.comap_id] at hcov
  change (∫ p, physicalCutSpinTraceCovSq n steps id k p
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤
    (∫ p, physicalCutSourceSquareTrace n steps id k p
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps)/a^2 at hcov
  simp only [div_eq_mul_inv,mul_assoc] at hcov ⊢
  nlinarith

theorem physicalRootLevelB_massCellSum_le_window_and_square (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (band : List PositiveMass) {start a M W H : ℝ}
    (hband : MassOrdered start band) (offset : ℕ)
    (hk : ∀ j < band.length, offset+j ≤ steps.length)
    (J : Finset (Fin (steps.length+1))) (hv : 0 < physicalWindowMass steps 0 J)
    (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (hc : ∀ j, physicalWindowCellMass steps 0 J j ≠ 0 → r j.castSucc < r j.succ)
    (hi : ∀ i < band.length, ∀ j ∈ J, offset+i ≤ j.val)
    (ha0 : 0 < a) (hacut : ∀ j < band.length, a ≤ physicalCutMass 0 steps (offset+j))
    (hW : 0 ≤ W)
    (hS : ∀ j ∈ J, (∫ p, ‖actualSpinPath n steps id j.val p‖^2
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤ M)
    (henergy : (∫ p, physicalSusceptibilityMassIntegral n steps id
      (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
        (physicalWindowCellMass steps 0 J)) (radiusGridCut r) p
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤ W)
    (htrace : massCellSum band start (fun j =>
      ∫ p, physicalCutSourceSquareTrace n steps id (offset+j) p
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤ H) :
    massCellSum band start (fun j => rootLevelPairMean (uniformWeight n) (finiteFeature n) q₀
      (fun σ τ => (orderedOverlap n σ τ)^2) steps (offset+j)) ≤
      (partitionEnd start band-start)*(4*M^2+(112/3:ℝ)*(physicalWindowMass steps 0 J)⁻¹^2*W)+
      2*H/a^2 := by
  have hpoint (j : ℕ) (hj : j < band.length) := physicalRootLevelB_le_window_and_square n steps ha q₀
    (offset+j) (hk j hj) J hv r hr hc (hi j hj) ha0 (hacut j hj) hW hS henergy
  calc
    _ ≤ massCellSum band start (fun j =>
      (4*M^2+(112/3:ℝ)*(physicalWindowMass steps 0 J)⁻¹^2*W)+
        (2/a^2)*(∫ p, physicalCutSourceSquareTrace n steps id (offset+j) p
          ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps)) := by
      apply massCellSum_mono band hband
      intro j hj
      simpa only [div_eq_mul_inv,mul_assoc,mul_comm ((a^2)⁻¹)] using hpoint j hj
    _ = (partitionEnd start band-start)*(4*M^2+(112/3:ℝ)*(physicalWindowMass steps 0 J)⁻¹^2*W)+
        (2/a^2)*massCellSum band start (fun j =>
          ∫ p, physicalCutSourceSquareTrace n steps id (offset+j) p
            ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) := by
      rw [massCellSum_add,massCellSum_const,massCellSum_const_mul]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left htrace (by positivity : 0 ≤ 2/a^2)
      have he : (2/a^2)*H=2*H/a^2 := by ring
      rw [he] at h
      exact add_le_add le_rfl h

theorem physicalSampledB_internal_band_le_window_and_square (n : ℕ) (b h : ℝ → ℝ≥0)
    (before band after : List PositiveMass) {start finish a M W H : ℝ}
    (hbefore : MassOrdered 0 before) (hendBefore : partitionEnd 0 before=start)
    (hband : MassOrdered start band) (hendBand : partitionEnd start band=finish)
    (hafter : MassOrdered finish after) (hfull : MassOrdered 0 (before++band++after))
    (ha0 : 0 < a) (hW : 0 ≤ W) :
    let steps := sampleClockSteps (completedPathClock (n+1) b h) 0 (before++band++after)
    let q₀ := completedPathClock (n+1) b h 0
    ∀ (J : Finset (Fin (steps.length+1))) (r : Fin (steps.length+2) → ℝ),
    0 < physicalWindowMass steps 0 J → Monotone r →
    (∀ j, physicalWindowCellMass steps 0 J j ≠ 0 → r j.castSucc < r j.succ) →
    (∀ i < band.length, ∀ j ∈ J, before.length+i ≤ j.val) →
    (∀ j < band.length, a ≤ physicalCutMass 0 steps (before.length+j)) →
    (∀ j ∈ J, (∫ p, ‖actualSpinPath (n+1) steps id j.val p‖^2
      ∂rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) q₀ steps) ≤ M) →
    (∫ p, physicalSusceptibilityMassIntegral (n+1) steps id
      (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
        (physicalWindowCellMass steps 0 J)) (radiusGridCut r) p
      ∂rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) q₀ steps) ≤ W →
    massCellSum band start (fun j =>
      ∫ p, physicalCutSourceSquareTrace (n+1) steps id (before.length+j) p
        ∂rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) q₀ steps) ≤ H →
    (∫ u in start..finish, physicalSampledB n b h (before++band++after) hfull u) ≤
      (finish-start)*(4*M^2+(112/3:ℝ)*(physicalWindowMass steps 0 J)⁻¹^2*W)+2*H/a^2 := by
  dsimp only
  intro J r hv hr hc hi hacut hS henergy htrace
  rw [physicalSampledB_internal_band_eq_cutSum n b h before band after hbefore hendBefore
    hband hendBand hafter hfull]
  have hk (j : ℕ) (hj : j < band.length) : before.length+j ≤
      (sampleClockSteps (completedPathClock (n+1) b h) 0 (before++band++after)).length := by
    simp only [sampleClockSteps_length,List.length_append]
    omega
  simpa only [hendBand] using physicalRootLevelB_massCellSum_le_window_and_square (n+1) _
    (sampleClockSteps_ordered _ _ hfull) _ band hband before.length hk J hv r hr hc hi ha0 hacut
    hW hS henergy htrace

end OAI.SKFluctuations.LaplaceWindowFormalization
