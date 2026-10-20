module

public import ComparisonSignedCavityRestRawRootPower
public import ComparisonSignedCavityPhysicalMomentJensen

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem physical_raw_ratio_sq_le_of_pair_moments (n l : ℕ) (hl : 0 < l)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) {xs C : ℝ} (hxs : 0 < xs) (hC : 0 ≤ C)
    (H : ∀j ≤ steps.length,
      physicalOverlapMoment n l steps (Measure.pi fun i => gaussianReal 0 (q₀ i))
        id measurable_id j ≤ (C*(xs+physicalCutMass 0 steps j))^(2*l)) :
    (physicalRawRatio n l steps 0 xs (Measure.pi fun i => gaussianReal 0 (q₀ i))
      id measurable_id)^2 ≤ 2*max 1 C := by
  apply physicalRawRatio_close n l steps ha hxs (le_max_left 1 C)
  intro j hj
  have hmass : 0 ≤ xs+physicalCutMass 0 steps j :=
    add_nonneg hxs.le (physicalCutMass_mem steps ha j).1
  have herr : 0 ≤ (physicalRawRatio n l steps 0 xs
      (Measure.pi fun i => gaussianReal 0 (q₀ i)) id measurable_id)^2/2*
        (xs+physicalCutMass 0 steps j) := by positivity
  suffices hh :
      ((∫p,‖actualSpinPath n steps id j p‖^(4*l)
        ∂physicalPathLaw (Measure.pi fun i => gaussianReal 0 (q₀ i))
          n steps id measurable_id)^(((4*l:ℕ):ℝ)⁻¹))^2 ≤
        max 1 C*(xs+physicalCutMass 0 steps j) by linarith
  by_cases hjl : j ≤ steps.length
  · have Hmoment := (physical_norm_power_le_overlap_moment n l steps ha q₀ j hjl).trans (H j hjl)
    exact (physical_raw_root_square_le (integral_nonneg (fun p => by positivity))
      (mul_nonneg hC hmass) l hl Hmoment).trans
        (mul_le_mul_of_nonneg_right (le_max_right 1 C) hmass)
  · have hje : j = steps.length+1 := by omega
    have Hone := physical_moment_le_one n l steps ha q₀ j
    rw [rootedHierarchyPathLaw_eq_physical] at Hone
    have Hzero : 0 ≤ (∫p,‖actualSpinPath n steps id j p‖^(4*l)
        ∂physicalPathLaw (Measure.pi fun i => gaussianReal 0 (q₀ i))
          n steps id measurable_id)^(((4*l:ℕ):ℝ)⁻¹) := Real.rpow_nonneg
            (integral_nonneg (fun p => by positivity)) _
    have Hsq : ((∫p,‖actualSpinPath n steps id j p‖^(4*l)
        ∂physicalPathLaw (Measure.pi fun i => gaussianReal 0 (q₀ i))
          n steps id measurable_id)^(((4*l:ℕ):ℝ)⁻¹))^2 ≤ 1 := by nlinarith
    apply Hsq.trans
    rw [hje,physicalCutMass_terminal]
    have hmax : 1 ≤ max 1 C := le_max_left _ _
    nlinarith

end OAI.SKFluctuations.Cavity
