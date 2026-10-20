module

public import ComparisonOriginalQOuterLocalTaperStarImportFirstDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 18000000
attribute [local instance] Classical.propDecidable

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock}

private theorem interval_error_le_affine
    {f g : ℝ → ℝ} {lo hi a b : ℝ} (hlohi : lo ≤ hi)
    (hf : IntervalIntegrable f volume lo hi)
    (hg : IntervalIntegrable g volume lo hi)
    (hpoint : ∀ᵐ u ∂volume.restrict (Icc lo hi), f u ≤ a*g u+b) :
    (∫u in lo..hi, f u) ≤ a*(∫u in lo..hi, g u)+(hi-lo)*b := by
  have H := intervalIntegral.integral_mono_ae_restrict hlohi hf
    ((hg.const_mul a).add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_add (hg.const_mul a) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    smul_eq_mul] at H
  exact H

private theorem thermal_mask_radius_integral_eq
    (F : Set ℝ) (lo hi : ℝ) :
    (∫u in lo..hi, F.indicator (fun _ => (1:ℝ))
      (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u) =
    ∫u in lo..hi, F.indicator (fun _ => (1:ℝ))
      (Q.sweepRadius u)*Q.shiftedNativeModel.thermal u := by
  simp only [Q.shiftedNativeModel_radius]

private theorem outer_local_masked_error_ae
    (P : Q.Potential) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (htravel : Q.cavityCapTravel ≤ Q.xs)
    {lo hi : ℝ} (hlo : lo ∈ Icc Q.data.s 1)
    (hhi : hi ∈ Icc Q.data.s 1)
    (houter : 2*cu*(Az+1)*Q.xs ≤ lo) :
    let F := P.negativeSet ∪ P.contactSet
    let G := max 1 cu*laplaceComparisonStrength Q.data.d Q.lam lo
    ∀ᵐ u ∂volume.restrict (Icc lo hi),
      F.indicator (fun _ => (1:ℝ)) (Q.sweepRadius u)*
        Q.data.thetaZeroErrorDensity Q.lam Q.alpha u ≤
      3*G*(F.indicator (fun _ => (1:ℝ)) (Q.sweepRadius u)*
        Q.shiftedNativeModel.thermal u)+16*G*Q.cavityCapTravel^2 := by
  let F := P.negativeSet ∪ P.contactSet
  let G := max 1 cu*laplaceComparisonStrength Q.data.d Q.lam lo
  let mask := fun u => F.indicator (fun _ => (1:ℝ)) (Q.sweepRadius u)
  let model := Q.shiftedNativeModel
  have hG : 0 ≤ G :=
    mul_nonneg (zero_le_one.trans (le_max_left _ _))
      (laplaceComparisonStrength_pos Q.data.d Q.hlam lo).le
  have Hmis := P.outer_import_first_star_mismatch_ae_mass_draft
  change ∀ᵐ u ∂volume.restrict (Icc lo hi),
    mask u*Q.data.thetaZeroErrorDensity Q.lam Q.alpha u ≤
      3*G*(mask u*model.thermal u)+16*G*Q.cavityCapTravel^2
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (volume.ae_ne lo),
    ae_restrict_of_ae Hmis]
    with u hu hune hmis
  have hu1 : u ∈ Ioc lo 1 :=
    ⟨lt_of_le_of_ne hu.1 hune.symm,hu.2.trans hhi.2⟩
  have hu0 : u ∈ Ioc (0:ℝ) 1 :=
    ⟨(Q.data.hs.1.trans_le hlo.1).trans hu1.1,hu1.2⟩
  have hcoeff := Q.outer_import_first_coefficient_le_local_strength_draft
    hcu hAz hlo houter hu1
  have hcoef0 :=
    (Q.data.theta_zero_coefficient_bounds Q.hlam Q.alpha u).1
  have hT0 := model.thermal_nonneg hu0
  by_cases hp : Q.sweepRadius u ∈ F
  · have haway := Q.outer_import_first_radius_beyond_initial_cap_draft
      hcu hAz htravel hlo.1 houter hu1
    have hH : P.H (Q.sweepRadius u) ≤ 0 := by
      rcases hp with hneg|hcontact
      · exact hneg.2.le
      · exact hcontact.2.le
    have hMismatch := hmis ⟨hlo.1.trans hu.1,hu.2.trans hhi.2⟩
      haway hH
    have hBr : model.thermal u+
        (orderedPathS (n+1) Q.sweepBf Q.sweepHf u-
          Q.sweepRadius u)^2 ≤
        3*model.thermal u+16*Q.cavityCapTravel^2 := by
      nlinarith only [hMismatch]
    have hBr0 : 0 ≤
        3*model.thermal u+16*Q.cavityCapTravel^2 := by
      positivity
    have H1 := mul_le_mul_of_nonneg_left hBr hcoef0
    have H2 := mul_le_mul_of_nonneg_right hcoeff hBr0
    have Herror : Q.data.thetaZeroErrorDensity Q.lam Q.alpha u ≤
        3*G*model.thermal u+16*G*Q.cavityCapTravel^2 := by
      change Q.sweepCoefficient u*(model.thermal u+
        (orderedPathS (n+1) Q.sweepBf Q.sweepHf u-
          Q.sweepRadius u)^2) ≤ _
      nlinarith only [H1,H2]
    simpa only [mask,indicator_of_mem hp,one_mul] using Herror
  · have hlast : 0 ≤ 16*G*Q.cavityCapTravel^2 := by
      positivity
    simp only [mask,indicator_of_notMem hp,
      zero_mul,mul_zero,zero_add]
    exact hlast

theorem Potential.outer_import_first_local_error_le_thermal_draft
    (P : Q.Potential) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (htravel : Q.cavityCapTravel ≤ Q.xs)
    {lo hi : ℝ} (hlo : lo ∈ Icc Q.data.s 1)
    (hhi : hi ∈ Icc Q.data.s 1) (hlohi : lo ≤ hi)
    (houter : 2*cu*(Az+1)*Q.xs ≤ lo) :
    let F := P.negativeSet ∪ P.contactSet
    let G := max 1 cu*laplaceComparisonStrength Q.data.d Q.lam lo
    (∫u in lo..hi,F.indicator (fun _ => (1:ℝ))
        (Q.sweepRadius u)*
        Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      3*G*(∫u in lo..hi,F.indicator (fun _ => (1:ℝ))
        (Q.sweepRadius u)*Q.shiftedNativeModel.thermal u)+
      16*G*Q.cavityCapTravel^2*(hi-lo) := by
  let F := P.negativeSet ∪ P.contactSet
  let G := max 1 cu*laplaceComparisonStrength Q.data.d Q.lam lo
  have hF : MeasurableSet F :=
    P.negativeSet_open.measurableSet.union P.contactSet_measurable
  have hband : Icc lo hi ⊆ Icc (0:ℝ) 1 :=
    Icc_subset_Icc (Q.data.hs.1.le.trans hlo.1) hhi.2
  have hiE := (Q.error_mask_intervalIntegrable F hF).mono_set (by
    rw [uIcc_of_le hlohi,uIcc_of_le zero_le_one]
    exact hband)
  have hiT := (Q.shiftedNativeModel.thermal_mask_integrable F hF).mono_set (by
    rw [uIcc_of_le hlohi,uIcc_of_le zero_le_one]
    exact hband)
  have Hpoint := outer_local_masked_error_ae P hcu hAz htravel hlo hhi houter
  have H := interval_error_le_affine hlohi hiE hiT
    (a := 3*G) (b := 16*G*Q.cavityCapTravel^2) (by
      simpa only [Q.shiftedNativeModel_radius] using Hpoint)
  rw [thermal_mask_radius_integral_eq F lo hi] at H
  have hconstant : (hi-lo)*(16*G*Q.cavityCapTravel^2) =
      16*G*Q.cavityCapTravel^2*(hi-lo) := by ring
  rw [hconstant] at H
  exact H

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
