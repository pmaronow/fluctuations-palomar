module

public import ComparisonActualHighWallThetaZeroStarMismatch
public import ComparisonActualHighWallThetaZeroErrorTransport
public import ComparisonActualHighWallThetaZeroInitialCapPoint
public import ComparisonActualHighWallThetaZeroCapTravelCore

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
variable {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem Potential.eq7_inner_nonpositive_squared_mismatch_ae (P : Q.Potential) :
    ∀ᵐr, r∈Icc Q.data.rmin 1 → P.H r≤0 →
      (Q.radiusS r-r)^2 ≤
        16*(Q.data.rmin+Q.cavityCapTravel)^2+
          2*(Q.radiusB r-(Q.radiusS r)^2) := by
  have hmom := Q.radius_moments
  have htravel0 : 0 ≤ Q.cavityCapTravel := by
    unfold cavityCapTravel
    exact mul_nonneg
      (div_nonneg Q.data.hL.le (Real.rpow_nonneg Q.data.hN.le _))
      (Real.log_nonneg ((one_le_div Q.data.hU).mpr (by linarith)))
  filter_upwards [P.hzero, volume.ae_ne Q.data.rmin,
    volume.ae_ne (1:ℝ)] with r hrzero hr0 hr1 hri hnonpos
  have hro : r∈Ioo Q.data.rmin 1 :=
    ⟨lt_of_le_of_ne hri.1 hr0.symm,lt_of_le_of_ne hri.2 hr1⟩
  have hthermal : 0 ≤ Q.radiusB r-(Q.radiusS r)^2 :=
    sub_nonneg.mpr (hmom.2.2 r hri).2.1
  rcases hnonpos.eq_or_lt with hz|hneg
  · have H := (hrzero hri hz).2.2
    change (Q.radiusS r-r)^2 ≤ Q.radiusB r-(Q.radiusS r)^2 at H
    nlinarith only [H,hthermal,sq_nonneg (Q.data.rmin+Q.cavityCapTravel)]
  · have hrneg : r∈P.negativeSet := ⟨hro,hneg⟩
    obtain ⟨c,hcl,hcr,heq,hcLeft,hcRight⟩ :=
      P.negative_component_endpoints hrneg
    have hwidth :=
      (P.cap_interval_travel Q c.hleft c.hlt.le c.hright c.negative).2.1
    have hrc : r∈Ioo c.left c.right := by
      rw [heq]
      exact self_mem_ordConnectedComponent.mpr hrneg
    rcases hcLeft with hcontact|hinitial
    · have H := P.star_cap_point_squared_mismatch c.hleft c.hright
        hrc hcontact hcRight hneg
      have hw0 : 0 ≤ c.right-c.left := sub_nonneg.mpr c.hlt.le
      have hsum : c.right-c.left ≤ Q.data.rmin+Q.cavityCapTravel := by
        linarith only [hwidth,Q.data.hrbounds.1]
      have hs := pow_le_pow_left₀ hw0 hsum 2
      nlinarith only [H,hs,hthermal]
    · have hrc' : r∈Ioo Q.data.rmin c.right := by simpa only [hinitial] using hrc
      have hwidth' : c.right-Q.data.rmin≤Q.cavityCapTravel := by
        simpa only [hinitial] using hwidth
      have H := P.initial_cap_point_squared_mismatch c.hright hrc'
        hneg hcRight hwidth' htravel0
      nlinarith only [H,hthermal,sq_nonneg (Q.data.rmin+Q.cavityCapTravel)]

theorem Potential.eq7_inner_nonpositive_mismatch_ae_mass (P : Q.Potential) :
    ∀ᵐu, u∈Icc Q.data.s 1 → P.H (Q.sweepRadius u)≤0 →
      (orderedPathS (n+1) Q.sweepBf Q.sweepHf u-Q.sweepRadius u)^2 ≤
        16*(Q.data.rmin+Q.cavityCapTravel)^2+
          2*Q.shiftedNativeModel.thermal u := by
  have H := ae_inverse_pullback
    (inverseIntegralConstraints_lipschitz Q.data.hm Q.data.hM Q.alpha.property)
    (fun u (_ : u∈Icc Q.data.s 1) =>
      by simpa only [Q.shiftedNativeModel_radius] using
        Q.shiftedNativeModel.R_bounds u)
    (fun u hu => by simpa only [Q.shiftedNativeModel_radius] using
      Q.shiftedNativeModel.R_spec hu)
    P.eq7_inner_nonpositive_squared_mismatch_ae
  filter_upwards [H] with u hu hui hh
  have H' := hu hui hh
  have hinv : Q.alpha.val.val (Q.sweepRadius u) = u := by
    simpa only [Q.shiftedNativeModel_radius] using
      Q.shiftedNativeModel.R_spec hui
  simpa only [radiusS, radiusB, Q.shiftedNativeModel_radius,
    hinv, ShiftedNativeBandModel.thermal] using H'

theorem Potential.eq7_inner_cap_contact_error_le_thermal
    (P : Q.Potential) {lo hi : ℝ}
    (hlo : Q.data.s≤lo) (hlohi : lo≤hi) (hhi : hi≤1) :
    let F := P.negativeSet ∪ P.contactSet
    let R := Q.data.rmin+Q.cavityCapTravel
    (∫u in lo..hi,F.indicator (fun _=>(1:ℝ)) (Q.sweepRadius u)*
      Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      3*Q.lam*(∫u in lo..hi,F.indicator (fun _=>(1:ℝ)) (Q.sweepRadius u)*
        Q.shiftedNativeModel.thermal u)+
      16*Q.lam*R^2*(hi-lo) := by
  let F := P.negativeSet ∪ P.contactSet
  let R := Q.data.rmin+Q.cavityCapTravel
  let mask := fun u=>F.indicator (fun _=>(1:ℝ)) (Q.sweepRadius u)
  let model := Q.shiftedNativeModel
  have hF : MeasurableSet F :=
    P.negativeSet_open.measurableSet.union P.contactSet_measurable
  have hband : Icc lo hi ⊆ Icc (0:ℝ) 1 :=
    Icc_subset_Icc (Q.data.hs.1.le.trans hlo) hhi
  have hiE := (Q.error_mask_intervalIntegrable F hF).mono_set (by
    rw [uIcc_of_le hlohi,uIcc_of_le zero_le_one]
    exact hband)
  have hiT := (model.thermal_mask_integrable F hF).mono_set (by
    rw [uIcc_of_le hlohi,uIcc_of_le zero_le_one]
    exact hband)
  have Hmass := P.eq7_inner_nonpositive_mismatch_ae_mass
  have Hpoint : ∀ᵐu∂volume.restrict (Icc lo hi),
      mask u*Q.data.thetaZeroErrorDensity Q.lam Q.alpha u ≤
        3*Q.lam*(mask u*model.thermal u)+16*Q.lam*R^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae Hmass] with u hu hmis
    have hu0 : u∈Ioc (0:ℝ) 1 :=
      ⟨Q.data.hs.1.trans_le (hlo.trans hu.1),hu.2.trans hhi⟩
    have hui : u∈Icc Q.data.s 1 := ⟨hlo.trans hu.1,hu.2.trans hhi⟩
    have hcoef := Q.data.theta_zero_coefficient_bounds Q.hlam Q.alpha u
    have hT0 := model.thermal_nonneg hu0
    by_cases hp : Q.sweepRadius u∈F
    · have hH : P.H (Q.sweepRadius u)≤0 := by
        rcases hp with hneg|hcontact
        · exact hneg.2.le
        · exact hcontact.2.le
      have hMismatch := hmis hui hH
      have hBr : model.thermal u+
          (orderedPathS (n+1) Q.sweepBf Q.sweepHf u-Q.sweepRadius u)^2 ≤
          3*model.thermal u+16*R^2 := by
        nlinarith only [hMismatch]
      have hBr0 : 0≤3*model.thermal u+16*R^2 := by
        nlinarith only [hT0, sq_nonneg R]
      have H1 := mul_le_mul_of_nonneg_left hBr hcoef.1
      have H2 := mul_le_mul_of_nonneg_right hcoef.2 hBr0
      have Herror : Q.data.thetaZeroErrorDensity Q.lam Q.alpha u ≤
          3*Q.lam*model.thermal u+16*Q.lam*R^2 := by
        change Q.sweepCoefficient u*(model.thermal u+
          (orderedPathS (n+1) Q.sweepBf Q.sweepHf u-Q.sweepRadius u)^2) ≤ _
        nlinarith only [H1,H2]
      simpa only [mask,indicator_of_mem hp,one_mul] using Herror
    · have hlast : 0≤16*Q.lam*R^2 :=
        mul_nonneg (mul_nonneg (by norm_num) Q.hlam.le) (sq_nonneg R)
      simp only [mask,indicator_of_notMem hp,zero_mul,mul_zero,zero_add]
      exact hlast
  have H := intervalIntegral.integral_mono_ae_restrict hlohi hiE
    ((hiT.const_mul (3*Q.lam)).add intervalIntegrable_const) Hpoint
  rw [intervalIntegral.integral_add (hiT.const_mul _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const] at H
  dsimp only [F,R,model] at H ⊢
  simp only [Q.shiftedNativeModel_radius] at H ⊢
  simp only [smul_eq_mul] at H
  nlinarith only [H]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
