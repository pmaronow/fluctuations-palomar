module

public import ComparisonActualHighWallThetaZeroStarMismatch
public import ComparisonActualHighWallThetaZeroPositiveFloorThermal
public import ComparisonActualHighWallThetaZeroErrorTransport

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
variable (Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem outer_import_first_radius_beyond_initial_cap_draft
    (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (htravel : Q.cavityCapTravel ≤ Q.xs) {lo u : ℝ}
    (hlo : Q.data.s ≤ lo)
    (houter : 2*cu*(Az+1)*Q.xs ≤ lo) (hu : u ∈ Ioc lo 1) :
    Q.data.rmin+Q.cavityCapTravel < Q.sweepRadius u := by
  have hpos : 0 < cu*(Az+1)*Q.xs := by
    have hAz1 : 0 < Az+1 := by linarith
    exact mul_pos (mul_pos hcu hAz1) Q.hxs
  have hstrict : cu*(Az+1)*Q.xs < lo := by linarith only [houter,hpos]
  have houter0 : cu*Az*Q.xs < lo := by
    nlinarith only [hstrict,mul_pos hcu Q.hxs]
  have hui : u ∈ Icc Q.data.s 1 := ⟨hlo.trans hu.1.le,hu.2⟩
  have hr := Q.shiftedNativeModel.R_bounds u
  have hspec := Q.shiftedNativeModel.R_spec hui
  have hRlo : lo/cu ≤ Q.sweepRadius u :=
    Q.actual_mass_slab_radius_lower hcu houter0 hr (by
      change lo ≤ Q.alpha.val.val (Q.shiftedNativeModel.R u)
      rw [hspec]
      exact hu.1.le)
  have hwall : Q.data.rmin+Q.cavityCapTravel ≤ (Az+1)*Q.xs := by
    nlinarith only [Q.hz.1,Q.hzxs,htravel]
  have hmiddle : (Az+1)*Q.xs < lo/cu :=
    (lt_div_iff₀ hcu).mpr (by nlinarith only [hstrict])
  exact lt_of_le_of_lt hwall (lt_of_lt_of_le hmiddle hRlo)

theorem outer_import_first_coefficient_le_local_strength_draft
    (hcu : 0 < cu) (hAz : 0 ≤ Az)
    {lo u : ℝ} (hlo : lo ∈ Icc Q.data.s 1)
    (houter : 2*cu*(Az+1)*Q.xs ≤ lo)
    (hu : u ∈ Ioc lo 1) :
    Q.sweepCoefficient u ≤
      max 1 cu*laplaceComparisonStrength Q.data.d Q.lam lo := by
  let g := laplaceComparisonStrength Q.data.d Q.lam
  let r := Q.sweepRadius u
  let K := max 1 cu
  have hstrict : cu*Az*Q.xs < lo := by
    have hpositive : 0 < cu*(Az+1)*Q.xs := by
      have hAz1 : 0 < Az+1 := by linarith
      exact mul_pos (mul_pos hcu hAz1) Q.hxs
    have hcx : 0 < cu*Q.xs := mul_pos hcu Q.hxs
    nlinarith only [houter,hpositive,hcx]
  have hui : u ∈ Icc Q.data.s 1 :=
    ⟨hlo.1.trans hu.1.le,hu.2⟩
  have hr := Q.shiftedNativeModel.R_bounds u
  have hspec := Q.shiftedNativeModel.R_spec hui
  have hRlo : lo/cu ≤ r :=
    Q.actual_mass_slab_radius_lower hcu hstrict hr (by
      change lo ≤ Q.alpha.val.val (Q.shiftedNativeModel.R u)
      rw [hspec]
      exact hu.1.le)
  have hr0 : 0 < r := Q.data.hrbounds.1.trans_le hr.1
  have hrI : r ∈ Icc (0:ℝ) 1 := ⟨hr0.le,hr.2⟩
  have hloI : lo ∈ Icc (0:ℝ) 1 :=
    ⟨Q.data.hs.1.le.trans hlo.1,hlo.2⟩
  have hK : 1 ≤ K := le_max_left _ _
  have hglo : 0 ≤ g lo :=
    (laplaceComparisonStrength_pos Q.data.d Q.hlam lo).le
  have hlor : lo ≤ K*r := by
    have hcuR : lo ≤ cu*r := by
      calc
        lo = cu*(lo/cu) := by field_simp [hcu.ne']
        _ ≤ cu*r := mul_le_mul_of_nonneg_left hRlo hcu.le
    exact hcuR.trans (mul_le_mul_of_nonneg_right
      (le_max_right (1:ℝ) cu) hr0.le)
  have hshape := laplaceComparisonStrength_monotonicities
    Q.data.hd.ne' Q.hlam (show (0:ℝ) ≤ 0 by norm_num)
  have hstrength : g r ≤ K*g lo := by
    by_cases hlor' : lo ≤ r
    · have H := hshape.1 hloI hrI hlor'
      calc
        g r ≤ g lo := H
        _ = 1*g lo := (one_mul _).symm
        _ ≤ K*g lo := mul_le_mul_of_nonneg_right hK hglo
    · have hrl : r ≤ lo := le_of_not_ge hlor'
      have H := hshape.2 hrI hloI hrl
      apply le_of_mul_le_mul_right (a:=r) _ hr0
      calc
        g r*r ≤ g lo*lo := H
        _ ≤ g lo*(K*r) := mul_le_mul_of_nonneg_left hlor hglo
        _ = (K*g lo)*r := by ring
  have hcoef : Q.sweepCoefficient u = g r := by
    simp [sweepCoefficient,omittedStrengthCoefficient,r,g,hui.1]
  rw [hcoef]
  exact hstrength

end ActualThetaZeroOverlapMinimum

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem Potential.outer_import_first_star_mismatch_ae_mass_draft
    (P : Q.Potential) :
    ∀ᵐ u, u ∈ Icc Q.data.s 1 →
      Q.data.rmin+Q.cavityCapTravel < Q.sweepRadius u →
      P.H (Q.sweepRadius u) ≤ 0 →
      (orderedPathS (n+1) Q.sweepBf Q.sweepHf u-
        Q.sweepRadius u)^2 ≤
        16*Q.cavityCapTravel^2+
          2*Q.shiftedNativeModel.thermal u := by
  have H := ae_inverse_pullback
    (inverseIntegralConstraints_lipschitz Q.data.hm Q.data.hM Q.alpha.property)
    (fun u (_ : u ∈ Icc Q.data.s 1) =>
      by simpa only [Q.shiftedNativeModel_radius] using
        Q.shiftedNativeModel.R_bounds u)
    (fun u hu => by simpa only [Q.shiftedNativeModel_radius] using
      Q.shiftedNativeModel.R_spec hu)
    P.star_nonpositive_squared_mismatch_ae
  filter_upwards [H] with u hu hui haway hh
  have H' := hu hui haway hh
  have hinv : Q.alpha.val.val (Q.sweepRadius u) = u := by
    simpa only [Q.shiftedNativeModel_radius] using
      Q.shiftedNativeModel.R_spec hui
  simpa only [radiusS,radiusB,hinv,Q.shiftedNativeModel_radius,
    ShiftedNativeBandModel.thermal] using H'

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
