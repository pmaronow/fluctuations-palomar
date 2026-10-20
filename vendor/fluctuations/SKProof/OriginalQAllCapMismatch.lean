module

public import ComparisonActualHighWallThetaZeroStarMismatch

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock}

private theorem cavityCapTravel_nonneg_original_q : 0 ≤ Q.cavityCapTravel := by
  unfold cavityCapTravel
  exact mul_nonneg
    (div_nonneg Q.data.hL.le (Real.rpow_nonneg Q.data.hN.le delta))
    (Real.log_nonneg ((le_div_iff₀ Q.data.hU).mpr (by linarith)))

theorem Potential.all_nonpositive_squared_mismatch_ae_original_q
    (P : Q.Potential) :
    ∀ᵐ r, r ∈ Icc Q.data.rmin 1 → P.H r ≤ 0 →
      (Q.radiusS r-r)^2 ≤ 16*(Q.data.rmin+Q.cavityCapTravel)^2 +
        2*(Q.radiusB r-(Q.radiusS r)^2) := by
  have htravel : 0 ≤ Q.cavityCapTravel := cavityCapTravel_nonneg_original_q
  have horigin : 0 ≤ Q.data.rmin := Q.data.hrbounds.1.le
  have hcharge : Q.cavityCapTravel^2 ≤
      (Q.data.rmin+Q.cavityCapTravel)^2 :=
    pow_le_pow_left₀ htravel (le_add_of_nonneg_left horigin) 2
  filter_upwards [P.hzero, volume.ae_ne Q.data.rmin,
    volume.ae_ne (1:ℝ)] with r hrzero hr0 hr1 hri hnonpos
  have hro : r ∈ Ioo Q.data.rmin 1 :=
    ⟨lt_of_le_of_ne hri.1 hr0.symm, lt_of_le_of_ne hri.2 hr1⟩
  have hthermal : 0 ≤ Q.radiusB r-(Q.radiusS r)^2 :=
    sub_nonneg.mpr (Q.radius_moments.2.2 r hri).2.1
  rcases hnonpos.eq_or_lt with hz | hneg
  · have H : (Q.radiusS r-r)^2 ≤ Q.radiusB r-(Q.radiusS r)^2 :=
      (hrzero hri hz).2.2
    nlinarith only [H, hthermal, sq_nonneg (Q.data.rmin+Q.cavityCapTravel)]
  · rcases P.star_negative_point_squared_mismatch_split hro hneg with H | H
    · nlinarith only [H, hthermal, sq_nonneg (Q.data.rmin+Q.cavityCapTravel)]
    · nlinarith only [H, hcharge]

theorem Potential.all_nonpositive_squared_mismatch_ae_high_mass_original_q
    (P : Q.Potential) :
    ∀ᵐ u, u ∈ Icc Q.data.s 1 → P.H (Q.sweepRadius u) ≤ 0 →
      (orderedPathS (n+1) Q.sweepBf Q.sweepHf u-Q.sweepRadius u)^2 ≤
        16*(Q.data.rmin+Q.cavityCapTravel)^2 +
        2*(orderedPathB (n+1) Q.sweepBf Q.sweepHf u-
          (orderedPathS (n+1) Q.sweepBf Q.sweepHf u)^2) := by
  have H := ae_inverse_pullback
    (inverseIntegralConstraints_lipschitz Q.data.hm Q.data.hM Q.alpha.property)
    (fun u (_ : u ∈ Icc Q.data.s 1) => omittedSweepQuantile_bounds Q.data.hr
      ⟨Q.data.hs.1.le, Q.data.hs1⟩ Q.data.hc Q.data.hk Q.data.hkc
      Q.data.hm Q.data.hM Q.alpha u)
    (fun u hu => omittedSweepQuantile_spec Q.data.hr
      ⟨Q.data.hs.1.le, Q.data.hs1⟩ Q.data.hc Q.data.hk Q.data.hkc
      Q.data.hm Q.data.hM Q.alpha hu)
    P.all_nonpositive_squared_mismatch_ae_original_q
  filter_upwards [H] with u hu hui hnonpos
  have HH := hu hui hnonpos
  simpa only [radiusS, radiusB, sweepRadius, omittedSweepQuantile_spec Q.data.hr
    ⟨Q.data.hs.1.le, Q.data.hs1⟩ Q.data.hc Q.data.hk Q.data.hkc
    Q.data.hm Q.data.hM Q.alpha hui] using HH

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
