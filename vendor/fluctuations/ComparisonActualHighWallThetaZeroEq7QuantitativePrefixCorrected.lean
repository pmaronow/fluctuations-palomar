module

public import ComparisonActualHighWallThetaZeroEq7FiniteMaskGeometry
public import ComparisonActualHighWallThetaZeroNearZeroPoint
public import ComparisonConditionalErrorSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eventually_theta_zero_eq7_unified_prefix_quantitative_corrected_draft
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Kprefix : ℝ, 0 < Kprefix ∧ ∀ᶠ n : ℕ in atTop,
      ∀ Q : ActualThetaZeroOverlapMinimum
          (n+1) m delta cl cu Az C0 Ct D Bclock,
        Q.xs = comparisonConditionalScale Q.data.N delta Q.data.E Q.lam →
        comparisonSmallMass Q.data.N Q.data.E ≤ Q.xs →
        (∫u in (0:ℝ)..Q.eq7InnerPrefixEnd,
          Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
          Kprefix*Q.data.N^(2*delta)*Q.data.E := by
  obtain ⟨Kraw,hKraw,Hpoint⟩ := eventually_theta_zero_near_zero_point
    (D:=D) (Bclock:=Bclock) hm hdelta hroom hcl hcu hAz hC0 hCt
  let C := Az+1/cl
  let Kprefix := 16224*(Kraw+C^2)
  have hKsum : 0 ≤ Kraw+C^2 := add_nonneg hKraw.le (sq_nonneg C)
  have hKprefix : 0 < Kprefix := by
    dsimp only [Kprefix]
    exact mul_pos (by norm_num) (add_pos_of_pos_of_nonneg hKraw (sq_nonneg C))
  refine ⟨Kprefix,hKprefix,?_⟩
  filter_upwards [Hpoint] with n hnPoint
  intro Q hcarrier hUA
  let U := comparisonSmallMass Q.data.N Q.data.E
  let z := Q.eq7InnerPrefixEnd
  have hzS : Q.data.s ≤ z := Q.eq7_inner_s_le_prefix_end
  have hz1 : z ≤ 1 := Q.eq7_inner_prefix_end_le_one
  have hz24 : z ≤ Q.data.s+24*U := by
    by_cases hsU : Q.data.s < U
    · have hmin : z ≤ 24*U := by
        dsimp only [z,eq7InnerPrefixEnd]
        rw [ite_eq_left (show Q.data.s < comparisonSmallMass Q.data.N Q.data.E from hsU)]
        exact min_le_left _ _
      linarith only [hmin,Q.data.hs.1]
    · have hmin : z ≤ Q.data.s+2*U := by
        dsimp only [z,eq7InnerPrefixEnd]
        rw [ite_eq_right (show ¬Q.data.s < comparisonSmallMass Q.data.N Q.data.E from hsU)]
        exact min_le_left _ _
      have hUpos : 0 < U := Q.data.hU
      linarith only [hmin,hUpos]
  have hiz := Q.error_intervalIntegrable.mono_set (by
    rw [uIcc_of_le hzS,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc Q.data.hs.1.le hz1)
  have Hpoint' : ∀ᵐu ∂volume.restrict (Icc Q.data.s z),
      Q.data.thetaZeroErrorDensity Q.lam Q.alpha u ≤
        Q.lam*(Kraw+C^2)*(26*Q.xs)^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hu0 : u ∈ Ioc (0:ℝ) 1 :=
      ⟨Q.data.hs.1.trans_le hu.1,hu.2.trans hz1⟩
    have HB := hnPoint Q u hu0
    have hupper : Q.xs+u ≤ 26*Q.xs := by
      nlinarith only [hu.2,hz24,Q.hsxs,hUA]
    have hsq : (Q.xs+u)^2 ≤ (26*Q.xs)^2 :=
      pow_le_pow_left₀
        (add_nonneg Q.hxs.le (Q.data.hs.1.le.trans hu.1)) hupper 2
    have H := mul_le_mul_of_nonneg_left hsq
      (mul_nonneg Q.hlam.le hKsum)
    dsimp only [C] at HB H ⊢
    exact HB.trans H
  have H := intervalIntegral.integral_mono_ae_restrict hzS hiz
    intervalIntegrable_const Hpoint'
  rw [intervalIntegral.integral_const] at H
  simp only [smul_eq_mul] at H
  have hwidth : z-Q.data.s ≤ 24*U := by linarith only [hz24]
  have Hwidth := mul_le_mul_of_nonneg_right hwidth
    (mul_nonneg (mul_nonneg Q.hlam.le hKsum) (sq_nonneg (26*Q.xs)))
  have Hbound : (∫u in Q.data.s..z,
      Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      Kprefix*(Q.lam*Q.xs^2*U) := by
    dsimp only [Kprefix]
    nlinarith only [H,Hwidth]
  have hcal : Q.lam*Q.xs^2*U =
      Q.data.N^(2*delta)*Q.data.E := by
    rw [hcarrier]
    exact comparison_conditional_small_mass_cost Q.data.hN Q.data.hE Q.hlam
  have hi0 := Q.error_intervalIntegrable.mono_set (by
    rw [uIcc_of_le Q.data.hs.1.le,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl Q.data.hs1)
  have Hadd := intervalIntegral.integral_add_adjacent_intervals hi0 hiz
  have hpref : (∫u in (0:ℝ)..z,
      Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) =
      ∫u in Q.data.s..z,
        Q.data.thetaZeroErrorDensity Q.lam Q.alpha u := by
    rw [←Hadd,Q.data.theta_zero_error_low_prefix_zero Q.lam Q.alpha,
      zero_add]
  rw [hpref]
  rw [hcal] at Hbound
  simpa only [mul_assoc] using Hbound

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
