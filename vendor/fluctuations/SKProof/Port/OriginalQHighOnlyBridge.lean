module

public import ComparisonActualHighWallThetaZeroStrongScaleGeometry
public import ComparisonActualHighWallThetaZeroSelectedOriginRateDraft
public import SKProof.OriginalQStrongContext
public import SKProof.OriginalQScalarLimitData

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal

namespace ActualHighWallData
variable {n : ℕ} {delta : ℝ} (a : ActualHighWallData n delta)
abbrev U : ℝ := comparisonSmallMass a.N a.E
abbrev L : ℝ := comparisonConstraintLength a.N a.E a.d
abbrev floor : ℝ := a.k 1
theorem k_eq_comparisonFloor : a.k = comparisonFloor a.N delta a.U := rfl
theorem M_eq_comparisonCap : a.M = comparisonCap a.N delta a.U a.L a.E a.d := rfl
theorem rmin_nonneg : 0 ≤ a.rmin := a.hrbounds.1.le
end ActualHighWallData

namespace ActualThetaZeroOverlapMinimum
section general
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
  (Q : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)

abbrev context := Q.data
abbrev b : ℝ → ℝ := Q.data.thetaZeroHighOnlyData.b
abbrev h : ℝ → ℝ := Q.data.thetaZeroHighOnlyData.h
theorem hb : MonotoneOn Q.b (Icc (0:ℝ) 1) := Q.data.thetaZeroHighOnlyData.hb
theorem hh : MonotoneOn Q.h (Icc (0:ℝ) 1) := Q.data.thetaZeroHighOnlyData.hh
theorem hb0 : 0 ≤ Q.b 0 := Q.data.thetaZeroHighOnlyData.hb0
theorem hh0 : 0 ≤ Q.h 0 := Q.data.thetaZeroHighOnlyData.hh0
theorem lam_mem : Q.lam ∈ Icc (0:ℝ) (Q.data.d^2) := ⟨Q.hlam.le, Q.hld⟩
theorem b_eq (u : ℝ) : Q.b u = wallBareMatrix Q.data.T Q.data.epsilon 0 Q.data.s u := rfl
theorem h_eq (u : ℝ) : Q.h u = 0 := rfl
theorem b_high {u : ℝ} (hu : Q.data.s ≤ u) : Q.b u = Q.data.T := by
  rw [b_eq]
  simp [wallBareMatrix, not_lt.mpr hu]
theorem bare_total_le : ∀ u ∈ Icc (0:ℝ) 1, Q.h u + Q.b u ≤ Q.data.T := by
  intro u _
  rw [h_eq, zero_add, b_eq]
  unfold wallBareMatrix
  split_ifs <;> linarith [Q.data.hepsilon.1]

theorem clocks_admissible :
    MonotoneOn (fun u => Q.b u - Q.sweepCoefficient u) (Icc (0:ℝ) 1) ∧
    MonotoneOn (fun u => Q.h u + Q.sweepCoefficient u * Q.sweepRadius u) (Icc (0:ℝ) 1) ∧
    (∀ u ∈ Icc (0:ℝ) 1, 0 ≤ Q.b u - Q.sweepCoefficient u) ∧
    (∀ u ∈ Icc (0:ℝ) 1, 0 ≤ Q.h u + Q.sweepCoefficient u * Q.sweepRadius u) :=
  (Q.data.thetaZeroShiftedParentData Q.lam Q.hlam Q.hld).clockAdmissible Q.alpha
theorem clock_coe {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    (Q.sweepBf u : ℝ) = Q.b u - Q.sweepCoefficient u ∧
    (Q.sweepHf u : ℝ) = Q.h u + Q.sweepCoefficient u * Q.sweepRadius u :=
  ⟨Real.coe_toNNReal _ (Q.clocks_admissible.2.2.1 u hu),
   Real.coe_toNNReal _ (Q.clocks_admissible.2.2.2 u hu)⟩
theorem high_clock_coe {u : ℝ} (hu : u ∈ Icc Q.data.s 1) :
    (Q.sweepBf u : ℝ) = Q.b u - laplaceComparisonStrength Q.data.d Q.lam (Q.sweepRadius u) ∧
    (Q.sweepHf u : ℝ) = Q.h u +
      laplaceComparisonStrength Q.data.d Q.lam (Q.sweepRadius u) * Q.sweepRadius u := by
  have H := Q.clock_coe ⟨Q.data.hs.1.le.trans hu.1, hu.2⟩
  simpa only [sweepCoefficient, omittedStrengthCoefficient, ite_eq_left hu.1] using H
theorem total_clock_le {T : ℝ} (htotal : ∀ u ∈ Icc (0:ℝ) 1, Q.h u + Q.b u ≤ T)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) : (Q.sweepHf u : ℝ) + (Q.sweepBf u : ℝ) ≤ T := by
  rw [(Q.clock_coe hu).1, (Q.clock_coe hu).2]
  have hR := (Q.data.theta_zero_radius_bounds Q.alpha u).2
  have he := (Q.data.theta_zero_coefficient_bounds Q.hlam Q.alpha u).1
  nlinarith [htotal u hu, mul_le_mul_of_nonneg_left hR he]
theorem clockBudget : (Q.sweepHf 1 : ℝ) - (Q.sweepHf 0 : ℝ) ≤ Bclock :=
  Q.field_clock_budget

theorem sweepRadius_bounds (u : ℝ) : Q.sweepRadius u ∈ Icc Q.data.rmin 1 :=
  omittedSweepQuantile_bounds Q.data.hr ⟨Q.data.hs.1.le, Q.data.hs1⟩ Q.data.hc Q.data.hk
    Q.data.hkc Q.data.hm Q.data.hM Q.alpha u
theorem sweepRadius_bounds0 (u : ℝ) : Q.sweepRadius u ∈ Icc (0:ℝ) 1 :=
  Q.data.theta_zero_radius_bounds Q.alpha u
theorem sweepRadius_monotone : Monotone Q.sweepRadius :=
  omittedSweepQuantile_monotone Q.data.hr ⟨Q.data.hs.1.le, Q.data.hs1⟩ Q.data.hc Q.data.hk
    Q.data.hkc Q.data.hm Q.data.hM Q.alpha
theorem sweepRadius_continuous : Continuous Q.sweepRadius :=
  omittedSweepQuantile_continuous Q.data.hr ⟨Q.data.hs.1.le, Q.data.hs1⟩ Q.data.hc Q.data.hk
    Q.data.hkc Q.data.hm Q.data.hM Q.alpha
theorem sweepRadius_lipschitz :
    LipschitzWith ⟨1/Q.data.k 1, div_nonneg zero_le_one Q.data.hc.le⟩ Q.sweepRadius :=
  omittedSweepQuantile_lipschitz Q.data.hr ⟨Q.data.hs.1.le, Q.data.hs1⟩ Q.data.hc Q.data.hk
    Q.data.hkc Q.data.hm Q.data.hM Q.alpha
theorem sweepRadius_spec {u : ℝ} (hu : u ∈ Icc Q.data.s 1) :
    Q.alpha.val.val (Q.sweepRadius u) = u :=
  omittedSweepQuantile_spec Q.data.hr ⟨Q.data.hs.1.le, Q.data.hs1⟩ Q.data.hc Q.data.hk
    Q.data.hkc Q.data.hm Q.data.hM Q.alpha hu
theorem sweepRadius_one : Q.sweepRadius 1 = 1 :=
  omittedSweepQuantile_one Q.data.hr ⟨Q.data.hs.1.le, Q.data.hs1⟩ Q.data.hc Q.data.hk
    Q.data.hkc Q.data.hm Q.data.hM Q.alpha
theorem sweepRadius_left : Q.sweepRadius Q.data.s = Q.data.rmin :=
  omittedSweepQuantile_left Q.data.hr ⟨Q.data.hs.1.le, Q.data.hs1⟩ Q.data.hc Q.data.hk
    Q.data.hkc Q.data.hm Q.data.hM Q.alpha
theorem sweepRadius_low {u : ℝ} (hu : u ≤ Q.data.s) : Q.sweepRadius u = Q.data.rmin :=
  Q.data.theta_zero_radius_low Q.alpha hu
theorem sweepRadius_inverse {r : ℝ} (hr : r ∈ Icc Q.data.rmin 1) :
    Q.sweepRadius (Q.alpha.val.val r) = r :=
  omittedSweepQuantile_inverse Q.data.hr ⟨Q.data.hs.1.le, Q.data.hs1⟩ Q.data.hc Q.data.hk
    Q.data.hkc Q.data.hm Q.data.hM Q.alpha hr

theorem R_bounds (u : ℝ) : Q.sweepRadius u ∈ Icc (0:ℝ) 1 := Q.sweepRadius_bounds0 u
theorem R_monotone : Monotone Q.sweepRadius := Q.sweepRadius_monotone
theorem R_one : Q.sweepRadius 1 = 1 := Q.sweepRadius_one
theorem R_zero : Q.sweepRadius 0 = Q.data.rmin :=
  Q.sweepRadius_low Q.data.hs.1.le
theorem radius_high_mass {u : ℝ} (hu : Q.data.rmin < Q.sweepRadius u) :
    Q.data.s < u := by
  by_contra H
  rw [Q.sweepRadius_low (le_of_not_gt H)] at hu
  exact lt_irrefl _ hu
theorem R_spec_high {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1)
    (hR : Q.data.rmin < Q.sweepRadius u) : Q.alpha.val.val (Q.sweepRadius u) = u :=
  Q.sweepRadius_spec ⟨(Q.radius_high_mass hR).le, hu.2⟩
theorem original_hf_radius_coe {u : ℝ} (hu : u ∈ Icc Q.data.s 1) :
    (Q.sweepHf u : ℝ) = Q.h u +
      laplaceComparisonStrength Q.data.d Q.lam (Q.sweepRadius u) * Q.sweepRadius u :=
  (Q.high_clock_coe hu).2
theorem hz0 : Q.z ∈ Icc (0:ℝ) 1 := ⟨Q.data.rmin_nonneg.trans Q.hz.1, Q.hz.2⟩
theorem rmin_le_U : Q.data.rmin ≤ Q.data.U := Q.data.theta_zero_radius_le_smallMass
theorem exists_potential_original_q (_hs : Q.data.s ≤ 1/4) : Nonempty Q.Potential :=
  Q.exists_potential
end general

section succ
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
  (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
def inheritedScalarMassProfileBare {T : ℝ} (hT : 0 < T)
    (htotal : ∀ u ∈ Icc (0:ℝ) 1, Q.h u + Q.b u ≤ T) : boundedMassProfiles :=
  actualMixedMassProfile hT (n+1) Q.data.hn Q.sweepBf Q.sweepHf
    Q.sweep_bf_monotone Q.sweep_hf_monotone (fun _ hu => Q.total_clock_le htotal hu)
theorem inheritedScalarMassProfileBare_eq {T : ℝ} (hT : 0 < T)
    (htotal : ∀ u ∈ Icc (0:ℝ) 1, Q.h u + Q.b u ≤ T)
    (h' : ∀ u ∈ Icc (0:ℝ) 1, (Q.sweepHf u : ℝ) + (Q.sweepBf u : ℝ) ≤ T) :
    Q.inheritedScalarMassProfileBare hT htotal = Q.inheritedScalarMassProfile hT h' := rfl
theorem actualRadiusMassProfile_eq :
    Q.actualRadiusMassProfile =
      quantileMassProfile Q.sweepRadius (fun u _ => Q.sweepRadius_bounds0 u) := rfl
theorem shiftedNativeModel_R_bounds0 (u : ℝ) :
    Q.shiftedNativeModel.R u ∈ Icc (0:ℝ) 1 := Q.sweepRadius_bounds0 u
end succ

theorem eventually_rmin_lt_xs_original_q {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) : ∀ᶠ n : ℕ in atTop,
      ∀ Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        Q.data.rmin < Q.xs := by
  have Hpow : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)^(-(3*m)))
      atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (show 0 < 3*m by positivity)).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have Hlim : Tendsto (fun n : ℕ => C0^3 * ((n+1 : ℕ) : ℝ)^(-(3*m)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using Hpow.const_mul (C0^3)
  filter_upwards [Hlim.eventually (eventually_lt_nhds zero_lt_one)] with n hn
  intro Q
  have Hbound : C0^3 * Q.data.N^(-3*m) < 1 := by
    simpa only [ActualHighWallData.N, neg_mul] using hn
  exact Q.radius_le_smallMass.trans_lt
    ((div_lt_one Q.hxs).mp ((Q.small_mass_ratio hC0).trans_lt Hbound))

variable {dim : ℕ → ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}
def OriginalQSequentialComparableBandClocks
    (Q : (n:ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ℝ) : Prop :=
  ∀ y : ℕ → ℝ, Tendsto y atTop (𝓝 0) →
    (∀ᶠ n in atTop, comparisonLowerScale (Q n).data.N (Q n).data.E (Q n).data.d ≤ y n) →
    ∀ c C epsilon : ℝ, 0 < c → 0 ≤ C → 0 < epsilon → ∀ᶠ n in atTop,
      ∀ u ∈ Icc (c * y n) (min (C * y n) 1),
        |(Q n).b u - T| ≤ epsilon * (y n)^2 ∧ |(Q n).h u| ≤ epsilon * (y n)^3

namespace OriginalQComparableBandContext
variable {Q : (n:ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}

theorem pullback_eventually_original_q (G : OriginalQComparableBandContext Q T) :
    ∀ᶠ n in atTop, NativePullbackClockRegularity (Q n).alpha.val.val (Q n).b (Q n).h
      (Q n).data.rmin 1 := Eventually.of_forall G.pullback_original_q
theorem total_root_bare_original_q (G : OriginalQComparableBandContext Q T) :
    ∀ᶠ n in atTop, (∀ u ∈ Icc (0:ℝ) 1, (Q n).h u + (Q n).b u ≤ T) ∧ (Q n).h 0 = 0 :=
  Eventually.of_forall fun n =>
    ⟨fun u hu => ((Q n).bare_total_le u hu).trans_eq (G.hTeq n), rfl⟩
def Cf (_G : OriginalQComparableBandContext Q T) : ℝ := D^2 * (Az + |1/cl|)
theorem hCf_original_q (G : OriginalQComparableBandContext Q T) : 0 ≤ G.Cf := by
  have H : 0 ≤ Az * (Q 0).xs :=
    (Q 0).data.rmin_nonneg.trans ((Q 0).hz.1.trans (Q 0).hzxs)
  have hAz : 0 ≤ Az := by nlinarith only [H, (Q 0).hxs]
  exact mul_nonneg (sq_nonneg D) (add_nonneg hAz (abs_nonneg _))
theorem source_eventually_original_q (G : OriginalQComparableBandContext Q T) (hcl : 0 < cl) :
    ∀ᶠ n in atTop, ∀ u ∈ Icc (0:ℝ) 1,
      ((Q n).sweepBf u : ℝ) ≤ T ∧ ((Q n).sweepHf u : ℝ) ≤ G.Cf * ((Q n).xs + u) := by
  have hAz : 0 ≤ Az := by
    have H : 0 ≤ Az * (Q 0).xs :=
      (Q 0).data.rmin_nonneg.trans ((Q 0).hz.1.trans (Q 0).hzxs)
    nlinarith only [H, (Q 0).hxs]
  have hC : 0 ≤ Az + 1/cl := add_nonneg hAz (one_div_pos.mpr hcl).le
  refine Eventually.of_forall fun n u hu => ?_
  have htotal := (G.total_root_original_q n u hu).1
  have hfield := (Q n).sweep_field_small_source hcl hAz hu
  have hlam : (Q n).lam ≤ D^2 :=
    (Q n).hld.trans (pow_le_pow_left₀ (Q n).data.hd.le (Q n).hdD 2)
  refine ⟨?_, hfield.trans ?_⟩
  · linarith only [htotal, ((Q n).sweepHf u).coe_nonneg]
  · have H : (Q n).lam * (Az + 1/cl) ≤ D^2 * (Az + |1/cl|) :=
      (mul_le_mul_of_nonneg_right hlam hC).trans
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl (le_abs_self (1/cl)))
          (sq_nonneg D))
    exact mul_le_mul_of_nonneg_right H (add_nonneg (Q n).hxs.le hu.1)
theorem comparable_original_q (G : OriginalQComparableBandContext Q T) :
    OriginalQSequentialComparableBandClocks Q T := by
  intro y _hy hay c C epsilon hc _hC heps
  have hlow : ∀ n, 0 < comparisonLowerScale (Q n).data.N (Q n).data.E (Q n).data.d :=
    fun n => div_pos (mul_pos (Real.sqrt_pos.mpr (Q n).data.hN) (Q n).data.hE) (Q n).data.hd
  filter_upwards [G.omission_ratio.eventually (eventually_le_nhds hc), hay] with n hn hyn u hu
  have hsu : (Q n).data.s ≤ u :=
    ((div_le_iff₀ (hlow n)).mp hn).trans (by nlinarith [hu.1, (hlow n).le])
  have hy0 : 0 ≤ y n := (hlow n).le.trans hyn
  rw [(Q n).b_high hsu, G.hTeq n, sub_self, abs_zero, (Q n).h_eq, abs_zero]
  exact ⟨by positivity, by positivity⟩
theorem positive_band_clocks_original_q (G : OriginalQComparableBandContext Q T)
    (c C epsilon : ℝ) (hc : 0 < c) (hC : 0 ≤ C) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ u ∈ Icc (c*(Q n).xs) (min (C*(Q n).xs) 1),
      |(Q n).b u - T| ≤ epsilon*(Q n).xs^2 ∧ |(Q n).h u| ≤ epsilon*(Q n).xs^3 :=
  G.comparable_original_q _ G.xs_zero (Eventually.of_forall fun n => (Q n).hscale)
    c C epsilon hc hC hepsilon
theorem initial_field_clock_original_q (G : OriginalQComparableBandContext Q T)
    (C epsilon : ℝ) (hC : 0 < C) (hepsilon : 0 < epsilon) :
    ∀ᶠ n in atTop, ∀ u ∈ Icc (0:ℝ) (C*(Q n).xs), |(Q n).h u| ≤ epsilon*(Q n).xs^3 := by
  filter_upwards [G.positive_bands_high_original_q C hC] with n _hn u _hu
  rw [(Q n).h_eq, abs_zero]
  exact mul_nonneg hepsilon.le (pow_nonneg (Q n).hxs.le 3)
end OriginalQComparableBandContext
end ActualThetaZeroOverlapMinimum

theorem eventually_actual_overlap_moment_normalized_original_q
    (ell : ℕ) (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
      ∀ a : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      a.data.s ≤ 1/4 → a.data.s ≤ a.xs → ∀ u ∈ Ioc (0:ℝ) 1,
        pathPairMoment (uniformWeight n) (finiteFeature n)
          (completedPathClock n a.sweepBf a.sweepHf)
          (fun sigma tau => |orderedOverlap n sigma tau|^(2*(ell+1))) u ≤
          K*(a.xs+u)^(2*(ell+1)) := by
  obtain ⟨K, hK, H⟩ := eventually_actual_theta_zero_selected_overlap_moment_normalized
    (D:=D) ell Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp H
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_ge_atTop (N0+1)] with n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
  intro a _ _ u hu
  exact hN0 k (by omega) a u hu
theorem eventually_actual_B_normalized_original_q
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
      ∀ a : ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      a.data.s ≤ 1/4 → a.data.s ≤ a.xs → ∀ u ∈ Ioc (0:ℝ) 1,
        orderedPathB n a.sweepBf a.sweepHf u ≤ K*(a.xs+u)^2 := by
  obtain ⟨K, hK, H⟩ := eventually_actual_theta_zero_selected_B_normalized
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp H
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_ge_atTop (N0+1)] with n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
  intro a _ _ u hu
  exact hN0 k (by omega) a u hu
end OAI.SKFluctuations.LaplaceWindowFormalization
