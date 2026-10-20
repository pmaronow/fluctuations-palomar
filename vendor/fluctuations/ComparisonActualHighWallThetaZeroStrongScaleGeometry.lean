module

public import ComparisonActualHighWallThetaZeroRadiusRegularity
public import ComparisonActualHighWallThetaZeroBroadCutoffRate

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 16000000

 theorem laplace_variable_strength_shell_lower
    {d lam C r : ℝ} (hd : 0 < d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (hC : 0 < C) (hr : 0 < r) (hrC : r ≤ C*Real.sqrt lam) :
    min 1 (1/C)*lam ≤ laplaceComparisonStrength d lam r := by
  have hS : 0 < Real.sqrt lam:=Real.sqrt_pos.mpr hlam
  have hSd : Real.sqrt lam ≤ d:=by
    have H:=Real.sqrt_le_sqrt hld
    simpa only [Real.sqrt_sq_eq_abs,abs_of_pos hd] using H
  have Hcube : lam*Real.sqrt lam ≤ d^3:=by
    have H:=pow_le_pow_left₀ hS.le hSd 3
    have HE : lam*Real.sqrt lam=(Real.sqrt lam)^3:=by
      rw [pow_succ,Real.sq_sqrt hlam.le]
    rwa [←HE] at H
  have Harg : lam*r ≤ C*d^3:=by
    have H1:=mul_le_mul_of_nonneg_left hrC hlam.le
    have H2:=mul_le_mul_of_nonneg_left Hcube hC.le
    nlinarith only [H1,H2]
  have Hquot : lam/C ≤ d^3/r:=by
    apply (div_le_div_iff₀ hC hr).mpr
    nlinarith only [Harg]
  calc
    min 1 (1/C)*lam=min lam (lam/C):=by
      rw [min_mul_of_nonneg _ _ hlam.le]
      simp only [one_mul]
      congr 1
      ring
    _ ≤ min lam (d^3/r):=min_le_min le_rfl Hquot
    _ ≤ laplaceComparisonStrength d lam r:=laplaceComparisonStrength_lower hd hlam hr

 theorem laplace_variable_strength_at_sqrt_eq
    {d lam : ℝ} (hd : 0 < d) (hlam : 0 < lam) (hld : lam ≤ d^2) :
    laplaceComparisonStrength d lam (Real.sqrt lam)=lam := by
  apply le_antisymm (laplaceComparisonStrength_le d hlam.le _)
  have H:=laplace_variable_strength_shell_lower hd hlam hld
    (by norm_num : (0:ℝ)<1) (Real.sqrt_pos.mpr hlam)
    (by simp : Real.sqrt lam ≤ (1:ℝ)*Real.sqrt lam)
  simpa only [one_div_one,min_self,one_mul] using H

 theorem laplace_variable_strength_above_sqrt
    {d lam r : ℝ} (hd : 0 < d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (hr : Real.sqrt lam ≤ r) (hr1 : r ≤ 1) :
    (Real.sqrt lam)^3 ≤ laplaceComparisonStrength d lam r*r := by
  have hS : 0 < Real.sqrt lam:=Real.sqrt_pos.mpr hlam
  have H:=(laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀:=0) le_rfl).2
    ⟨hS.le,hr.trans hr1⟩ ⟨hS.le.trans hr,hr1⟩ hr
  dsimp only at H
  rw [laplace_variable_strength_at_sqrt_eq hd hlam hld] at H
  have HE : lam*Real.sqrt lam=(Real.sqrt lam)^3:=by
    rw [pow_succ,Real.sq_sqrt hlam.le]
  simpa only [HE] using H

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
  (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

def naturalStrengthScale : ℝ:=Real.sqrt Q.lam

def directTestWorkingScale : ℝ:=
  max Q.xs (Real.sqrt (laplaceComparisonStrength Q.data.d Q.lam Q.xs))

theorem natural_strength_scale_pos : 0 < Q.naturalStrengthScale:=Real.sqrt_pos.mpr Q.hlam

theorem natural_strength_scale_sq : Q.naturalStrengthScale^2=Q.lam:=Real.sq_sqrt Q.hlam.le

theorem natural_strength_scale_le_original_taper : Q.naturalStrengthScale ≤ Q.data.d:=by
  have H:=Real.sqrt_le_sqrt Q.hld
  simpa only [naturalStrengthScale,Real.sqrt_sq_eq_abs,abs_of_pos Q.data.hd] using H

theorem direct_test_working_scale_pos : 0 < Q.directTestWorkingScale:=
  Q.hxs.trans_le (le_max_left _ _)

theorem target_le_direct_test_working_scale : Q.xs ≤ Q.directTestWorkingScale:=le_max_left _ _

theorem strong_direct_test_working_geometry {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hstrong : Q.xs^2 ≤ Cs*laplaceComparisonStrength Q.data.d Q.lam Q.xs) :
    Q.xs ≤ (Cs+1)*Q.naturalStrengthScale ∧
    Q.directTestWorkingScale ≤ (Cs+1)*Q.naturalStrengthScale ∧
    Q.directTestWorkingScale^2 ≤ (Cs+1)*Q.lam := by
  have Hg : 0 ≤ laplaceComparisonStrength Q.data.d Q.lam Q.xs:=
    (laplaceComparisonStrength_pos _ Q.hlam _).le
  have HgLam:=laplaceComparisonStrength_le Q.data.d Q.hlam.le Q.xs
  have HxLam:=hstrong.trans (mul_le_mul_of_nonneg_left HgLam hCs)
  have hS:=Q.natural_strength_scale_pos
  have HS:=Q.natural_strength_scale_sq
  have hK : 0 ≤ Cs+1:=by linarith
  have HX : Q.xs ≤ (Cs+1)*Q.naturalStrengthScale:=by
    have Hcoef : Cs ≤ (Cs+1)^2:=by nlinarith
    have HH:=mul_le_mul_of_nonneg_right Hcoef Q.hlam.le
    have Hbound : Q.xs^2 ≤ ((Cs+1)*Q.naturalStrengthScale)^2:=by
      rw [mul_pow,HS]
      exact HxLam.trans HH
    have HY : 0 ≤ (Cs+1)*Q.naturalStrengthScale:=mul_nonneg hK hS.le
    nlinarith only [Hbound,HY,Q.hxs]
  have Hsqrt : Real.sqrt (laplaceComparisonStrength Q.data.d Q.lam Q.xs) ≤
      Q.naturalStrengthScale:=Real.sqrt_le_sqrt HgLam
  refine ⟨HX,max_le HX (Hsqrt.trans (by nlinarith [mul_nonneg hCs hS.le])),?_⟩
  unfold directTestWorkingScale
  rcases le_total Q.xs (Real.sqrt (laplaceComparisonStrength Q.data.d Q.lam Q.xs)) with H|H
  · rw [max_eq_right H,Real.sq_sqrt Hg]
    nlinarith only [HgLam,Q.hlam,mul_nonneg hCs Q.hlam.le]
  · rw [max_eq_left H]
    nlinarith only [HxLam,Q.hlam]

theorem strong_working_strength_comparability {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hstrong : Q.xs^2 ≤ Cs*laplaceComparisonStrength Q.data.d Q.lam Q.xs) :
    Q.lam ≤ (Cs+1)*Q.directTestWorkingScale^2 := by
  have Hgeometry:=Q.strong_direct_test_working_geometry hCs hstrong
  have hK : 0 < Cs+1:=by linarith
  have hInv : 1/(Cs+1) ≤ 1:=by
    apply (div_le_one hK).mpr
    linarith
  have Hlower:=laplace_variable_strength_shell_lower Q.data.hd Q.hlam Q.hld hK Q.hxs Hgeometry.1
  rw [min_eq_right hInv] at Hlower
  have H:=mul_le_mul_of_nonneg_left Hlower hK.le
  have HE : (Cs+1)*(1/(Cs+1)*Q.lam)=Q.lam:=by field_simp [hK.ne']
  rw [HE] at H
  have Hg : 0 ≤ laplaceComparisonStrength Q.data.d Q.lam Q.xs:=
    (laplaceComparisonStrength_pos _ Q.hlam _).le
  have Hsqrt : Real.sqrt (laplaceComparisonStrength Q.data.d Q.lam Q.xs) ≤ Q.directTestWorkingScale:=
    le_max_right _ _
  have Hsq:=pow_le_pow_left₀ (Real.sqrt_nonneg _) Hsqrt 2
  rw [Real.sq_sqrt Hg] at Hsq
  exact H.trans (mul_le_mul_of_nonneg_left Hsq hK.le)

theorem strong_ratio_direct_test_working_geometry {eta : ℝ} (heta : 0 < eta)
    (hstrong : eta ≤ laplaceComparisonStrength Q.data.d Q.lam Q.xs/Q.xs^2) :
    Q.xs ≤ (1/eta+1)*Q.naturalStrengthScale ∧
    Q.directTestWorkingScale ≤ (1/eta+1)*Q.naturalStrengthScale ∧
    Q.directTestWorkingScale^2 ≤ (1/eta+1)*Q.lam := by
  have H:=(le_div_iff₀ (sq_pos_of_pos Q.hxs)).mp hstrong
  have H' : Q.xs^2 ≤ laplaceComparisonStrength Q.data.d Q.lam Q.xs/eta:=by
    apply (le_div_iff₀ heta).mpr
    nlinarith only [H]
  have H'' : Q.xs^2 ≤ (1/eta)*laplaceComparisonStrength Q.data.d Q.lam Q.xs:=by
    convert H' using 1
    ring
  exact Q.strong_direct_test_working_geometry (one_div_pos.mpr heta).le H''

theorem sweep_clock_coe {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    (Q.sweepBf u:ℝ)=Q.data.thetaZeroHighOnlyData.b u-Q.sweepCoefficient u ∧
    (Q.sweepHf u:ℝ)=Q.data.thetaZeroHighOnlyData.h u+Q.sweepCoefficient u*Q.sweepRadius u := by
  have H:=(Q.data.thetaZeroShiftedParentData Q.lam Q.hlam Q.hld).clockAdmissible Q.alpha
  exact ⟨Real.coe_toNNReal _ (H.2.2.1 u hu),Real.coe_toNNReal _ (H.2.2.2 u hu)⟩

theorem sweep_root_field_zero : Q.sweepHf 0=0:=by
  have H : Q.sweepCoefficient 0=0:=by
    simp only [sweepCoefficient,omittedStrengthCoefficient,ite_eq_right (not_le.mpr Q.data.hs.1)]
  change (Q.data.thetaZeroHighOnlyData.h 0+Q.sweepCoefficient 0*Q.sweepRadius 0).toNNReal=0
  rw [H]
  simp only [ActualHighWallData.thetaZeroHighOnlyData,zero_mul,zero_add,Real.toNNReal_zero]

theorem sweep_total_clock_le :
    ∀u∈Icc (0:ℝ) 1,(Q.sweepHf u:ℝ)+(Q.sweepBf u:ℝ) ≤ Q.data.T := by
  intro u hu
  rw [(Q.sweep_clock_coe hu).1,(Q.sweep_clock_coe hu).2]
  have hR:=Q.data.theta_zero_radius_bounds Q.alpha u
  have he:=Q.data.theta_zero_coefficient_bounds Q.hlam Q.alpha u
  change 0+Q.sweepCoefficient u*Q.sweepRadius u+
    (wallBareMatrix Q.data.T Q.data.epsilon 0 Q.data.s u-Q.sweepCoefficient u) ≤ Q.data.T
  simp only [wallBareMatrix,zero_mul,sub_zero,zero_add]
  split_ifs <;> nlinarith only [he.1,he.2,hR.1,hR.2,Q.data.hepsilon.1,
    mul_le_mul_of_nonneg_left hR.2 he.1]

theorem sweep_field_small_source (hcl : 0 < cl) (hAz : 0 ≤ Az)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    (Q.sweepHf u:ℝ) ≤ Q.lam*(Az+1/cl)*(Q.xs+u) := by
  rw [(Q.sweep_clock_coe hu).2]
  change 0+Q.sweepCoefficient u*Q.sweepRadius u ≤ _
  rw [zero_add]
  have he:=Q.data.theta_zero_coefficient_bounds Q.hlam Q.alpha u
  have hR:=Q.data.theta_zero_radius_bounds Q.alpha u
  have HR:=Q.inverse_radius_le_source_mass hcl hAz hu
  have H:=mul_le_mul he.2 HR hR.1 Q.hlam.le
  nlinarith only [H]

theorem sweep_high_clock_comparison_identity {u : ℝ} (hu : u∈Icc Q.data.s 1) :
    actualMixedClock (n+1) Q.sweepBf Q.sweepHf u-
      Q.data.T*orderedPathS (n+1) Q.sweepBf Q.sweepHf u=
      Q.sweepCoefficient u*(Q.sweepRadius u-orderedPathS (n+1) Q.sweepBf Q.sweepHf u) := by
  have hu0 : u∈Icc (0:ℝ) 1:=⟨Q.data.hs.1.le.trans hu.1,hu.2⟩
  dsimp only [actualMixedClock]
  rw [(Q.sweep_clock_coe hu0).1,(Q.sweep_clock_coe hu0).2]
  change 0+Q.sweepCoefficient u*Q.sweepRadius u+
    (wallBareMatrix Q.data.T Q.data.epsilon 0 Q.data.s u-Q.sweepCoefficient u)*
      orderedPathS (n+1) Q.sweepBf Q.sweepHf u-Q.data.T*
        orderedPathS (n+1) Q.sweepBf Q.sweepHf u=_
  simp only [wallBareMatrix,if_neg (not_lt.mpr hu.1),zero_mul,sub_zero,zero_add]
  ring

theorem sweep_high_clock_comparison_abs_le {u : ℝ} (hu : u∈Icc Q.data.s 1) :
    |actualMixedClock (n+1) Q.sweepBf Q.sweepHf u-
      Q.data.T*orderedPathS (n+1) Q.sweepBf Q.sweepHf u| ≤
      Q.lam*|Q.sweepRadius u-orderedPathS (n+1) Q.sweepBf Q.sweepHf u| := by
  rw [Q.sweep_high_clock_comparison_identity hu,abs_mul]
  have H:=Q.data.theta_zero_coefficient_bounds Q.hlam Q.alpha u
  rw [abs_of_nonneg H.1]
  exact mul_le_mul_of_nonneg_right H.2 (abs_nonneg _)

theorem working_mass_inverse_power (hC0 : 0 < C0) (k : ℕ) :
    1/(Q.data.N^((k:ℝ)/6)*Q.directTestWorkingScale^k) ≤
      C0^k*Q.data.N^(-(k:ℝ)*m) := by
  exact mass_critical_inverse_power Q.data.hN Q.direct_test_working_scale_pos hC0
    ((Q.high_mass_scale_critical_lower hC0).trans Q.target_le_direct_test_working_scale) k

theorem working_site_fourth_normalized (hC0 : 0 < C0) :
    (1/Q.data.N)/Q.directTestWorkingScale^4 ≤
      C0^4*Q.data.N^(-(1:ℝ)/3-4*m) := by
  have hN:=Q.data.hN
  have hW:=Q.direct_test_working_scale_pos
  have H:=Q.working_mass_inverse_power hC0 4
  have H' : 1/(Q.data.N^((2:ℝ)/3)*Q.directTestWorkingScale^4) ≤
      C0^4*Q.data.N^(-4*m):=by
    simpa only [Nat.cast_ofNat,show (4:ℝ)/6=2/3 by norm_num,
      show -(4:ℝ)*m=-4*m by ring] using H
  have HP : Q.data.N^(-(1:ℝ)/3)*Q.data.N=Q.data.N^((2:ℝ)/3):=by
    calc
      _=Q.data.N^(-(1:ℝ)/3)*Q.data.N^(1:ℝ):=by rw [Real.rpow_one]
      _=Q.data.N^(-(1:ℝ)/3+1):=(Real.rpow_add hN _ _).symm
      _=_:=by congr 1;norm_num
  have HE : (1/Q.data.N)/Q.directTestWorkingScale^4=
      Q.data.N^(-(1:ℝ)/3)*(1/(Q.data.N^((2:ℝ)/3)*Q.directTestWorkingScale^4)):=by
    rw [←HP]
    field_simp [hN.ne',hW.ne',(Real.rpow_pos_of_pos hN (-(1:ℝ)/3)).ne']
  have Hscaled:=mul_le_mul_of_nonneg_left H' (Real.rpow_nonneg hN.le (-(1:ℝ)/3))
  rw [HE]
  apply Hscaled.trans_eq
  rw [mul_left_comm,←Real.rpow_add hN]
  congr 2
  ring

theorem omitted_ratio_le_target_ratio :
    Q.data.s/Q.directTestWorkingScale ≤ Q.data.s/Q.xs :=
  div_le_div_of_nonneg_left Q.data.hs.1.le Q.hxs Q.target_le_direct_test_working_scale

end ActualThetaZeroOverlapMinimum
theorem actual_theta_zero_natural_strength_scale_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (dim : ℕ→ℕ)
    (Q : (n : ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hdlim : Tendsto (fun n=>(Q n).data.d) atTop (𝓝 0)) :
    Tendsto (fun n=>(Q n).naturalStrengthScale) atTop (𝓝 0) := by
  exact squeeze_zero' (Eventually.of_forall (fun n=>(Q n).natural_strength_scale_pos.le))
    (Eventually.of_forall (fun n=>(Q n).natural_strength_scale_le_original_taper)) hdlim

theorem actual_theta_zero_strong_working_scale_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Cs : ℝ}
    (dim : ℕ→ℕ)
    (Q : (n : ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCs : 0 ≤ Cs)
    (hstrong : ∀n,(Q n).xs^2 ≤ Cs*laplaceComparisonStrength (Q n).data.d (Q n).lam (Q n).xs)
    (hdlim : Tendsto (fun n=>(Q n).data.d) atTop (𝓝 0)) :
    Tendsto (fun n=>(Q n).directTestWorkingScale) atTop (𝓝 0) ∧
    Tendsto (fun n=>(Q n).xs) atTop (𝓝 0) := by
  have HS:=actual_theta_zero_natural_strength_scale_tendsto_zero_along dim Q hdlim
  have HU : Tendsto (fun n=>(Cs+1)*(Q n).naturalStrengthScale) atTop (𝓝 0):=by
    simpa only [mul_zero] using HS.const_mul (Cs+1)
  have HW : Tendsto (fun n=>(Q n).directTestWorkingScale) atTop (𝓝 0):=
    squeeze_zero' (Eventually.of_forall (fun n=>(Q n).direct_test_working_scale_pos.le))
      (Eventually.of_forall (fun n=>((Q n).strong_direct_test_working_geometry hCs (hstrong n)).2.1)) HU
  refine ⟨HW,?_⟩
  exact squeeze_zero' (Eventually.of_forall (fun n=>(Q n).hxs.le))
    (Eventually.of_forall (fun n=>(Q n).target_le_direct_test_working_scale)) HW

theorem actual_theta_zero_omitted_working_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (dim : ℕ→ℕ)
    (Q : (n : ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hsRatio : Tendsto (fun n=>(Q n).data.s/(Q n).xs) atTop (𝓝 0)) :
    Tendsto (fun n=>(Q n).data.s/(Q n).directTestWorkingScale) atTop (𝓝 0) := by
  exact squeeze_zero' (Eventually.of_forall (fun n=>div_nonneg (Q n).data.hs.1.le
      (Q n).direct_test_working_scale_pos.le))
    (Eventually.of_forall (fun n=>(Q n).omitted_ratio_le_target_ratio)) hsRatio

end OAI.SKFluctuations.LaplaceWindowFormalization
