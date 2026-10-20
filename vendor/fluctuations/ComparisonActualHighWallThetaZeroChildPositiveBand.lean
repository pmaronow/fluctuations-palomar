module

public import ComparisonActualHighWallThetaZeroChildClockNumerics
public import ComparisonActualHighWallThetaZeroMacroscopicAllMassExclusion

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}

theorem theta_zero_wall_radius_le_regular_cap
    (M:ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hcl:0<cl) {u:ℝ} (hu:u∈Icc M.data.s 1):
    M.data.wallRadius M.alpha u≤M.z+u/cl:=by
  have hR:=M.data.wallRadius_bounds M.alpha u
  have hspec:=M.data.wallRadius_spec M.alpha hu
  by_cases hz:M.z≤M.data.wallRadius M.alpha u
  · have H:=(M.regular _ ⟨hz,hR.2⟩).1
    rw [hspec] at H
    have Hdiv:M.data.wallRadius M.alpha u≤u/cl:=
      (le_div_iff₀ hcl).mpr (by simpa only [mul_comm] using H)
    linarith [M.hz.1,M.data.hrbounds.1]
  · have Hdiv:0≤u/cl:=div_nonneg (M.data.hs.1.le.trans hu.1) hcl.le
    linarith [le_of_not_ge hz]

theorem theta_zero_high_clock_formula
    (M:ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    {u:ℝ} (hu:u∈Icc M.data.s 1):
    |M.changedBare u-M.data.T|=
        laplaceComparisonStrength M.data.d M.lam (M.data.wallRadius M.alpha u) ∧
      |M.changedField u|=
        laplaceComparisonStrength M.data.d M.lam (M.data.wallRadius M.alpha u)*
          M.data.wallRadius M.alpha u:=by
  let P:=M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld
  let R:=M.data.wallRadius M.alpha
  let g:=laplaceComparisonStrength M.data.d M.lam
  have hcoef:P.coefficient M.alpha u=g (R u):=by
    change omittedStrengthCoefficient M.data.d M.data.s R M.lam u =
      laplaceComparisonStrength M.data.d M.lam (R u)
    simp only [omittedStrengthCoefficient,ite_eq_left hu.1]
  have hbare:P.b u=M.data.T:=by
    change wallBareMatrix M.data.T M.data.epsilon 0 M.data.s u=M.data.T
    simp only [wallBareMatrix,not_lt.mpr hu.1,ite_false]
  have hfield:P.h u=0:=rfl
  have hr:R u∈Icc (0:ℝ) 1:=by
    have H:=M.data.wallRadius_bounds M.alpha u
    exact ⟨M.data.hrbounds.1.le.trans H.1,H.2⟩
  have hg:0≤g (R u):=(laplaceComparisonStrength_pos M.data.d M.hlam _).le
  change |P.b u-P.coefficient M.alpha u-M.data.T|=g (R u) ∧
    |P.h u+P.coefficient M.alpha u*P.R M.alpha u|=g (R u)*R u
  rw [hbare,hcoef,hfield]
  change |M.data.T-g (R u)-M.data.T|=g (R u) ∧
    |(0:ℝ)+g (R u)*R u|=g (R u)*R u
  simp only [sub_sub_cancel_left,abs_neg,abs_of_nonneg hg,zero_add,
    abs_of_nonneg (mul_nonneg hg hr.1),and_self]

end ActualThetaZeroOverlapMinimum

theorem eventually_theta_zero_child_positive_band_increments
    {m delta cl cu Az C0 Ct D Bclock c0:ℝ}
    (hdelta:0<delta) (hcl:0<cl) (hAz:0≤Az) (hC0:0<C0)
    (hc0:0<c0) (hc01:c0≤1) {eta Cmass:ℝ}
    (heta:0<eta) (heta1:eta≤1) (hCmass:0≤Cmass)
    (hmargin:0<9*m-298*delta):
    ∀ᶠn:ℕ in atTop,
      ∀M:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs≤1 → comparisonConditionalScale M.data.N delta M.data.E M.lam≤M.xs →
      laplaceComparisonStrength M.data.d M.lam M.xs≤(eta*c0)^3*M.xs^2 →
      M.z≤Az*M.xs →
      ∀y:ℝ,actualChildCutoff (n+1) delta c0 M.data.d M.lam M.xs≤y →
      ∀u∈Icc M.data.s (min (Cmass*y) 1),
        |M.changedBare u-M.data.T|≤eta^2*y^2 ∧
        |M.changedField u| ≤ (max 1 (Az+Cmass/cl))*eta^2*y^3:=by
  let C:=max 1 (Az+Cmass/cl)
  have hC:1≤C:=le_max_left _ _
  have hC0':0≤C:=zero_le_one.trans hC
  filter_upwards [eventually_theta_zero_child_numeric_clock_increments_from_target
      (m:=m) (delta:=delta) (C0:=C0) (c0:=c0)
      hdelta hC0 hc0 hc01 heta heta1 hC hmargin,
    eventually_theta_zero_strength_le_child_cutoff_sq
      (m:=m) (delta:=delta) (C0:=C0) (c0:=c0)
      hdelta hC0 hc0 hc01 heta heta1 hmargin] with n hn hlamBound
  intro M hunit htarget hweak hz y hay u hu
  let a:=actualChildCutoff (n+1) delta c0 M.data.d M.lam M.xs
  have ha:0<a:=(actual_child_cutoff_pos_le_radius M.data.hN hc0 M.hlam M.hxs).1
  have hy:0<y:=ha.trans_le hay
  have hu1:u∈Icc M.data.s 1:=⟨hu.1,hu.2.trans (min_le_right _ _)⟩
  have huCy:u≤Cmass*y:=hu.2.trans (min_le_left _ _)
  have hrwall:=M.data.wallRadius_bounds M.alpha u
  have hr:M.data.wallRadius M.alpha u∈Icc (0:ℝ) 1:=
    ⟨M.data.hrbounds.1.le.trans hrwall.1,hrwall.2⟩
  have hlam:M.lam≤eta^2*a^2:=hlamBound M hunit htarget hweak
  have Hg:laplaceComparisonStrength M.data.d M.lam (M.data.wallRadius M.alpha u)≤
      eta^2*y^2:=
    (laplaceComparisonStrength_le M.data.d M.hlam.le _).trans
      (hlam.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ ha.le hay 2) (sq_nonneg eta)))
  rw [(M.theta_zero_high_clock_formula hu1).1,
    (M.theta_zero_high_clock_formula hu1).2]
  refine ⟨Hg,?_⟩
  have Hr:M.data.wallRadius M.alpha u≤Az*M.xs+(Cmass/cl)*y:=by
    have H:=M.theta_zero_wall_radius_le_regular_cap hcl hu1
    have Hdiv:u/cl≤(Cmass/cl)*y:=by
      convert div_le_div_of_nonneg_right huCy hcl.le using 1
      ring
    linarith only [H,Hdiv,hz]
  by_cases hyx:y≤M.xs
  · have HrCx:M.data.wallRadius M.alpha u≤C*M.xs:=by
      have H:=mul_le_mul_of_nonneg_left hyx (div_nonneg hCmass hcl.le)
      have H':=mul_le_mul_of_nonneg_right
        (le_max_right 1 (Az+Cmass/cl)) M.hxs.le
      nlinarith only [Hr,H,H']
    have HH:=(hn M hunit htarget hweak (M.data.wallRadius M.alpha u) hr HrCx).2
    have Hpow:=pow_le_pow_left₀ ha.le hay 3
    have Het:eta^3≤eta^2:=by
      have H:=mul_le_mul_of_nonneg_left heta1 (sq_nonneg eta)
      nlinarith only [H]
    have H1:=mul_le_mul_of_nonneg_left Hpow
      (mul_nonneg hC0' (pow_nonneg heta.le 3))
    have H2:=mul_le_mul_of_nonneg_left Het
      (mul_nonneg hC0' (pow_nonneg hy.le 3))
    change laplaceComparisonStrength M.data.d M.lam (M.data.wallRadius M.alpha u)*
      M.data.wallRadius M.alpha u≤C*eta^2*y^3
    nlinarith only [HH,H1,H2]
  · have HrCy:M.data.wallRadius M.alpha u≤C*y:=by
      have H:=mul_le_mul_of_nonneg_left (le_of_not_ge hyx) hAz
      have H':=mul_le_mul_of_nonneg_right
        (le_max_right 1 (Az+Cmass/cl)) hy.le
      nlinarith only [Hr,H,H']
    have H:=mul_le_mul Hg HrCy hr.1 (by positivity:0≤eta^2*y^2)
    change laplaceComparisonStrength M.data.d M.lam (M.data.wallRadius M.alpha u)*
      M.data.wallRadius M.alpha u≤C*eta^2*y^3
    nlinarith only [H]

end OAI.SKFluctuations.LaplaceWindowFormalization
