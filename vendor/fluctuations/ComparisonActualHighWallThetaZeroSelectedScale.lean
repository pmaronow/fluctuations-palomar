module

public import ComparisonActualHighWallThetaZeroFieldClock
public import ComparisonNativeActualBadScaleSelection

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false

structure ActualThetaZeroOverlapMinimum
    (n:ℕ) (m delta cl cu Az C0 Ct D Bclock:ℝ) where
  data : ActualHighWallData n delta
  lam : ℝ
  hlam : 0 < lam
  hld : lam ≤ data.d^2
  alpha : data.Profile
  minimum : ∀beta:data.Profile,
    (data.thetaZeroShiftedParentData lam hlam hld).objective alpha ≤
      (data.thetaZeroShiftedParentData lam hlam hld).objective beta
  xs : ℝ
  z : ℝ
  hxs : 0 < xs
  hscale : comparisonLowerScale data.N data.E data.d ≤ xs
  hsxs : data.s ≤ xs
  hz : z∈Icc data.rmin 1
  hzxs : z ≤ Az*xs
  hdD : data.d ≤ D
  hupper : Real.sqrt data.N*data.E ≤ data.d^2
  hlower : data.N^(-(2:ℝ)/3+m)*data.d ≤ C0*data.E
  htest : data.N*data.E^2 ≤ Ct*laplaceComparisonStrength data.d lam xs*xs^2
  regular : ∀r∈Icc z 1,cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r
  hT : data.T ≤ Bclock

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
variable (M:ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)

theorem field_clock_budget :
    (let R:=omittedSweepQuantile M.data.hr ⟨M.data.hs.1.le,M.data.hs1⟩
        M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM M.alpha
     let e:=omittedStrengthCoefficient M.data.d M.data.s R M.lam
     let hf:=fun u=>(M.data.thetaZeroHighOnlyData.h u+e u*R u).toNNReal
     (hf 1:ℝ)-(hf 0:ℝ) ≤ Bclock) := by
  exact (M.data.theta_zero_variable_strength_field_clock_budget M.lam M.hlam M.hld
    M.alpha).trans M.hT

end ActualThetaZeroOverlapMinimum

namespace ActualHighWallData
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ} (a:ActualHighWallData n delta)

theorem exists_theta_zero_selected_bad_scale_minimum
    (lam:ℝ) (hlam:0 < lam) (hld:lam ≤ a.d^2) (alpha:a.Profile)
    (hminimum:∀beta:a.Profile,
      (a.thetaZeroShiftedParentData lam hlam hld).objective alpha ≤
        (a.thetaZeroShiftedParentData lam hlam hld).objective beta)
    (hdelta:0 ≤ delta) (hcl:cl ≤ 1) (hcu:1 ≤ cu)
    (hsA:a.s ≤ comparisonConditionalScale a.N delta a.E lam)
    (hrA:a.rmin ≤ comparisonConditionalScale a.N delta a.E lam)
    (hdD:a.d ≤ D) (hupper:Real.sqrt a.N*a.E ≤ a.d^2)
    (hlower:a.N^(-(2:ℝ)/3+m)*a.d ≤ C0*a.E)
    (hT:a.T ≤ Bclock) (hAz:2 ≤ Az) (hCt:1 ≤ Ct)
    (hbad:∃r∈Icc (min (comparisonConditionalScale a.N delta a.E lam) 1) 1,
      alpha.val.val r < cl*r ∨ cu*r < alpha.val.val r) :
    ∃M:ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      M.data=a ∧ M.lam=lam ∧ HEq M.alpha alpha ∧
      M.xs∈Icc (comparisonConditionalScale a.N delta a.E lam) 1 ∧
      M.z=min (2*M.xs) 1 ∧
      (M.alpha.val.val M.xs < cl*M.xs ∨ cu*M.xs < M.alpha.val.val M.xs) := by
  have hA:=comparison_conditional_scale_pos (delta:=delta) a.hN a.hE hlam
  obtain ⟨x,hx,hbadx,hregular⟩:=comparison_exists_bad_scale_with_regular_outer
    alpha.val.val hA hcl hcu alpha.property.2.1 hbad
  have hx0:0 < x:=hA.trans_le hx.1
  have hN1:1 ≤ a.N:=by exact_mod_cast (Nat.succ_le_iff.mpr a.hn : 1≤n)
  have hscale:comparisonLowerScale a.N a.E a.d≤x:=
    (comparison_conditional_scale_ge_lower hN1 hdelta a.hE a.hd hlam hld).trans hx.1
  have htest:a.N*a.E^2 ≤ Ct*laplaceComparisonStrength a.d lam x*x^2:=by
    have H:=comparison_selected_scale_direct_test hN1 hdelta a.hE a.hd hlam hld hupper hx0 hx.1
    have HM:=mul_le_mul_of_nonneg_right hCt
      (mul_nonneg (laplaceComparisonStrength_pos a.d hlam x).le (sq_nonneg x))
    exact H.trans (by simpa only [one_mul,mul_assoc] using HM)
  have hz:a.rmin ≤ min (2*x) 1:=by
    apply le_min _ a.hr
    linarith only [hrA,hx.1,hx0]
  let M:ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock:={
    data:=a,lam:=lam,hlam:=hlam,hld:=hld,alpha:=alpha,minimum:=hminimum,
    xs:=x,z:=min (2*x) 1,hxs:=hx0,hscale:=hscale,hsxs:=hsA.trans hx.1,
    hz:=⟨hz,min_le_right _ _⟩,
    hzxs:=(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hAz hx0.le),
    hdD:=hdD,hupper:=hupper,hlower:=hlower,htest:=htest,regular:=hregular,hT:=hT}
  exact ⟨M,rfl,rfl,HEq.rfl,hx,rfl,hbadx⟩

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
