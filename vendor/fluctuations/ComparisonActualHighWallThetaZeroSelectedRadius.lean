module

public import ComparisonActualHighWallThetaZeroSelectedPotential
public import ComparisonShiftedNativeBandCarrier

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
  (Q:ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

abbrev radiusS:ℝ→ℝ:=
  fun r=>orderedPathS (n+1) Q.sweepBf Q.sweepHf (Q.alpha.val.val r)
abbrev radiusB:ℝ→ℝ:=
  fun r=>orderedPathB (n+1) Q.sweepBf Q.sweepHf (Q.alpha.val.val r)
abbrev radiusThermal:ℝ→ℝ:=fun r=>Q.radiusB r-(Q.radiusS r)^2

theorem radius_mass_mem {r:ℝ} (hr:r∈Icc Q.data.rmin 1):
    Q.alpha.val.val r∈Ioc (0:ℝ) 1 := by
  have H:=inverseConstraint_mass_mem Q.data.hr Q.data.hc Q.data.hk
    Q.data.hkc Q.alpha hr
  exact ⟨Q.data.hs.1.trans_le H.1,H.2⟩

theorem radius_moments:
    MonotoneOn Q.radiusS (Icc Q.data.rmin 1) ∧
    MonotoneOn Q.radiusB (Icc Q.data.rmin 1) ∧
    ∀r∈Icc Q.data.rmin 1,Q.radiusS r∈Icc (0:ℝ) 1 ∧
      (Q.radiusS r)^2≤Q.radiusB r ∧ Q.radiusB r≤1 := by
  have hm:=orderedPath_SK_monotone (n+1) Q.data.hn Q.sweepBf Q.sweepHf
    Q.sweep_bf_monotone Q.sweep_hf_monotone
  have hα:=(inverseConstraint_strictMonoOn Q.data.hc Q.data.hk Q.data.hkc
    Q.alpha.property).monotoneOn
  refine ⟨?_,?_,?_⟩
  · intro r hr t ht hrt
    exact hm.1 (Q.radius_mass_mem hr) (Q.radius_mass_mem ht) (hα hr ht hrt)
  · intro r hr t ht hrt
    exact hm.2 (Q.radius_mass_mem hr) (Q.radius_mass_mem ht) (hα hr ht hrt)
  · intro r hr
    have hb:=orderedPath_SK_bounds (n+1) Q.data.hn Q.sweepBf Q.sweepHf
      Q.sweep_bf_monotone Q.sweep_hf_monotone (Q.radius_mass_mem hr)
    exact ⟨⟨hb.1,hb.2.1⟩,hb.2.2⟩

abbrev shiftedNativeModel:ShiftedNativeBandModel where
  rmin:=Q.data.rmin
  u0:=Q.data.s
  c:=Q.data.k 1
  k:=Q.data.k
  M:=Q.data.M
  hr:=Q.data.hr
  hu:=⟨Q.data.hs.1.le,Q.data.hs1⟩
  hc:=Q.data.hc
  hk:=Q.data.hk
  hkc:=Q.data.hkc
  hm:=Q.data.hm
  hM:=Q.data.hM
  alpha:=Q.alpha
  n:=n
  bf:=Q.sweepBf
  hf:=Q.sweepHf
  hbf:=Q.sweep_bf_monotone
  hhf:=Q.sweep_hf_monotone

theorem shiftedNativeModel_radius (u:ℝ):Q.shiftedNativeModel.R u=Q.sweepRadius u:=rfl

theorem inverse_radius_le_source_mass (hcl:0<cl) (hAz:0≤Az)
    {u:ℝ} (hu:u∈Icc (0:ℝ) 1):
    Q.sweepRadius u≤(Az+1/cl)*(Q.xs+u) := by
  have hR:=omittedSweepQuantile_bounds Q.data.hr
    ⟨Q.data.hs.1.le,Q.data.hs1⟩ Q.data.hc Q.data.hk Q.data.hkc
    Q.data.hm Q.data.hM Q.alpha u
  by_cases hus:u<Q.data.s
  · have HR:Q.sweepRadius u=Q.data.rmin:=
      Q.data.theta_zero_radius_low Q.alpha hus.le
    rw [HR]
    have hC:0≤Az+1/cl:=by positivity
    have hA:Q.data.rmin≤Az*Q.xs:=Q.hz.1.trans Q.hzxs
    have H1:Az*Q.xs≤(Az+1/cl)*Q.xs:=by
      nlinarith [mul_nonneg (one_div_pos.mpr hcl).le Q.hxs.le]
    exact hA.trans (H1.trans (mul_le_mul_of_nonneg_left (by linarith [hu.1]) hC))
  · have huhi:u∈Icc Q.data.s 1:=⟨le_of_not_gt hus,hu.2⟩
    have Hspec:=omittedSweepQuantile_spec Q.data.hr
      ⟨Q.data.hs.1.le,Q.data.hs1⟩ Q.data.hc Q.data.hk Q.data.hkc
      Q.data.hm Q.data.hM Q.alpha huhi
    by_cases hsmall:Q.sweepRadius u<Q.z
    · have HH:0≤1/cl:=by positivity
      nlinarith [Q.hzxs,Q.hxs,hu.1]
    · have Hregular:=Q.regular (Q.sweepRadius u) ⟨le_of_not_gt hsmall,hR.2⟩
      rw [Hspec] at Hregular
      have HR:Q.sweepRadius u≤u/cl:=
        (le_div_iff₀ hcl).mpr (by nlinarith [Hregular.1])
      have HH:=mul_le_mul_of_nonneg_right
        (show 1/cl≤Az+1/cl by linarith) hu.1
      calc
        Q.sweepRadius u≤u/cl:=HR
        _=(1/cl)*u:=by ring
        _≤(Az+1/cl)*u:=HH
        _≤(Az+1/cl)*(Q.xs+u):=
          mul_le_mul_of_nonneg_left (by linarith [Q.hxs]) (by positivity)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
