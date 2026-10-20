module

public import ComparisonActualHighWallThetaZeroSelectedAmplitude
public import ComparisonActualHighOnlyConditionalDensityBasics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false

namespace ActualHighWallData
variable {n:ℕ} {delta:ℝ} (a:ActualHighWallData n delta)

abbrev thetaZeroRadius (alpha:a.Profile) :=
  omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha
abbrev thetaZeroCoefficient (lam:ℝ) (alpha:a.Profile) :=
  omittedStrengthCoefficient a.d a.s (a.thetaZeroRadius alpha) lam
abbrev thetaZeroBf (lam:ℝ) (alpha:a.Profile) : ℝ→ℝ≥0 :=
  fun u=>(a.thetaZeroHighOnlyData.b u-a.thetaZeroCoefficient lam alpha u).toNNReal
abbrev thetaZeroHf (lam:ℝ) (alpha:a.Profile) : ℝ→ℝ≥0 :=
  fun u=>(a.thetaZeroHighOnlyData.h u+
    a.thetaZeroCoefficient lam alpha u*a.thetaZeroRadius alpha u).toNNReal

def thetaZeroErrorDensity (lam:ℝ) (alpha:a.Profile) (u:ℝ):ℝ :=
  a.thetaZeroCoefficient lam alpha u*
    ((orderedPathB n (a.thetaZeroBf lam alpha) (a.thetaZeroHf lam alpha) u-
      (orderedPathS n (a.thetaZeroBf lam alpha) (a.thetaZeroHf lam alpha) u)^2)+
      (orderedPathS n (a.thetaZeroBf lam alpha) (a.thetaZeroHf lam alpha) u-
        a.thetaZeroRadius alpha u)^2)

theorem theta_zero_density_eq_error_integral (lam:ℝ) (alpha:a.Profile) :
    a.thetaZeroOriginalSweepDensity lam alpha=
      ∫u in (0:ℝ)..1,a.thetaZeroErrorDensity lam alpha u := rfl

theorem theta_zero_radius_low (alpha:a.Profile) {u:ℝ} (hu:u ≤ a.s):
    a.thetaZeroRadius alpha u=a.rmin := by
  have H:=omittedSweepQuantile_monotone a.hr ⟨a.hs.1.le,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM alpha hu
  rw [omittedSweepQuantile_left a.hr ⟨a.hs.1.le,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM alpha] at H
  exact le_antisymm H (omittedSweepQuantile_bounds a.hr ⟨a.hs.1.le,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM alpha u).1

theorem theta_zero_coefficient_low (lam:ℝ) (alpha:a.Profile)
    {u:ℝ} (hu:u<a.s):a.thetaZeroCoefficient lam alpha u=0 := by
  simp [thetaZeroCoefficient,omittedStrengthCoefficient,not_le_of_gt hu]

theorem theta_zero_error_density_low (lam:ℝ) (alpha:a.Profile)
    {u:ℝ} (hu:u<a.s):a.thetaZeroErrorDensity lam alpha u=0 := by
  simp [thetaZeroErrorDensity,a.theta_zero_coefficient_low lam alpha hu]

theorem theta_zero_error_low_prefix_zero (lam:ℝ) (alpha:a.Profile):
    (∫u in (0:ℝ)..a.s,a.thetaZeroErrorDensity lam alpha u)=0 := by
  apply Eq.trans ?_ (intervalIntegral.integral_zero :
    (∫u in (0:ℝ)..a.s,(0:ℝ))=0)
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne a.s] with u hus hu
  have huu:u∈Ioc (0:ℝ) a.s:=by simpa only [uIoc_of_le a.hs.1.le] using hu
  exact a.theta_zero_error_density_low lam alpha (lt_of_le_of_ne huu.2 hus)

theorem theta_zero_radius_bounds (alpha:a.Profile) (u:ℝ):
    a.thetaZeroRadius alpha u∈Icc (0:ℝ) 1 := by
  have H:=omittedSweepQuantile_bounds a.hr ⟨a.hs.1.le,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM alpha u
  exact ⟨a.hrbounds.1.le.trans H.1,H.2⟩

theorem theta_zero_coefficient_bounds {lam:ℝ} (hlam:0<lam)
    (alpha:a.Profile) (u:ℝ):
    a.thetaZeroCoefficient lam alpha u∈Icc (0:ℝ) lam := by
  unfold thetaZeroCoefficient omittedStrengthCoefficient
  split_ifs
  · exact ⟨(laplaceComparisonStrength_pos a.d hlam _).le,
      laplaceComparisonStrength_le a.d hlam.le _⟩
  · exact ⟨le_rfl,hlam.le⟩

theorem theta_zero_density_le_two_strength (alpha:a.Profile) {lam:ℝ}
    (hlam:0<lam) (hld:lam≤a.d^2):
    a.thetaZeroOriginalSweepDensity lam alpha≤2*lam := by
  let R:=a.thetaZeroRadius alpha
  let e:=a.thetaZeroCoefficient lam alpha
  let bf:=a.thetaZeroBf lam alpha
  let hf:=a.thetaZeroHf lam alpha
  have Hclock:=(a.thetaZeroShiftedParentData lam hlam hld).clockAdmissible alpha
  have hbf:MonotoneOn bf (Icc (0:ℝ) 1):=toNNReal_monotoneOn Hclock.1
  have hhf:MonotoneOn hf (Icc (0:ℝ) 1):=toNNReal_monotoneOn Hclock.2.1
  have hR:=omittedSweepQuantile_monotone a.hr ⟨a.hs.1.le,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM alpha
  have hRb:=omittedSweepQuantile_bounds a.hr ⟨a.hs.1.le,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM alpha
  have hquad:=actual_quadratic_integrable n a.hn bf hf hbf hhf R (hR.monotoneOn _)
    (fun u _=>(a.theta_zero_radius_bounds alpha u).1)
  have hco:∀u,e u∈Icc (0:ℝ) lam:=a.theta_zero_coefficient_bounds hlam alpha
  have hg:Measurable (fun u=>laplaceComparisonStrength a.d lam (R u)):=
    (laplaceComparisonStrength_contDiff a.d lam).continuous.measurable.comp
      (omittedSweepQuantile_continuous a.hr ⟨a.hs.1.le,a.hs1⟩
        a.hc a.hk a.hkc a.hm a.hM alpha).measurable
  have he:Measurable e:=by
    convert hg.indicator (s:={u:ℝ|a.s≤u})
      (measurableSet_le measurable_const measurable_id) using 1
    funext u
    simp only [e,thetaZeroCoefficient,omittedStrengthCoefficient,
      Set.indicator_apply,mem_ofPred_eq,R]
  have hi:=intervalIntegrable_bounded_measurable_mul he hlam.le
    (fun u _=>hco u) (hquad.1.add hquad.2)
  have hp:∀ᵐu∂volume.restrict (Ioc (0:ℝ) 1),
      e u*((orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
        (orderedPathS n bf hf u-R u)^2)≤2*lam:=by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hs:=orderedPath_SK_bounds n a.hn bf hf hbf hhf hu
    have hr:R u∈Icc (0:ℝ) 1:=a.theta_zero_radius_bounds alpha u
    have hr2:(R u)^2≤1:=by nlinarith [hr.1,hr.2]
    have hbracket:(orderedPathB n bf hf u-(orderedPathS n bf hf u)^2)+
        (orderedPathS n bf hf u-R u)^2≤2:=by
      have hm:=mul_nonneg hs.1 hr.1
      change 0≤orderedPathS n bf hf u*R u at hm
      nlinarith [hs.2.2.2]
    exact (mul_le_mul_of_nonneg_left hbracket (hco u).1).trans
      (by linarith [(hco u).2])
  rw [a.theta_zero_density_eq_error_integral lam alpha]
  change (∫u in 0..1,e u*((orderedPathB n bf hf u-
    (orderedPathS n bf hf u)^2)+(orderedPathS n bf hf u-R u)^2))≤2*lam
  have H:(∫u in 0..1,e u*((orderedPathB n bf hf u-
      (orderedPathS n bf hf u)^2)+(orderedPathS n bf hf u-R u)^2))≤
      ∫u in (0:ℝ)..1,(2*lam):=by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact integral_mono_ae ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hi)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp intervalIntegrable_const) hp
  simpa using H

theorem theta_zero_density_large_conditional_scale (alpha:a.Profile) {lam:ℝ}
    (hlam:0<lam) (hld:lam≤a.d^2) (hN:8≤a.N) (hE1:a.E≤1)
    (hlarge:a.N≤comparisonConditionalScale a.N delta a.E lam+1):
    a.thetaZeroOriginalSweepDensity lam alpha≤a.N^(2*delta)*a.E:=
  (a.theta_zero_density_le_two_strength alpha hlam hld).trans
    (comparison_large_conditional_scale_strength_le hN a.hE hE1 hlam hlarge)

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
