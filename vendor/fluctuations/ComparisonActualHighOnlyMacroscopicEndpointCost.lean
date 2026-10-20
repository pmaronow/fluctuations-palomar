module

public import ComparisonActualHighOnlyInverseClocks
public import ComparisonMacroscopicScalarIdentification
public import ComparisonMacroscopicShellEndpoint

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000
namespace ActualHighOnlyComparisonData
variable {n : ℕ} {delta : ℝ} (a : ActualHighOnlyComparisonData n delta)

def radiusProfile (alpha : a.Profile) : boundedMassProfiles :=
  ⟨a.R alpha,⟨fun u=>omittedSweepQuantile_bounds zero_le_one ⟨a.hs.1,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM alpha u,
    omittedSweepQuantile_monotone zero_le_one ⟨a.hs.1,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha⟩⟩

theorem radius_below_initial_zero (alpha : a.Profile) {u : ℝ} (hu : u<a.s) :
    a.R alpha u=0 := by
  have HR:=omittedSweepQuantile_monotone zero_le_one ⟨a.hs.1,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM alpha hu.le
  have Hleft:=omittedSweepQuantile_left zero_le_one ⟨a.hs.1,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM alpha
  change a.R alpha a.s=0 at Hleft
  change a.R alpha u≤a.R alpha a.s at HR
  rw [Hleft] at HR
  exact le_antisymm HR ((a.radiusProfile alpha).property.1 u).1

def fullStrengthBareMatrix (alpha : a.Profile) (lam : ℝ) (u : ℝ) : ℝ :=
  a.b u+laplaceComparisonStrength a.d lam (a.R alpha u)-a.coefficient alpha lam u

theorem coefficient_field_eq_full (alpha : a.Profile) (lam u : ℝ) :
    a.coefficient alpha lam u*a.R alpha u=
      laplaceComparisonStrength a.d lam (a.R alpha u)*a.R alpha u := by
  by_cases hu:a.s≤u
  · simp only [coefficient,omittedStrengthCoefficient,ite_eq_left hu]
  · rw [a.radius_below_initial_zero alpha (not_le.mp hu)]
    simp

theorem fullStrength_clockAdmissible (alpha : a.Profile) {lam : ℝ}
    (hlam : lam∈Icc (0:ℝ) (a.d^2)) :
    comparisonClockAdmissible (a.fullStrengthBareMatrix alpha lam) a.h
      (fun u=>laplaceComparisonStrength a.d lam (a.R alpha u)) (a.R alpha) := by
  have H:=a.clocks_admissible alpha hlam
  have HB:(fun u=>a.fullStrengthBareMatrix alpha lam u-
      laplaceComparisonStrength a.d lam (a.R alpha u))=(fun u=>a.b u-a.coefficient alpha lam u):=by
    funext u
    dsimp only [fullStrengthBareMatrix]
    ring
  have HF:(fun u=>a.h u+laplaceComparisonStrength a.d lam (a.R alpha u)*a.R alpha u)=
      (fun u=>a.h u+a.coefficient alpha lam u*a.R alpha u):=by
    funext u
    rw [a.coefficient_field_eq_full]
  refine ⟨?_,?_,?_,?_⟩
  · rw [HB]
    exact H.1
  · rw [HF]
    exact H.2.1
  · change 0≤(fun u=>a.fullStrengthBareMatrix alpha lam u-
      laplaceComparisonStrength a.d lam (a.R alpha u)) 0
    rw [HB]
    exact H.2.2.1 0 ⟨le_rfl,zero_le_one⟩
  · change 0≤(fun u=>a.h u+laplaceComparisonStrength a.d lam (a.R alpha u)*a.R alpha u) 0
    rw [HF]
    exact H.2.2.2 0 ⟨le_rfl,zero_le_one⟩

theorem original_objective_eq_fullStrength (alpha : a.Profile) (lam : ℝ) :
    a.objective lam alpha=pathCompensatedPressure n
      (a.fullStrengthBareMatrix alpha lam) a.h
      (fun u=>laplaceComparisonStrength a.d lam (a.R alpha u)) (a.R alpha) 0 := by
  have HB:(fun u=>a.fullStrengthBareMatrix alpha lam u-
      laplaceComparisonStrength a.d lam (a.R alpha u))=(fun u=>a.b u-a.coefficient alpha lam u):=by
    funext u
    dsimp only [fullStrengthBareMatrix]
    ring
  have HF:(fun u=>a.h u+laplaceComparisonStrength a.d lam (a.R alpha u)*a.R alpha u)=
      (fun u=>a.h u+a.coefficient alpha lam u*a.R alpha u):=by
    funext u
    rw [a.coefficient_field_eq_full]
  have HP:(fun u=>a.coefficient alpha lam u*(a.R alpha u)^2)=
      (fun u=>laplaceComparisonStrength a.d lam (a.R alpha u)*(a.R alpha u)^2):=by
    funext u
    simpa only [pow_two,mul_assoc] using congrArg (fun z=>z*a.R alpha u)
      (a.coefficient_field_eq_full alpha lam u)
  change realOrderedSKPathPressure n (fun u=>a.b u-a.coefficient alpha lam u)
      (fun u=>a.h u+a.coefficient alpha lam u*a.R alpha u) 0+
      (1/4:ℝ)*(∫u in (0:ℝ)..1,a.coefficient alpha lam u*(a.R alpha u)^2)=_
  unfold pathCompensatedPressure
  rw [HB,HF,HP]

theorem fullStrengthBareMatrix_intervalIntegrable (alpha : a.Profile) {lam : ℝ}
    (hlam : lam∈Icc (0:ℝ) (a.d^2)) :
    IntervalIntegrable (a.fullStrengthBareMatrix alpha lam) volume 0 1 := by
  have HA:IntervalIntegrable (fun u=>a.b u-a.coefficient alpha lam u) volume 0 1:=
    (show MonotoneOn (fun u=>a.b u-a.coefficient alpha lam u) (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one,coefficient] using (a.clocks_admissible alpha hlam).1).intervalIntegrable
  have HR:=omittedSweepQuantile_continuous zero_le_one ⟨a.hs.1,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM alpha
  have HG:IntervalIntegrable (fun u=>laplaceComparisonStrength a.d lam (a.R alpha u)) volume 0 1:=
    ((laplaceComparisonStrength_contDiff a.d lam).continuous.comp HR).intervalIntegrable 0 1
  convert HA.add HG using 1
  ext u
  dsimp only [fullStrengthBareMatrix]
  ring

theorem fullStrengthBareMatrix_extra_l1 (alpha : a.Profile) {lam : ℝ}
    (hlam : lam∈Icc (0:ℝ) (a.d^2)) :
    (∫u in (0:ℝ)..1,|a.fullStrengthBareMatrix alpha lam u-a.b u|)=a.s*lam := by
  have HE:(∫u in (0:ℝ)..1,|a.fullStrengthBareMatrix alpha lam u-a.b u|)=
      ∫u in (0:ℝ)..1,(Iic a.s).indicator (fun _:ℝ=>lam) u:=by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne a.s] with u hne _
    by_cases hu:u<a.s
    · have HR:=a.radius_below_initial_zero alpha hu
      have Hzero:laplaceComparisonStrength a.d lam 0=lam:=by
        simp [laplaceComparisonStrength,comparisonStrength,laplaceComparisonShape]
      have Hdiff:a.fullStrengthBareMatrix alpha lam u-a.b u=lam:=by
        dsimp only [fullStrengthBareMatrix,coefficient,omittedStrengthCoefficient]
        rw [HR,Hzero,ite_eq_right (not_le.mpr hu)]
        ring
      rw [Hdiff,abs_of_nonneg hlam.1]
      simp [hu.le]
    · have Hhigh:a.s<u:=lt_of_le_of_ne (not_lt.mp hu) (Ne.symm hne)
      have Hdiff:a.fullStrengthBareMatrix alpha lam u-a.b u=0:=by
        dsimp only [fullStrengthBareMatrix,coefficient,omittedStrengthCoefficient]
        rw [ite_eq_left Hhigh.le]
        ring
      rw [Hdiff,abs_zero]
      simp [not_le.mpr Hhigh]
  rw [HE]
  change (∫u in (0:ℝ)..1,{u:ℝ|u≤a.s}.indicator (fun _=>lam) u)=_
  rw [intervalIntegral.integral_indicator ⟨a.hs.1,a.hs1⟩]
  simp

theorem fullStrengthBareMatrix_endpoint_cost_le (alpha : a.Profile) {lam T : ℝ}
    (hlam : lam∈Icc (0:ℝ) (a.d^2)) :
    comparisonEndpointL1Cost T (a.fullStrengthBareMatrix alpha lam) a.h≤
      comparisonEndpointL1Cost T a.b a.h+a.s*lam/4 := by
  have HB:IntervalIntegrable (fun u=>|a.b u-T|) volume 0 1:=
    ((show MonotoneOn a.b (uIcc (0:ℝ) 1) by simpa only [uIcc_of_le zero_le_one] using a.hb).intervalIntegrable.sub intervalIntegrable_const).abs
  have HC:IntervalIntegrable (fun u=>|a.fullStrengthBareMatrix alpha lam u-T|) volume 0 1:=
    ((a.fullStrengthBareMatrix_intervalIntegrable alpha hlam).sub intervalIntegrable_const).abs
  have HD:IntervalIntegrable (fun u=>|a.fullStrengthBareMatrix alpha lam u-a.b u|) volume 0 1:=
    ((a.fullStrengthBareMatrix_intervalIntegrable alpha hlam).sub
      (show MonotoneOn a.b (uIcc (0:ℝ) 1) by simpa only [uIcc_of_le zero_le_one] using a.hb).intervalIntegrable).abs
  have H:=intervalIntegral.integral_mono_on zero_le_one HC (HB.add HD) (fun u _=>by
    have H:=abs_add_le (a.b u-T) (a.fullStrengthBareMatrix alpha lam u-a.b u)
    have HE:a.fullStrengthBareMatrix alpha lam u-T=
        (a.b u-T)+(a.fullStrengthBareMatrix alpha lam u-a.b u):=by ring
    rw [HE]
    exact H)
  rw [intervalIntegral.integral_add HB HD,a.fullStrengthBareMatrix_extra_l1 alpha hlam] at H
  unfold comparisonEndpointL1Cost
  linarith

theorem original_endpoint_cost (alpha : a.Profile) {lam T : ℝ}
    (hlam : lam∈Icc (0:ℝ) (a.d^2)) (hlT : lam≤T) :
    |a.objective lam alpha-pathCompensatedPressure n (fun _=>T) (fun _=>0)
      (fun u=>laplaceComparisonStrength a.d lam (a.R alpha u)) (a.R alpha) 0| ≤ 
      comparisonEndpointL1Cost T a.b a.h+a.s*lam/4 := by
  rw [a.original_objective_eq_fullStrength]
  exact (actualComparison_endpoint_cost n a.hn a.hd.ne' hlam.1 hlT
    (a.fullStrengthBareMatrix alpha lam) a.h (a.radiusProfile alpha)
    (a.fullStrength_clockAdmissible alpha hlam)).trans
      (a.fullStrengthBareMatrix_endpoint_cost_le alpha hlam)

end ActualHighOnlyComparisonData
end OAI.SKFluctuations.LaplaceWindowFormalization
