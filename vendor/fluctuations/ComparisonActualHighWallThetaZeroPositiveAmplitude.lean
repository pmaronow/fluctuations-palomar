module

public import ComparisonActualHighWallThetaZeroInverseClocks
public import ComparisonActualHighWallOverlapAmplitude
public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalTerminalPairLaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

namespace ActualHighWallData
variable {n:ℕ} {delta:ℝ} (a:ActualHighWallData n delta)

theorem theta_zero_radius_le_smallMass : a.rmin ≤ comparisonSmallMass a.N a.E := by
  have hcap:=a.hq.trans (concreteWallCap_ge a.hN a.hE a.hd a.hs.1.le)
  change comparisonSmallMass a.N a.E/(2*a.M a.s) ≤ _
  apply (div_le_iff₀ (by linarith : 0 < 2*a.M a.s)).mpr
  nlinarith [a.hU]

end ActualHighWallData

theorem eventually_actual_theta_zero_positive_overlap_moment_normalized
    (ell:ℕ) (Bclock:ℝ) {m delta cl cu Az C0 Ct D:ℝ}
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct) :
    ∃K:ℝ,0 < K ∧ ∀ᶠn:ℕ in atTop,
      ∀(a:ActualHighWallData (n+1) delta) (lam:ℝ) (hlam:0 < lam) (hld:lam ≤ a.d^2)
        (alpha:a.Profile) (xs z:ℝ),
      (∀beta:a.Profile,
        (a.thetaZeroShiftedParentData lam hlam hld).objective alpha ≤
          (a.thetaZeroShiftedParentData lam hlam hld).objective beta) →
      0 < xs → comparisonLowerScale a.N a.E a.d ≤ xs → a.s ≤ xs →
      z∈Icc a.rmin 1 → z ≤ Az*xs → a.d ≤ D →
      Real.sqrt a.N*a.E ≤ a.d^2 → a.N^(-(2:ℝ)/3+m)*a.d ≤ C0*a.E →
      a.N*a.E^2 ≤ Ct*laplaceComparisonStrength a.d lam xs*xs^2 →
      (∀r∈Icc z 1,cl*r ≤ alpha.val.val r ∧ alpha.val.val r ≤ cu*r) →
      (let e:=omittedStrengthCoefficient a.d a.s
          (omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha) lam
       let R:=omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha
       let hf:=fun u=>(a.thetaZeroHighOnlyData.h u+e u*R u).toNNReal
       (hf 1:ℝ)-(hf 0:ℝ) ≤ Bclock) →
      ∀u∈Ioc (0:ℝ) 1,
        let e:=omittedStrengthCoefficient a.d a.s
          (omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha) lam
        let R:=omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha
        let bf:=fun u=>(a.thetaZeroHighOnlyData.b u-e u).toNNReal
        let hf:=fun u=>(a.thetaZeroHighOnlyData.h u+e u*R u).toNNReal
        pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) bf hf)
          (fun sigma tau=>|orderedOverlap (n+1) sigma tau|^(2*(ell+1))) u ≤
          K*(xs+u)^(2*(ell+1)) := by
  obtain ⟨K,hK,hamp⟩:=comparison_minimum_retained_overlap_moment_normalized
    (D:=D) ell Bclock hm hdelta hroom hcl hcu hAz (by norm_num:(0:ℝ) < 1/3) hC0 hCt
  have hlog:∀ᶠn:ℕ in atTop,1 ≤ Real.log ((n+1:ℕ):ℝ):=
    (tendsto_add_atTop_nat 1).eventually
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1)
  refine ⟨K,hK,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hamp,
    (tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm),
    hlog] with n hnamp hndepth hnlog
  intro a lam hlam hld alpha xs z hmin hxs hscale hsxs hz hzxs hdD hupper hlower htest hregular hfield u hu
  let g:=laplaceComparisonStrength a.d lam
  let R:=omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha
  let e:=omittedStrengthCoefficient a.d a.s R lam
  let bf:=fun u=>(a.thetaZeroHighOnlyData.b u-e u).toNNReal
  let hf:=fun u=>(a.thetaZeroHighOnlyData.h u+e u*R u).toNNReal
  have hN1:1 ≤ a.N:=by exact_mod_cast Nat.succ_pos n
  have hnd:1/a.N ≤ a.d:=by
    have H:=hndepth a.E a.d a.hE a.hd hlower
    have HS:comparisonLowerScale a.N a.E a.d ≤ a.d:=by
      unfold comparisonLowerScale
      exact (div_le_iff₀ a.hd).mpr (by simpa only [pow_two] using hupper)
    exact H.trans HS
  have hr0:0 ≤ a.rmin ∧ a.rmin ≤ (1/4:ℝ):=
    ⟨a.hrbounds.1.le,a.hrbounds.2.1.trans (by linarith [a.hd1])⟩
  have hs0:0 ≤ a.s ∧ a.s ≤ (1/4:ℝ):=⟨a.hs.1.le,a.hs.2⟩
  have hslow:∀r∈Icc z 1,(1/3)/Real.log a.N ≤ 1-comparisonLogSlope g r:=by
    intro r hr
    exact laplaceComparisonStrength_uniform_slope hN1 hnlog a.hd hnd hlam hld
      ⟨a.hrbounds.1.le.trans (hz.1.trans hr.1),hr.2⟩
  have hp:∀r∈Ioc a.rmin 1,comparisonLogSlope g r∈Icc (0:ℝ) 1:=by
    intro r hr
    exact ⟨(laplaceComparisonStrength_logSlope_mem a.hd.ne' hlam.ne' r).1,
      (laplaceComparisonStrength_logSlope_mem a.hd.ne' hlam.ne' r).2.le⟩
  have had (beta:a.Profile):
      MonotoneOn (fun u=>a.thetaZeroHighOnlyData.b u-
        omittedExtension a.hs1 (constrainedCoefficient a.hr a.hc a.hk a.hkc a.hm a.hM
          g (laplaceComparisonStrength_contDiff a.d lam).continuous beta) u) (Icc (0:ℝ) 1) ∧
      MonotoneOn (fun u=>a.thetaZeroHighOnlyData.h u+
        omittedExtension a.hs1 (constrainedCoefficient a.hr a.hc a.hk a.hkc a.hm a.hM
          (fun r=>g r*r) ((laplaceComparisonStrength_contDiff a.d lam).continuous.mul continuous_id) beta) u)
        (Icc (0:ℝ) 1) ∧
      0 ≤ a.thetaZeroHighOnlyData.b 0-
        omittedExtension a.hs1 (constrainedCoefficient a.hr a.hc a.hk a.hkc a.hm a.hM
          g (laplaceComparisonStrength_contDiff a.d lam).continuous beta) 0 ∧
      0 ≤ a.thetaZeroHighOnlyData.h 0+
        omittedExtension a.hs1 (constrainedCoefficient a.hr a.hc a.hk a.hkc a.hm a.hM
          (fun r=>g r*r) ((laplaceComparisonStrength_contDiff a.d lam).continuous.mul continuous_id) beta) 0:=by
    have H:=(a.thetaZeroShiftedParentData lam hlam hld).clockAdmissible beta
    rw [←a.theta_zero_coefficient_eq_original beta lam,
      a.theta_zero_field_coefficient_eq_original beta lam]
    exact ⟨H.1,H.2.1,H.2.2.1 0 ⟨le_rfl,zero_le_one⟩,
      H.2.2.2 0 ⟨le_rfl,zero_le_one⟩⟩
  have hminInverse:∀beta:a.Profile,
      inverseCompensatedPressure a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM
        g (laplaceComparisonStrength_contDiff a.d lam).continuous (n+1)
        a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h 0 alpha ≤
      inverseCompensatedPressure a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM
        g (laplaceComparisonStrength_contDiff a.d lam).continuous (n+1)
        a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h 0 beta:=by
    intro beta
    have H:=hmin beta
    rw [a.theta_zero_objective_eq_omitted lam hlam hld alpha,
      a.theta_zero_objective_eq_omitted lam hlam hld beta,
      omittedComparisonSweepObjective_eq_inverse a.hr ⟨a.hs.1.le,a.hs1⟩
        a.hc a.hk a.hkc a.hm a.hM (n+1) a.thetaZeroHighOnlyData.b
        a.thetaZeroHighOnlyData.h a.d lam alpha,
      omittedComparisonSweepObjective_eq_inverse a.hr ⟨a.hs.1.le,a.hs1⟩
        a.hc a.hk a.hkc a.hm a.hM (n+1) a.thetaZeroHighOnlyData.b
        a.thetaZeroHighOnlyData.h a.d lam beta] at H
    exact H
  have hfieldmono:MonotoneOn a.thetaZeroHighOnlyData.h (Icc a.s 1):=by
    intro u hu v hv huv
    exact le_rfl
  have H:=hnamp (E:=a.E) (d:=a.d) (r₀:=a.rmin) (u₀:=a.s)
    a.hn a.hE a.hd hr0 hs0 g alpha
    (laplaceComparisonStrength_contDiff a.d lam)
    (fun r _=>laplaceComparisonStrength_pos a.d hlam r) hp
    a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h
    (fun beta=>(had beta).1) (fun beta=>(had beta).2.1)
    (fun beta=>(had beta).2.2.1) (fun beta=>(had beta).2.2.2)
    hminInverse ⟨u,hu.1⟩ hu.2 xs z hxs hscale hsxs
    a.theta_zero_radius_le_smallMass hz hzxs hdD hupper hlower htest hregular hslow
    hfieldmono (by
      obtain ⟨_,HH⟩:=a.theta_zero_inverse_clock_eq alpha lam
      dsimp only [g]
      convert hfield using 1
      exact congrArg₂ (fun x y:ℝ=>x-y)
        (congrArg (fun q:ℝ≥0=>(q:ℝ)) (congrFun HH 1))
        (congrArg (fun q:ℝ≥0=>(q:ℝ)) (congrFun HH 0)))
  obtain ⟨HB,HF⟩:=a.theta_zero_inverse_clock_eq alpha lam
  dsimp only [g] at H
  dsimp only [ActualHighWallData.Profile,ActualHighWallData.k,ActualHighWallData.M,
    concreteWallFloor,concreteWallCap,ActualHighWallData.N] at H HB HF ⊢
  rw [HB,HF] at H
  exact H

end OAI.SKFluctuations.LaplaceWindowFormalization
