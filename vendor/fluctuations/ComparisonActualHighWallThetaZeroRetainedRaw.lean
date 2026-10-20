module

public import ComparisonActualHighWallThetaZeroSelectedRadius
public import ComparisonActualHighWallThetaZeroBarePullback
public import ComparisonTwoSidedNativeRawRetention
public import ComparisonSignedCavityActualMinimumResampling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy Cavity
open scoped BigOperators Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false

theorem eventually_actual_theta_zero_original_boundary_raw
    (ell:ℕ) (Bclock:ℝ) {m delta cl cu Az C0 Ct D:ℝ}
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,
      ∀Q:ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      ∀u:PositiveMass,u.val≤1 →
      ∀extra:List PositiveMass,(∀v∈extra,v.val≤1) →
      ∃us:List PositiveMass,(∀v∈us,v.val≤1) ∧ u∈us ∧
        (∀v∈extra,v∈us) ∧ ∀ᶠj:ℕ in atTop,
          let as:=finiteCutMasses us j
          let steps:=sampleClockSteps (completedPathClock n Q.sweepBf Q.sweepHf) 0 as
          let V:=stepClockValues (fun i=>(completedPathClock n Q.sweepBf Q.sweepHf 0 i:ℝ)) steps
          (physicalRawRatio n (ell+1) steps 0 Q.xs
            (Measure.pi fun i=>gaussianReal 0 (completedPathClock n Q.sweepBf Q.sweepHf 0 i))
            id measurable_id)^2≤2*C ∧
          ∀low:ℕ,low≤as.length →
            (physicalRawRatio n (ell+1) (originalBoundaryTailSteps n as V low)
              (physicalCutMass 0 steps low) Q.xs (originalBoundaryPrefixLaw n as V low)
              id measurable_id)^2≤2*C := by
  obtain ⟨C,hC,hraw⟩:=comparison_minimum_finite_raw_ratio_retaining
    (D:=D) ell Bclock hm hdelta hroom hcl hcu hAz
    (by norm_num:(0:ℝ)<1/3) hC0 hCt
  have hlog:∀ᶠn:ℕ in atTop,1≤Real.log (n:ℝ):=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  refine ⟨C,hC,?_⟩
  filter_upwards [hraw,eventually_comparisonLowerScale_depth hC0 hm,hlog,
    eventually_ge_atTop (1:ℕ)] with n hnraw hndepth hnlog hn1
  intro Q u hu extra hextra
  let a:=Q.data
  let g:=laplaceComparisonStrength a.d Q.lam
  have hN1:(1:ℝ)≤a.N:=by exact_mod_cast hn1
  have hnd:1/a.N≤a.d:=by
    have hh:=hndepth a.E a.d a.hE a.hd Q.hlower
    have hs:comparisonLowerScale n a.E a.d≤a.d:=by
      unfold comparisonLowerScale
      exact (div_le_iff₀ a.hd).mpr (by simpa only [pow_two] using Q.hupper)
    exact hh.trans hs
  have hr0:a.rmin∈Icc (0:ℝ) (1/4):=
    ⟨a.hrbounds.1.le,a.hrbounds.2.1.trans (by linarith [a.hd1])⟩
  have hs0:a.s∈Icc (0:ℝ) (1/4):=⟨a.hs.1.le,a.hs.2⟩
  have hslow:∀r∈Icc Q.z 1,(1/3)/Real.log (n:ℝ)≤1-comparisonLogSlope g r:=by
    intro r hr
    exact laplaceComparisonStrength_uniform_slope hN1 hnlog a.hd hnd Q.hlam Q.hld
      ⟨a.hrbounds.1.le.trans (Q.hz.1.trans hr.1),hr.2⟩
  have hp:∀r∈Ioc a.rmin 1,comparisonLogSlope g r∈Icc (0:ℝ) 1:=by
    intro r hr
    exact ⟨(laplaceComparisonStrength_logSlope_mem a.hd.ne' Q.hlam.ne' r).1,
      (laplaceComparisonStrength_logSlope_mem a.hd.ne' Q.hlam.ne' r).2.le⟩
  have had (beta:a.Profile):
      MonotoneOn (fun u=>a.thetaZeroHighOnlyData.b u-
        omittedExtension a.hs1 (constrainedCoefficient a.hr a.hc a.hk a.hkc a.hm a.hM
          g (laplaceComparisonStrength_contDiff a.d Q.lam).continuous beta) u) (Icc (0:ℝ) 1) ∧
      MonotoneOn (fun u=>a.thetaZeroHighOnlyData.h u+
        omittedExtension a.hs1 (constrainedCoefficient a.hr a.hc a.hk a.hkc a.hm a.hM
          (fun r=>g r*r) ((laplaceComparisonStrength_contDiff a.d Q.lam).continuous.mul continuous_id) beta) u)
          (Icc (0:ℝ) 1) ∧
      0≤a.thetaZeroHighOnlyData.b 0-
        omittedExtension a.hs1 (constrainedCoefficient a.hr a.hc a.hk a.hkc a.hm a.hM
          g (laplaceComparisonStrength_contDiff a.d Q.lam).continuous beta) 0 ∧
      0≤a.thetaZeroHighOnlyData.h 0+
        omittedExtension a.hs1 (constrainedCoefficient a.hr a.hc a.hk a.hkc a.hm a.hM
          (fun r=>g r*r) ((laplaceComparisonStrength_contDiff a.d Q.lam).continuous.mul continuous_id) beta) 0:=by
    have H:=(a.thetaZeroShiftedParentData Q.lam Q.hlam Q.hld).clockAdmissible beta
    rw [←a.theta_zero_coefficient_eq_original beta Q.lam,
      a.theta_zero_field_coefficient_eq_original beta Q.lam]
    exact ⟨H.1,H.2.1,H.2.2.1 0 ⟨le_rfl,zero_le_one⟩,
      H.2.2.2 0 ⟨le_rfl,zero_le_one⟩⟩
  have hbare:MonotoneOn a.thetaZeroHighOnlyData.h (Icc a.s 1):=by
    intro _ _ _ _ _
    exact le_rfl
  obtain ⟨us,hus,huus,hextraus,hfinite⟩:=hnraw a.hn a.hE a.hd hr0 hs0 g Q.alpha
    (laplaceComparisonStrength_contDiff a.d Q.lam)
    (fun r _=>laplaceComparisonStrength_pos a.d Q.hlam r) hp
    a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h
    (fun beta=>(had beta).1) (fun beta=>(had beta).2.1)
    (fun beta=>(had beta).2.2.1) (fun beta=>(had beta).2.2.2)
    Q.inverse_minimum u hu extra hextra Q.xs Q.z Q.hxs Q.hscale Q.hsxs
    a.theta_zero_radius_le_smallMass Q.hz Q.hzxs Q.hdD Q.hupper Q.hlower
    Q.htest Q.regular hslow hbare (by
      obtain ⟨_,HH⟩:=a.theta_zero_inverse_clock_eq Q.alpha Q.lam
      dsimp only [g]
      convert Q.field_clock_budget using 1
      exact congrArg₂ (fun x y:ℝ=>x-y)
        (congrArg (fun q:ℝ≥0=>(q:ℝ)) (congrFun HH 1))
        (congrArg (fun q:ℝ≥0=>(q:ℝ)) (congrFun HH 0)))
  refine ⟨us,hus,huus,hextraus,?_⟩
  filter_upwards [hfinite] with j hj
  dsimp only at hj ⊢
  obtain ⟨HB,HF⟩:=a.theta_zero_inverse_clock_eq Q.alpha Q.lam
  dsimp only [g] at hj
  dsimp only [ActualHighWallData.Profile,ActualHighWallData.k,ActualHighWallData.M,
    concreteWallFloor,concreteWallCap,ActualHighWallData.N] at hj HB HF
  rw [HB,HF] at hj
  refine ⟨hj,?_⟩
  intro low hlow
  have h:=original_boundary_raw_ratio_le_sampled n (ell+1)
    (completedPathClock n Q.sweepBf Q.sweepHf) (finiteCutMasses us j)
    (finiteCutMasses_ordered us hus j) low hlow Q.hxs
  dsimp only at h
  apply (pow_le_pow_left₀ ?_ h 2).trans hj
  exact zero_le_one.trans (physicalRawRatio_one_le _ _ _ _ _ _ _ _)

end OAI.SKFluctuations.LaplaceWindowFormalization
