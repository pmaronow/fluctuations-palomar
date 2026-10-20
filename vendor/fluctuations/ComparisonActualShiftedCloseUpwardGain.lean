module

public import ComparisonNativeCloseUpwardTrial
public import ComparisonActualShiftedCloseUpwardTrial

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7000000

theorem exists_actual_shifted_upward_close_cubic_gain {A B cFloor c rho y a b finish q s r0:ℝ} {M:ℝ → ℝ}
    (hr0:0 ≤ r0) (hr1:r0 ≤ 1) (hs:s∈Icc (0:ℝ) 1)
    (hA:0 < A) (hB:0 < B) (hFloor:0 < cFloor)
    (hkc:∀r∈Icc r0 1,cFloor  ≤  reciprocalSquareFloor A B r)
    (hMc:Continuous M) (hMm:MonotoneOn M (Icc (0:ℝ) 1))
    (hMp:∀u∈Icc (0:ℝ) 1,0 < M u)
    (α:inverseIntegralConstraints r0 s (reciprocalSquareFloor A B) M)
    (Z:ℝ → ℝ) (hZc:ContinuousOn Z (Icc (0:ℝ) 1)) (hZm:MonotoneOn Z (Icc (0:ℝ) 1)) (hZb:∀u∈Icc (0:ℝ) 1,Z u∈Icc (0:ℝ) 1)
    {dp lp dc lc:ℝ} (hdp:dp≠0) (hlp:0 < lp) (hdc:dc≠0) (hlc:0 < lc)
    (hc:0 < c) (hc1:c  ≤  1) (hrho:0 < rho) (hrho1:rho  ≤  1) (hy:0 < y) (ha:s  ≤  a) (hab:a < b) (hbf:b  ≤  finish) (hf:finish  ≤  1) (_hq:0  ≤  q) (hwidth:q*y  ≤  finish-b)
    (hforce:r0+inverseCapPrimitive M 1  ≤  rho*y/4)
    (hspeed:(M 0)⁻¹+(1-rho/2)*y/(b-a)  ≤  B^2/A)
    (hZlarge:y  ≤  Z a)
    (hroute:(∀u∈Icc a 1,c*y  ≤  omittedSweepQuantile hr1 hs hFloor ((reciprocalSquareFloor_continuousOn hB).mono (Icc_subset_Icc hr0 le_rfl))
      hkc hMm (hMp 1 (by norm_num)).le α u) ∨
      laplaceComparisonStrength dp lp 0  ≤  laplaceComparisonStrength dc lc y)
    (hRupper:∀u∈Icc b finish,omittedSweepQuantile hr1 hs hFloor ((reciprocalSquareFloor_continuousOn hB).mono (Icc_subset_Icc hr0 le_rfl))
      hkc hMm (hMp 1 (by norm_num)).le α u  ≤  (1-rho)*y) :
    let R:=omittedSweepQuantile hr1 hs hFloor ((reciprocalSquareFloor_continuousOn hB).mono (Icc_subset_Icc hr0 le_rfl))
      hkc hMm (hMp 1 (by norm_num)).le α
    let t:=(c*rho)/100*min 1 (laplaceComparisonStrength dc lc y/laplaceComparisonStrength dp lp y)
    let w:=omittedUpwardRampBarrier M r0 s a b ((1-rho/2)*y/(b-a))
    ∃γ:inverseIntegralConstraints r0 s (reciprocalSquareFloor A B) M,
      (∀u∈Icc s 1,γ.val.val ((1-t)*R u+t*max (R u) (w u))=u) ∧
      (∀u∈Icc s 1,R u < w u →
        t*(w u-R u)/(Z u-R u)∈Ico (0:ℝ)
          (laplaceComparisonStrength dc lc (Z u)/
            (laplaceComparisonStrength dp lp (R u)+laplaceComparisonStrength dc lc (Z u)))) ∧
      (c*rho^3*q/200)*min (laplaceComparisonStrength dp lp y) (laplaceComparisonStrength dc lc y)*y^3  ≤ 
        ∫u in (0:ℝ)..1,laplaceComparisonStrength dp lp (R u)*t*(max (R u) (w u)-R u)*(Z u-R u) := by
  let R:=omittedSweepQuantile hr1 hs hFloor ((reciprocalSquareFloor_continuousOn hB).mono (Icc_subset_Icc hr0 le_rfl))
    hkc hMm (hMp 1 (by norm_num)).le α
  let t:=(c*rho)/100*min 1 (laplaceComparisonStrength dc lc y/laplaceComparisonStrength dp lp y)
  let w:=omittedUpwardRampBarrier M r0 s a b ((1-rho/2)*y/(b-a))
  obtain ⟨γ,hγ,hmove,hpoint⟩:=exists_actual_shifted_upward_close_trial hr0 hr1 hs hA hB hFloor hkc hMc hMm hMp α Z
    hZm hZb hdp hlp hdc hlc hc hc1 hrho hrho1 hy ha hab hbf hf hforce hspeed hZlarge hroute hRupper
  refine ⟨γ,hγ,hmove,?_⟩
  have hRc:ContinuousOn R (Icc (0:ℝ) 1):=
    (omittedSweepQuantile_continuous hr1 hs hFloor ((reciprocalSquareFloor_continuousOn hB).mono (Icc_subset_Icc hr0 le_rfl)) hkc hMm
      (hMp 1 (by norm_num)).le α).continuousOn
  obtain ⟨Cw,hw⟩:=upwardRampBarrier_lipschitz hMc hMm hMp a b ((1-rho/2)*y/(b-a))
  have Hwc:ContinuousOn w (Icc (0:ℝ) 1):=by
    exact continuousOn_const.add hw.continuousOn
  have Hactive:∀u∈Icc (0:ℝ) 1,R u<w u → 0  ≤  t*(w u-R u)/(Z u-R u):=by
    intro u hu hactive
    by_cases Hs:s  ≤  u
    · exact (hmove u ⟨Hs,hu.2⟩ hactive).1
    · have HR:R u=r0:=actual_shifted_omitted_quantile_low_origin hr0 hr1 hs hFloor
        ((reciprocalSquareFloor_continuousOn hB).mono (Icc_subset_Icc hr0 le_rfl)) hkc hMm (hMp 1 (by norm_num)).le α (not_le.mp Hs).le
      have HP:=actual_high_only_inverseCapPrimitive_mono hMc hMm hMp hu hs (not_le.mp Hs).le
      have Hramp:truncatedBarrierRamp a b u=0:=truncatedBarrierRamp_before ((not_le.mp Hs).le.trans ha)
      have Hw:w u  ≤  r0:=by
        dsimp only [w,omittedUpwardRampBarrier,upwardRampBarrier]
        rw [Hramp,mul_zero]
        linarith
      rw [HR] at hactive
      exact False.elim (not_lt_of_ge Hw hactive)
  have hec:Continuous (laplaceComparisonStrength dp lp):=(laplaceComparisonStrength_contDiff dp lp).continuous
  have hconst:0  ≤  (c*rho^3/200)*min (laplaceComparisonStrength dp lp y) (laplaceComparisonStrength dc lc y)*y^2:=by
    have hey:=laplaceComparisonStrength_pos dp hlp y
    have hDy:=laplaceComparisonStrength_pos dc hlc y
    positivity
  have hbudget:=native_upward_interval_gain R w Z (laplaceComparisonStrength dp lp) hRc Hwc hZc hec
    (fun u _=>(laplaceComparisonStrength_pos dp hlp (R u)).le) (hs.1.trans (ha.trans hab.le)) hbf hf
    Hactive hpoint
  have hwidth':((c*rho^3/200)*min (laplaceComparisonStrength dp lp y) (laplaceComparisonStrength dc lc y)*y^2)*(q*y)  ≤ 
      ((c*rho^3/200)*min (laplaceComparisonStrength dp lp y) (laplaceComparisonStrength dc lc y)*y^2)*(finish-b):=
    mul_le_mul_of_nonneg_left hwidth hconst
  have hh:=hwidth'.trans hbudget
  convert hh using 1; ring

end OAI.SKFluctuations.LaplaceWindowFormalization
