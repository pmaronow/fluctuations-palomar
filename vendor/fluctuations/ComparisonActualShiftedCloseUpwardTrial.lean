module

public import ComparisonNativeCloseThresholdFractions
public import ComparisonActualShiftedOmittedCapEnvelopes

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7000000

theorem exists_actual_shifted_upward_close_trial {A B cFloor c rho y a b finish s r0:ℝ} {M:ℝ → ℝ}
    (hr0:0 ≤ r0) (hr1:r0 ≤ 1) (hs:s∈Icc (0:ℝ) 1)
    (hA:0 < A) (hB:0 < B) (hFloor:0 < cFloor)
    (hkc:∀r∈Icc r0 1,cFloor  ≤  reciprocalSquareFloor A B r)
    (hMc:Continuous M) (hMm:MonotoneOn M (Icc (0:ℝ) 1))
    (hMp:∀u∈Icc (0:ℝ) 1,0 < M u)
    (α:inverseIntegralConstraints r0 s (reciprocalSquareFloor A B) M)
    (Z:ℝ → ℝ) (hZm:MonotoneOn Z (Icc (0:ℝ) 1)) (hZb:∀u∈Icc (0:ℝ) 1,Z u∈Icc (0:ℝ) 1)
    {dp lp dc lc:ℝ} (hdp:dp≠0) (hlp:0 < lp) (hdc:dc≠0) (hlc:0 < lc)
    (hc:0 < c) (hc1:c  ≤  1) (hrho:0 < rho) (hrho1:rho  ≤  1) (hy:0 < y) (ha:s  ≤  a) (hab:a < b) (hbf:b  ≤  finish) (hf:finish  ≤  1)
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
      (∀u∈Icc b finish,(c*rho^3/200)*min (laplaceComparisonStrength dp lp y) (laplaceComparisonStrength dc lc y)*y^2  ≤ 
        laplaceComparisonStrength dp lp (R u)*t*(max (R u) (w u)-R u)*(Z u-R u)) := by
  let R:=omittedSweepQuantile hr1 hs hFloor ((reciprocalSquareFloor_continuousOn hB).mono (Icc_subset_Icc hr0 le_rfl))
    hkc hMm (hMp 1 (by norm_num)).le α
  let t:=(c*rho)/100*min 1 (laplaceComparisonStrength dc lc y/laplaceComparisonStrength dp lp y)
  let speed:=(1-rho/2)*y/(b-a)
  let w:=omittedUpwardRampBarrier M r0 s a b speed
  have haI:a∈Icc (0:ℝ) 1:=⟨hs.1.trans ha,hab.le.trans (hbf.trans hf)⟩
  have hy1:y  ≤  1:=by linarith [(hZb a haI).2]
  have hey:0 < laplaceComparisonStrength dp lp y:=laplaceComparisonStrength_pos dp hlp y
  have hDy:0 < laplaceComparisonStrength dc lc y:=laplaceComparisonStrength_pos dc hlc y
  have ht0:0  ≤  t:=by dsimp [t];positivity
  have ht1:t  ≤  1:=by
    have hh:=mul_le_mul_of_nonneg_left
      (min_le_left (1:ℝ) (laplaceComparisonStrength dc lc y/laplaceComparisonStrength dp lp y))
      (by positivity : 0  ≤  (c*rho)/100)
    dsimp [t]
    nlinarith
  have hheight:0 < 1-rho/2:=by linarith
  have hspeed0:0  ≤  speed:=by dsimp [speed];positivity
  have hspeedmass:speed*(b-a)=(1-rho/2)*y:=by
    dsimp [speed]
    exact div_mul_cancel₀ _ (sub_pos.mpr hab).ne'
  have hrise:r0+inverseCapPrimitive M 1+speed*(b-a)  ≤  1:=by rw [hspeedmass];nlinarith
  obtain ⟨γ,hγ⟩:=explicit_upward_omitted_ramp_trial hr0 hr1 hs hA hB hFloor ⟨ht0,ht1⟩ hkc hMc hMm hMp
    ha hab.le hspeed0 hrise hspeed α
  refine ⟨γ,hγ,?_,?_⟩
  · intro u hu hactive
    change R u < w u at hactive
    have hau:a < u:=by
      by_contra hn
      have hw0:truncatedBarrierRamp a b u=0:=truncatedBarrierRamp_before (le_of_not_gt hn)
      have hw:w u=r0+inverseCapPrimitive M u-inverseCapPrimitive M s:=by
        dsimp only [w,omittedUpwardRampBarrier,upwardRampBarrier]
        rw [hw0,mul_zero]
        ring
      have hcap:r0+inverseCapPrimitive M u-inverseCapPrimitive M s  ≤  R u:=
        (actual_shifted_omitted_quantile_cap_envelopes hr0 hr1 hs hFloor
          ((reciprocalSquareFloor_continuousOn hB).mono (Icc_subset_Icc hr0 le_rfl)) hkc hMc hMm hMp α hu).1
      rw [hw] at hactive
      exact (not_lt_of_ge hcap) hactive
    have hZ:y  ≤  Z u:=hZlarge.trans (hZm haI ⟨hs.1.trans hu.1,hu.2⟩ hau.le)
    have hw:w u  ≤  (1-rho/4)*y:=by
      have hh:upwardRampBarrier M a b speed u ≤ inverseCapPrimitive M 1+speed*(b-a):=
        (upwardRampBarrier_bounds hMc hMm hMp hab.le hspeed0 ⟨hs.1.trans hu.1,hu.2⟩).2
      have Hs:=inverseCapPrimitive_nonneg hMc hMm hMp hs
      rw [hspeedmass] at hh
      dsimp only [w,omittedUpwardRampBarrier]
      nlinarith
    have hrouteu:c*y  ≤  R u ∨ laplaceComparisonStrength dp lp 0  ≤  laplaceComparisonStrength dc lc y:=by
      rcases hroute with hlo|hsmall
      · exact Or.inl (hlo u ⟨hau.le,hu.2⟩)
      · exact Or.inr hsmall
    exact native_upward_close_fraction hdp hlp hdc hlc hy hy1
      (Icc_subset_Icc hr0 le_rfl (omittedSweepQuantile_bounds hr1 hs hFloor ((reciprocalSquareFloor_continuousOn hB).mono (Icc_subset_Icc hr0 le_rfl)) hkc hMm
        (hMp 1 (by norm_num)).le α u)) (hZb u ⟨hs.1.trans hu.1,hu.2⟩) hc hc1 hrho hrho1 hrouteu hactive hw hZ
  · intro u hu
    have huI:u∈Icc (0:ℝ) 1:=⟨hs.1.trans (ha.trans (hab.le.trans hu.1)),hu.2.trans hf⟩
    have hR:R u∈Icc (0:ℝ) ((1-rho)*y):=⟨(omittedSweepQuantile_bounds hr1 hs hFloor
      ((reciprocalSquareFloor_continuousOn hB).mono (Icc_subset_Icc hr0 le_rfl)) hkc hMm (hMp 1 (by norm_num)).le α u).1.trans' hr0,hRupper u hu⟩
    have hw:(1-rho/2)*y  ≤  w u:=by
      have he:truncatedBarrierRamp a b u=b-a:=truncatedBarrierRamp_after hab.le hu.1
      have hp:inverseCapPrimitive M s ≤ inverseCapPrimitive M u:=
        actual_high_only_inverseCapPrimitive_mono hMc hMm hMp hs huI (ha.trans (hab.le.trans hu.1))
      dsimp only [w,omittedUpwardRampBarrier,upwardRampBarrier]
      rw [he,hspeedmass]
      linarith
    have hZ:y  ≤  Z u:=hZlarge.trans (hZm haI huI (hab.le.trans hu.1))
    have hRw:R u  ≤  w u:=by nlinarith [hR.2]
    rw [max_eq_right hRw]
    exact native_upward_close_threshold_gain hdp hlp hlc hy hy1 hc.le hrho hrho1 hR.1 hR.2 hw hZ

end OAI.SKFluctuations.LaplaceWindowFormalization
