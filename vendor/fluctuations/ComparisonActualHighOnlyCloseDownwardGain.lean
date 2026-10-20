module

public import ComparisonNativeCloseDownwardFractions
public import ComparisonActualHighOnlyDownwardClippedRadius

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7000000

theorem exists_actual_high_only_downward_close_cubic_gain {A B cFloor C rho y start stop b finish q s:ℝ} {M:ℝ → ℝ}
    (hs:s∈Icc (0:ℝ) 1)
    (hA:0 < A) (hB:0 < B) (hFloor:0 < cFloor)
    (hkc:∀r∈Icc (0:ℝ) 1,cFloor  ≤  reciprocalSquareFloor A B r)
    (hMc:Continuous M) (hMm:MonotoneOn M (Icc (0:ℝ) 1)) (hMp:∀u∈Icc (0:ℝ) 1,0 < M u)
    (α:inverseIntegralConstraints 0 s (reciprocalSquareFloor A B) M)
    (Z:ℝ → ℝ) (hZc:ContinuousOn Z (Icc (0:ℝ) 1)) (hZm:MonotoneOn Z (Icc (0:ℝ) 1))
    (hZb:∀u∈Icc (0:ℝ) 1,Z u∈Icc (0:ℝ) 1)
    {dp lp dc lc:ℝ} (hdp:dp≠0) (hlp:0 < lp) (hdc:dc≠0) (hlc:0 < lc)
    (hC:1  ≤  C) (hrho:0 < rho) (hrho1:rho  ≤  1) (hy:0 < y) (hy1:y  ≤  1)
    (ha:s  ≤  start) (hab:start  ≤  stop) (hstop:stop  ≤  b) (hb:b  ≤  finish) (hf:finish  ≤  1)
    (_hq:0  ≤  q) (hwidth:q*y  ≤  stop-start)
    (hforce:inverseCapPrimitive M 1  ≤  rho*y/4) (hspeed:(M 0)⁻¹  ≤  B^2/A)
    (htravel:b+reciprocalFloorTime A B 1  ≤  finish) (hZsmall:Z finish  ≤  (1-rho)*y)
    (hRupper:∀u∈Icc (0:ℝ) finish,omittedSweepQuantile zero_le_one hs hFloor (reciprocalSquareFloor_continuousOn hB)
      hkc hMm (hMp 1 (by norm_num)).le α u  ≤  C*y)
    (hRlarge:∀u∈Icc start stop,y  ≤  omittedSweepQuantile zero_le_one hs hFloor (reciprocalSquareFloor_continuousOn hB)
      hkc hMm (hMp 1 (by norm_num)).le α u) :
    let R:=omittedSweepQuantile zero_le_one hs hFloor (reciprocalSquareFloor_continuousOn hB)
      hkc hMm (hMp 1 (by norm_num)).le α
    let t:=(1/C)/100*min 1 (laplaceComparisonStrength dc lc y/laplaceComparisonStrength dp lp y)
    let w:=downwardRampBarrier A B M ((1-rho/2)*y) b
    let Rhat:=fun u=>harmonicBarrierRadius B t (R u) (min (R u) (w u))
    ∃γ:inverseIntegralConstraints 0 s (reciprocalSquareFloor A B) M,
      (∀u∈Icc s 1,γ.val.val (Rhat u)=u) ∧
      (∀u∈Icc (0:ℝ) 1,w u < R u →
        (R u-Rhat u)/(R u-Z u)∈Ico (0:ℝ)
          (laplaceComparisonStrength dc lc (Z u)/
            (laplaceComparisonStrength dp lp (R u)+laplaceComparisonStrength dc lc (Z u)))) ∧
      (q*rho^2/(400*C^2))*min (laplaceComparisonStrength dp lp y) (laplaceComparisonStrength dc lc y)*y^3  ≤ 
        ∫u in (0:ℝ)..1,laplaceComparisonStrength dp lp (R u)*(R u-Rhat u)*(R u-Z u) := by
  let R:=omittedSweepQuantile zero_le_one hs hFloor (reciprocalSquareFloor_continuousOn hB)
    hkc hMm (hMp 1 (by norm_num)).le α
  let ey:=laplaceComparisonStrength dp lp y
  let Dy:=laplaceComparisonStrength dc lc y
  let t:=(1/C)/100*min 1 (Dy/ey)
  let w:=downwardRampBarrier A B M ((1-rho/2)*y) b
  let v:=fun u=>min (R u) (w u)
  let Rhat:=fun u=>harmonicBarrierRadius B t (R u) (v u)
  have hC0:0 < C:=zero_lt_one.trans_le hC
  have hey:0 < ey:=laplaceComparisonStrength_pos dp hlp y
  have hDy:0 < Dy:=laplaceComparisonStrength_pos dc hlc y
  have ht0:0  ≤  t:=by dsimp [t];positivity
  have ht1:t  ≤  1:=by
    have hh:=mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (Dy/ey)) (show 0  ≤  (1/C)/100 by positivity)
    have hi:1/C  ≤  1:=by simpa only [one_div] using inv_le_one_of_one_le₀ hC
    dsimp [t]
    nlinarith
  have hheight:0  ≤  (1-rho/2)*y:=mul_nonneg (by linarith) hy.le
  have hroom:(1-rho/2)*y+inverseCapPrimitive M 1  ≤  1:=by nlinarith
  have hbI:b∈Icc (0:ℝ) 1:=⟨hs.1.trans (ha.trans (hab.trans hstop)),hb.trans hf⟩
  have hfinish:finish∈Icc (0:ℝ) 1:=⟨hbI.1.trans hb,hf⟩
  have htail:b+reciprocalFloorTime A B 1  ≤  1:=htravel.trans hf
  obtain ⟨γ,hγ⟩:=explicit_downward_omitted_ramp_trial le_rfl zero_le_one hs hA hB hFloor ⟨ht0,ht1⟩ hkc hMc hMm hMp
    hheight hroom hbI htail hspeed α
  have hwb:∀u∈Icc (0:ℝ) 1,w u∈Icc (0:ℝ) 1:=
    fun u hu=>downwardRampBarrier_mem (b:=b) hA hB hMc hMm hMp hheight hroom hu
  have hRbounds:∀u∈Icc (0:ℝ) 1,R u∈Icc (0:ℝ) 1:=fun u _=>
    omittedSweepQuantile_bounds zero_le_one hs hFloor (reciprocalSquareFloor_continuousOn hB) hkc hMm
      (hMp 1 (by norm_num)).le α u
  have hwlower:∀u∈Icc (0:ℝ) 1,(1-rho/2)*y  ≤  w u:=by
    intro u hu
    have hh:=native_downward_barrier_base_le (b:=b) hA hB hMc hMm hMp hheight hroom hu
    have hp:=inverseCapPrimitive_nonneg hMc hMm hMp hu
    dsimp only [downwardBarrierBase] at hh
    linarith
  have hactive:∀u∈Icc (0:ℝ) 1,w u < R u →
      u  ≤  finish ∧ Z u  ≤  (1-rho)*y ∧ R u  ≤  C*y:=by
    intro u hu huclip
    have huf:u  ≤  finish:=by
      by_contra hn
      have HHs:s ≤ u:=ha.trans (hab.trans (hstop.trans (hb.trans (lt_of_not_ge hn).le)))
      have hh:=actual_high_only_downward_clipped_radius_after hs hA hB hFloor hkc hMc hMm hMp hheight hroom hbI α ⟨HHs,hu.2⟩
        (htravel.trans (lt_of_not_ge hn).le)
      change min (R u) (w u)=R u at hh
      rw [min_eq_right huclip.le] at hh
      linarith
    exact ⟨huf,(hZm hu hfinish huf).trans hZsmall,hRupper u ⟨hu.1,huf⟩⟩
  have hmove:∀u∈Icc (0:ℝ) 1,w u < R u →
      (R u-Rhat u)/(R u-Z u)∈Ico (0:ℝ)
        (laplaceComparisonStrength dc lc (Z u)/(laplaceComparisonStrength dp lp (R u)+laplaceComparisonStrength dc lc (Z u))):=by
    intro u hu huclip
    have hh:=hactive u hu huclip
    dsimp only [Rhat,v]
    rw [min_eq_right huclip.le]
    exact native_downward_close_fraction hB hC hdp hlp hdc hlc hy hy1 (hRbounds u hu)
      (hZb u hu) hrho hrho1 (hwlower u hu) huclip.le hh.2.2 hh.2.1
  refine ⟨γ,hγ,hmove,?_⟩
  have hRlip:LipschitzOnWith ⟨1/cFloor,by positivity⟩ R (Icc (0:ℝ) 1):=
    (omittedSweepQuantile_lipschitz zero_le_one hs hFloor (reciprocalSquareFloor_continuousOn hB) hkc hMm
      (hMp 1 (by norm_num)).le α).lipschitzOnWith
  obtain ⟨Cw,hwlip⟩:=downwardRampBarrier_lipschitz (b:=b) hA hB hMc hMm hMp hheight hroom
  have hvlip:=real_min_lipschitzOn hRlip hwlip
  have hvbounds:MapsTo v (Icc (0:ℝ) 1) (Icc (0:ℝ) 1):=by
    intro u hu
    exact ⟨le_min (hRbounds u hu).1 (hwb u hu).1,(min_le_left _ _).trans (hRbounds u hu).2⟩
  obtain ⟨Ch,hhc⟩:=harmonicBarrierRadius_lipschitz hB ⟨ht0,ht1⟩ hRlip hvlip (fun u hu=>hRbounds u hu) hvbounds
  have hzero:∀u∈Icc (0:ℝ) 1,0  ≤  laplaceComparisonStrength dp lp (R u)*(R u-Rhat u)*(R u-Z u):=by
    intro u hu
    by_cases huclip:w u < R u
    · have hh:=hactive u hu huclip
      have hdisp:0  ≤  R u-Rhat u:=by
        dsimp only [Rhat,v]
        rw [min_eq_right huclip.le]
        exact (mul_nonneg ht0 (sub_nonneg.mpr huclip.le)).trans
          (harmonicBarrierRadius_displacement_bounds hB ⟨ht0,ht1⟩ (hwb u hu).1 huclip.le).1
      exact mul_nonneg (mul_nonneg (laplaceComparisonStrength_pos dp hlp (R u)).le hdisp)
        (by nlinarith [hwlower u hu] : 0  ≤  R u-Z u)
    · have he:Rhat u=R u:=by
        dsimp only [Rhat,v]
        rw [min_eq_left (le_of_not_gt huclip)]
        exact harmonicBarrierRadius_diagonal hB (hRbounds u hu).1
      rw [he,sub_self,mul_zero,zero_mul]
  have hpoint:∀u∈Icc start stop,
      (rho^2/(400*C^2))*min ey Dy*y^2  ≤  laplaceComparisonStrength dp lp (R u)*(R u-Rhat u)*(R u-Z u):=by
    intro u hu
    have huI:u∈Icc (0:ℝ) 1:=⟨hs.1.trans (ha.trans hu.1),hu.2.trans (hstop.trans (hb.trans hf))⟩
    have hwu:w u  ≤  (1-rho/4)*y:=by
      have he:=downwardRampBarrier_before hA hB hMc hMm hMp hheight hroom hspeed hbI huI (hu.2.trans hstop)
      have hp:=inverseCapPrimitive_le_total hMc hMm hMp huI
      change w u=downwardBarrierBase M ((1-rho/2)*y) u at he
      dsimp only [downwardBarrierBase] at he
      nlinarith
    have hrl:=hRlarge u hu
    have hclip:w u < R u:=by nlinarith
    have hh:=hactive u huI hclip
    dsimp only [Rhat,v]
    rw [min_eq_right hclip.le]
    exact native_downward_close_threshold_gain hB hC hdp hlp hlc hy hy1 (hRbounds u huI)
      hrho hrho1 (hwb u huI).1 hwu hrl hh.2.2 hh.2.1
  have hbudget:=native_downward_interval_gain R Rhat Z (laplaceComparisonStrength dp lp)
    hRlip.continuousOn hhc.continuousOn hZc (laplaceComparisonStrength_contDiff dp lp).continuous
    (hs.1.trans ha) hab (hstop.trans (hb.trans hf)) hzero hpoint
  have hconst:0  ≤  (rho^2/(400*C^2))*min ey Dy*y^2:=by positivity
  have hh:((rho^2/(400*C^2))*min ey Dy*y^2)*(q*y)  ≤ 
      ((rho^2/(400*C^2))*min ey Dy*y^2)*(stop-start):=mul_le_mul_of_nonneg_left hwidth hconst
  have hg:=hh.trans hbudget
  convert hg using 1; ring

end OAI.SKFluctuations.LaplaceWindowFormalization
