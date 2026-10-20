module

public import ComparisonNativeUpwardChildBarrierGain
public import FiniteBarrierBandGain
public import StrictMovementFraction

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7000000

theorem native_downward_barrier_base_le {A B H b:ℝ} {M:ℝ → ℝ}
    (hA:0 < A) (hB:0 < B) (hMc:Continuous M)
    (hm:MonotoneOn M (Icc (0:ℝ) 1)) (hMp:∀u∈Icc (0:ℝ) 1,0 < M u)
    (hH:0 ≤ H) (hroom:H+inverseCapPrimitive M 1 ≤ 1)
    {u:ℝ} (hu:u∈Icc (0:ℝ) 1) :
    downwardBarrierBase M H u ≤ downwardRampBarrier A B M H b u := by
  have hbase:=downwardBarrierBase_mem hA hB hMc hm hMp hH hroom hu
  have henv:=downwardBarrierEnvelope_mem hA hB hMc hm hMp hH hroom hu
  have hclock:=downwardBarrierClock_mem (b:=b) hA hB hMc hm hMp hH hroom u hu
  have hw:=downwardRampBarrier_mem (b:=b) hA hB hMc hm hMp hH hroom hu
  have hlo:reciprocalFloorTime A B (downwardBarrierBase M H u) ≤
      downwardBarrierClock A B M H b u:=by
    apply le_min
    · exact (reciprocalFloorTime_monotoneOn hA.le hB) hbase henv
        (downwardBarrierBase_le_envelope hA hB hMc hm hMp hH hroom u)
    · exact le_max_left _ _
  have he:reciprocalFloorTime A B (downwardRampBarrier A B M H b u)=
      downwardBarrierClock A B M H b u:=reciprocalFloorInverse_right hA hB hclock
  rw [←he] at hlo
  by_contra hn
  have hlt:downwardRampBarrier A B M H b u < downwardBarrierBase M H u:=lt_of_not_ge hn
  have hh:=div_lt_div_of_pos_left hA (by linarith [hw.1] : 0 < downwardRampBarrier A B M H b u+B)
    (by linarith : downwardRampBarrier A B M H b u+B < downwardBarrierBase M H u+B)
  unfold reciprocalFloorTime at hlo
  linarith

theorem native_downward_child_fraction {B C dp lp dc lc y r v z:ℝ}
    (hB:0 < B) (hC:1 ≤ C) (hdp:dp≠0) (hlp:0 < lp) (hdc:dc≠0) (hlc:0 < lc)
    (hy:0 < y) (hy1:y ≤ 1) (hr:r∈Icc (0:ℝ) 1) (hz:z∈Icc (0:ℝ) 1)
    (hvlower:2*y ≤ v) (hvr:v ≤ r) (hrC:r ≤ C*y) (hzy:z ≤ y) :
    let t:=(1/C)/100*min 1 (laplaceComparisonStrength dc lc y/laplaceComparisonStrength dp lp y)
    (r-harmonicBarrierRadius B t r v)/(r-z)∈Ico (0:ℝ)
      (laplaceComparisonStrength dc lc z/
        (laplaceComparisonStrength dp lp r+laplaceComparisonStrength dc lc z)) := by
  let ey:=laplaceComparisonStrength dp lp y
  let Dy:=laplaceComparisonStrength dc lc y
  let t:=(1/C)/100*min 1 (Dy/ey)
  have hC0:0 < C:=zero_lt_one.trans_le hC
  have hey:0 < ey:=laplaceComparisonStrength_pos dp hlp y
  have hDy:0 < Dy:=laplaceComparisonStrength_pos dc hlc y
  have ht0:0 ≤ t:=by dsimp [t];positivity
  have hct:C*t ≤ 1/100:=by
    have hh:=mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (Dy/ey)) (show 0 ≤ (1/C)/100 by positivity)
    have he:C*((1/C)/100)=1/100:=by field_simp
    have hj:=mul_le_mul_of_nonneg_left hh hC0.le
    dsimp [t]
    nlinarith
  have ht:t∈Icc (0:ℝ) 1:=⟨ht0,by nlinarith [mul_le_mul_of_nonneg_right hC ht0]⟩
  have hv:0 ≤ v:=by linarith
  have hzr:z < r:=by linarith
  have hratio:(r+B)/(v+B) ≤ C:=by
    apply (div_le_iff₀ (by linarith : 0 < v+B)).mpr
    have hh:=mul_le_mul_of_nonneg_left hvlower hC0.le
    have hj:=mul_le_mul_of_nonneg_right hC hB.le
    nlinarith
  have hs:=harmonic_downward_fraction_bound hB ht hv hvr (by linarith : z ≤ v) hzr hratio
  have her:laplaceComparisonStrength dp lp r ≤ ey:=
    (laplaceComparisonStrength_monotonicities hdp hlp (r₀:=0) le_rfl).1 ⟨hy.le,hy1⟩ hr (by linarith)
  have hDz:Dy ≤ laplaceComparisonStrength dc lc z:=
    (laplaceComparisonStrength_monotonicities hdc hlc (r₀:=0) le_rfl).1 hz ⟨hy.le,hy1⟩ hzy
  refine ⟨hs.1,?_⟩
  apply strict_movement_fraction_of_scale (C:=C) (Ce:=1) (Cd:=1) (eta:=(1/C)/100)
    (laplaceComparisonStrength_pos dp hlp r).le hey hDy zero_lt_one hC0.le zero_le_one
    (by positivity) (by simpa using her) (by simpa using hDz) hs.1
    (by simpa only [t,mul_assoc] using hs.2)
  have he:C*((1/C)/100)*(1+1:ℝ)=1/50:=by field_simp;norm_num
  rw [he]
  norm_num

theorem native_downward_threshold_gain {B C dp lp dc lc y r v z:ℝ}
    (hB:0 < B) (hC:1 ≤ C) (hdp:dp≠0) (hlp:0 < lp) (hlc:0 < lc)
    (hy:0 < y) (hy1:y ≤ 1) (hr:r∈Icc (0:ℝ) 1)
    (hv:0 ≤ v) (hvlower:2*y ≤ v) (hvupper:v ≤ (9/4:ℝ)*y)
    (hrlower:4*y ≤ r) (hrC:r ≤ C*y) (hzy:z ≤ y) :
    let t:=(1/C)/100*min 1 (laplaceComparisonStrength dc lc y/laplaceComparisonStrength dp lp y)
    (1/(100*C^2))*min (laplaceComparisonStrength dp lp y) (laplaceComparisonStrength dc lc y)*y^2 ≤
      laplaceComparisonStrength dp lp r*(r-harmonicBarrierRadius B t r v)*(r-z) := by
  let ey:=laplaceComparisonStrength dp lp y
  let Dy:=laplaceComparisonStrength dc lc y
  let t:=(1/C)/100*min 1 (Dy/ey)
  have hC0:0 < C:=zero_lt_one.trans_le hC
  have hey:0 < ey:=laplaceComparisonStrength_pos dp hlp y
  have hDy:0 < Dy:=laplaceComparisonStrength_pos dc hlc y
  have ht0:0 ≤ t:=by dsimp [t];positivity
  have ht1:t ≤ 1:=by
    have hh:=mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (Dy/ey)) (show 0 ≤ (1/C)/100 by positivity)
    have hi:1/C ≤ 1:=by simpa only [one_div] using inv_le_one_of_one_le₀ hC
    dsimp [t]
    nlinarith
  have her:ey/C ≤ laplaceComparisonStrength dp lp r:=by
    have hf:ey*y ≤ laplaceComparisonStrength dp lp r*r:=
      (laplaceComparisonStrength_monotonicities hdp hlp (r₀:=0) le_rfl).2 ⟨hy.le,hy1⟩ hr (by linarith)
    have hh:=mul_le_mul_of_nonneg_left hrC (laplaceComparisonStrength_pos dp hlp r).le
    apply (div_le_iff₀ hC0).mpr
    nlinarith
  have hvr:v ≤ r:=by linarith
  have hzr:z < r:=by linarith
  have hdisp: t*(r-v) ≤ r-harmonicBarrierRadius B t r v:=
    (harmonicBarrierRadius_displacement_bounds hB ⟨ht0,ht1⟩ hv hvr).1
  have hgap:y ≤ r-v:=by linarith
  have hzGap:y ≤ r-z:=by linarith
  have hdd:t*y ≤ r-harmonicBarrierRadius B t r v:=
    (mul_le_mul_of_nonneg_left hgap ht0).trans hdisp
  have hmul:=mul_le_mul hdd hzGap hy.le ((mul_nonneg ht0 hy.le).trans hdd)
  have hg:=mul_le_mul her hmul (by positivity : 0 ≤ t*y*y) (laplaceComparisonStrength_pos dp hlp r).le
  have he:t*ey=((1/C)/100)*min ey Dy:=native_barrier_fraction_strength (c:=1/C) hey
  have heq:(ey/C)*(t*y*y)=(1/(100*C^2))*min ey Dy*y^2:=by
    calc
      _ = (t*ey)*y^2/C:=by ring
      _ = _:=by rw [he];field_simp
  rw [heq] at hg
  convert hg using 1 <;> ring

theorem native_downward_interval_gain (R Rhat Z e:ℝ → ℝ)
    (hR:ContinuousOn R (Icc (0:ℝ) 1)) (hh:ContinuousOn Rhat (Icc (0:ℝ) 1))
    (hZ:ContinuousOn Z (Icc (0:ℝ) 1)) (he:Continuous e)
    {start stop K:ℝ} (ha:0 ≤ start) (hab:start ≤ stop) (hb:stop ≤ 1)
    (hzero:∀u∈Icc (0:ℝ) 1,0 ≤ e (R u)*(R u-Rhat u)*(R u-Z u))
    (hband:∀u∈Icc start stop,K ≤ e (R u)*(R u-Rhat u)*(R u-Z u)) :
    K*(stop-start) ≤ ∫u in (0:ℝ)..1,e (R u)*(R u-Rhat u)*(R u-Z u) := by
  let G:=fun u=>e (R u)*(R u-Rhat u)*(R u-Z u)
  have hGc:ContinuousOn G (Icc (0:ℝ) 1):=((he.comp_continuousOn hR).mul (hR.sub hh)).mul (hR.sub hZ)
  have hGi:IntervalIntegrable G volume 0 1:=hGc.intervalIntegrable_of_Icc zero_le_one
  have hGb:IntervalIntegrable G volume start stop:=
    (hGc.mono (Icc_subset_Icc ha hb)).intervalIntegrable_of_Icc hab
  have hl:(∫_ in start..stop,K) ≤ ∫u in start..stop,G u:=
    intervalIntegral.integral_mono_on hab intervalIntegrable_const hGb hband
  have hr:(∫u in start..stop,G u) ≤ ∫u in (0:ℝ)..1,G u:=by
    apply intervalIntegral.integral_mono_interval ha hab hb _ hGi
    change ∀ᵐu∂volume.restrict (Ioc (0:ℝ) 1),0 ≤ G u
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall (fun u hu=>hzero u ⟨hu.1.le,hu.2⟩)
  change K*(stop-start) ≤ ∫u in (0:ℝ)..1,G u
  simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_comm] using hl.trans hr

theorem exists_native_downward_child_cubic_gain {A B cFloor C y start stop b finish q:ℝ} {M:ℝ → ℝ}
    (hA:0 < A) (hB:0 < B) (hFloor:0 < cFloor)
    (hkc:∀r∈Icc (0:ℝ) 1,cFloor ≤ reciprocalSquareFloor A B r)
    (hMc:Continuous M) (hMm:MonotoneOn M (Icc (0:ℝ) 1)) (hMp:∀u∈Icc (0:ℝ) 1,0 < M u)
    (α:inverseIntegralConstraints 0 0 (reciprocalSquareFloor A B) M)
    (Z:ℝ → ℝ) (hZc:ContinuousOn Z (Icc (0:ℝ) 1)) (hZm:MonotoneOn Z (Icc (0:ℝ) 1))
    (hZb:∀u∈Icc (0:ℝ) 1,Z u∈Icc (0:ℝ) 1)
    {dp lp dc lc:ℝ} (hdp:dp≠0) (hlp:0 < lp) (hdc:dc≠0) (hlc:0 < lc)
    (hC:1 ≤ C) (hy:0 < y) (hy4:y ≤ 1/4)
    (ha:0 ≤ start) (hab:start ≤ stop) (hstop:stop ≤ b) (hb:b ≤ finish) (hf:finish ≤ 1)
    (hq:0 ≤ q) (hwidth:q*y ≤ stop-start)
    (hforce:inverseCapPrimitive M 1 ≤ y/4) (hspeed:(M 0)⁻¹ ≤ B^2/A)
    (htravel:b+reciprocalFloorTime A B 1 ≤ finish) (hZsmall:Z finish ≤ y)
    (hRupper:∀u∈Icc (0:ℝ) finish,comparisonSweepQuantile hFloor (reciprocalSquareFloor_continuousOn hB)
      hkc hMm (hMp 1 (by norm_num)).le α u ≤ C*y)
    (hRlarge:∀u∈Icc start stop,4*y ≤ comparisonSweepQuantile hFloor (reciprocalSquareFloor_continuousOn hB)
      hkc hMm (hMp 1 (by norm_num)).le α u) :
    let R:=comparisonSweepQuantile hFloor (reciprocalSquareFloor_continuousOn hB)
      hkc hMm (hMp 1 (by norm_num)).le α
    let t:=(1/C)/100*min 1 (laplaceComparisonStrength dc lc y/laplaceComparisonStrength dp lp y)
    let w:=downwardRampBarrier A B M (2*y) b
    let Rhat:=fun u=>harmonicBarrierRadius B t (R u) (min (R u) (w u))
    ∃γ:inverseIntegralConstraints 0 0 (reciprocalSquareFloor A B) M,
      (∀u∈Icc (0:ℝ) 1,γ.val.val (Rhat u)=u) ∧
      (∀u∈Icc (0:ℝ) 1,w u < R u →
        (R u-Rhat u)/(R u-Z u)∈Ico (0:ℝ)
          (laplaceComparisonStrength dc lc (Z u)/
            (laplaceComparisonStrength dp lp (R u)+laplaceComparisonStrength dc lc (Z u)))) ∧
      (q/(100*C^2))*min (laplaceComparisonStrength dp lp y) (laplaceComparisonStrength dc lc y)*y^3 ≤
        ∫u in (0:ℝ)..1,laplaceComparisonStrength dp lp (R u)*(R u-Rhat u)*(R u-Z u) := by
  let R:=comparisonSweepQuantile hFloor (reciprocalSquareFloor_continuousOn hB)
    hkc hMm (hMp 1 (by norm_num)).le α
  let ey:=laplaceComparisonStrength dp lp y
  let Dy:=laplaceComparisonStrength dc lc y
  let t:=(1/C)/100*min 1 (Dy/ey)
  let w:=downwardRampBarrier A B M (2*y) b
  let v:=fun u=>min (R u) (w u)
  let Rhat:=fun u=>harmonicBarrierRadius B t (R u) (v u)
  have hC0:0 < C:=zero_lt_one.trans_le hC
  have hey:0 < ey:=laplaceComparisonStrength_pos dp hlp y
  have hDy:0 < Dy:=laplaceComparisonStrength_pos dc hlc y
  have ht0:0 ≤ t:=by dsimp [t];positivity
  have ht1:t ≤ 1:=by
    have hh:=mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (Dy/ey)) (show 0 ≤ (1/C)/100 by positivity)
    have hi:1/C ≤ 1:=by simpa only [one_div] using inv_le_one_of_one_le₀ hC
    dsimp [t]
    nlinarith
  have hheight:0 ≤ 2*y:=by positivity
  have hroom:2*y+inverseCapPrimitive M 1 ≤ 1:=by linarith
  have hbI:b∈Icc (0:ℝ) 1:=⟨ha.trans (hab.trans hstop),hb.trans hf⟩
  have hfinish:finish∈Icc (0:ℝ) 1:=⟨hbI.1.trans hb,hf⟩
  have htail:b+reciprocalFloorTime A B 1 ≤ 1:=htravel.trans hf
  obtain ⟨γ,hγ⟩:=explicit_downward_ramp_trial hA hB hFloor ⟨ht0,ht1⟩ hkc hMc hMm hMp
    hheight hroom hbI htail hspeed α
  have hwb:∀u∈Icc (0:ℝ) 1,w u∈Icc (0:ℝ) 1:=
    fun u hu=>downwardRampBarrier_mem (b:=b) hA hB hMc hMm hMp hheight hroom hu
  have hRbounds:∀u∈Icc (0:ℝ) 1,R u∈Icc (0:ℝ) 1:=fun u _=>
    comparisonSweepQuantile_bounds hFloor (reciprocalSquareFloor_continuousOn hB) hkc hMm
      (hMp 1 (by norm_num)).le α u
  have hwlower:∀u∈Icc (0:ℝ) 1,2*y ≤ w u:=by
    intro u hu
    have hh:=native_downward_barrier_base_le (b:=b) hA hB hMc hMm hMp hheight hroom hu
    have hp:=inverseCapPrimitive_nonneg hMc hMm hMp hu
    dsimp only [downwardBarrierBase] at hh
    linarith
  have hactive:∀u∈Icc (0:ℝ) 1,w u < R u →
      u ≤ finish ∧ Z u ≤ y ∧ R u ≤ C*y:=by
    intro u hu huclip
    have huf:u ≤ finish:=by
      by_contra hn
      have hh:=downward_clipped_radius_after hA hB hFloor hkc hMc hMm hMp hheight hroom hbI α hu
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
    exact native_downward_child_fraction hB hC hdp hlp hdc hlc hy (by linarith) (hRbounds u hu)
      (hZb u hu) (hwlower u hu) huclip.le hh.2.2 hh.2.1
  refine ⟨γ,hγ,hmove,?_⟩
  have hRlip:=comparisonSweepQuantile_lipschitzOn hFloor (reciprocalSquareFloor_continuousOn hB) hkc hMm
    (hMp 1 (by norm_num)).le α
  obtain ⟨Cw,hwlip⟩:=downwardRampBarrier_lipschitz (b:=b) hA hB hMc hMm hMp hheight hroom
  have hvlip:=real_min_lipschitzOn hRlip hwlip
  have hvbounds:MapsTo v (Icc (0:ℝ) 1) (Icc (0:ℝ) 1):=by
    intro u hu
    exact ⟨le_min (hRbounds u hu).1 (hwb u hu).1,(min_le_left _ _).trans (hRbounds u hu).2⟩
  obtain ⟨Ch,hhc⟩:=harmonicBarrierRadius_lipschitz hB ⟨ht0,ht1⟩ hRlip hvlip (fun u hu=>hRbounds u hu) hvbounds
  have hzero:∀u∈Icc (0:ℝ) 1,0 ≤ laplaceComparisonStrength dp lp (R u)*(R u-Rhat u)*(R u-Z u):=by
    intro u hu
    by_cases huclip:w u < R u
    · have hh:=hactive u hu huclip
      have hdisp:0 ≤ R u-Rhat u:=by
        dsimp only [Rhat,v]
        rw [min_eq_right huclip.le]
        exact (mul_nonneg ht0 (sub_nonneg.mpr huclip.le)).trans
          (harmonicBarrierRadius_displacement_bounds hB ⟨ht0,ht1⟩ (hwb u hu).1 huclip.le).1
      exact mul_nonneg (mul_nonneg (laplaceComparisonStrength_pos dp hlp (R u)).le hdisp)
        (by linarith [hwlower u hu] : 0 ≤ R u-Z u)
    · have he:Rhat u=R u:=by
        dsimp only [Rhat,v]
        rw [min_eq_left (le_of_not_gt huclip)]
        exact harmonicBarrierRadius_diagonal hB (hRbounds u hu).1
      rw [he,sub_self,mul_zero,zero_mul]
  have hpoint:∀u∈Icc start stop,
      (1/(100*C^2))*min ey Dy*y^2 ≤ laplaceComparisonStrength dp lp (R u)*(R u-Rhat u)*(R u-Z u):=by
    intro u hu
    have huI:u∈Icc (0:ℝ) 1:=⟨ha.trans hu.1,hu.2.trans (hstop.trans (hb.trans hf))⟩
    have hwu:w u ≤ (9/4:ℝ)*y:=by
      have he:=downwardRampBarrier_before hA hB hMc hMm hMp hheight hroom hspeed hbI huI (hu.2.trans hstop)
      have hp:=inverseCapPrimitive_le_total hMc hMm hMp huI
      change w u=downwardBarrierBase M (2*y) u at he
      dsimp only [downwardBarrierBase] at he
      linarith
    have hrl:=hRlarge u hu
    have hclip:w u < R u:=by linarith
    have hh:=hactive u huI hclip
    dsimp only [Rhat,v]
    rw [min_eq_right hclip.le]
    exact native_downward_threshold_gain hB hC hdp hlp hlc hy (by linarith) (hRbounds u huI)
      (hwb u huI).1 (hwlower u huI) hwu hrl hh.2.2 hh.2.1
  have hbudget:=native_downward_interval_gain R Rhat Z (laplaceComparisonStrength dp lp)
    hRlip.continuousOn hhc.continuousOn hZc (laplaceComparisonStrength_contDiff dp lp).continuous
    ha hab (hstop.trans (hb.trans hf)) hzero hpoint
  have hconst:0 ≤ (1/(100*C^2))*min ey Dy*y^2:=by positivity
  have hh:((1/(100*C^2))*min ey Dy*y^2)*(q*y) ≤
      ((1/(100*C^2))*min ey Dy*y^2)*(stop-start):=mul_le_mul_of_nonneg_left hwidth hconst
  have hg:=hh.trans hbudget
  convert hg using 1 <;> ring

end OAI.SKFluctuations.LaplaceWindowFormalization
