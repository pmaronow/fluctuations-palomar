module

public import ComparisonActualShiftedAllMassParentChildCall
public import ComparisonActualShiftedCloseUpwardGain
public import ComparisonActualShiftedCloseDownwardGain
public import ComparisonNativeSuccessfulChildBarrier

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 14000000
theorem comparison_actual_shifted_allmass_upward_close_child_error_lower {n:ℕ} {delta:ℝ}
    (a:ActualShiftedAllMassParentChildCall n delta) {cMove rho y start stop finish q:ℝ}
    (hcMove:0 < cMove) (hcMove1:cMove  ≤  1) (hrho:0 < rho) (hrho1:rho ≤ 1) (hy:0 < y)
    (ha:a.context.s  ≤  start) (hab:start < stop) (hbf:stop  ≤  finish) (hf:finish  ≤  1)
    (hq:0  ≤  q) (hwidth:q*y  ≤  finish-stop)
    (hforce:a.context.r0+inverseCapPrimitive a.context.M 1  ≤  rho*y/4)
    (hspeed:(a.context.M 0)⁻¹+(1-rho/2)*y/(stop-start)  ≤ 
      ((n:ℝ)^(2*delta)*a.context.U)^2/((n:ℝ)^delta*a.context.U^2))
    (hZlarge:y  ≤  a.Z start)
    (hroute:(∀u∈Icc start 1,cMove*y ≤ a.R u) ∨ a.e 0 ≤ a.D y)
    (hRupper:∀u∈Icc stop finish,a.R u  ≤  (1-rho)*y) :
    (cMove*rho^3*q/200)*min (a.e y) (a.D y)*y^3  ≤  4*a.err := by
  let c:=a.context
  have hr0:=c.hr0
  let R:=a.R
  let t:=(cMove*rho)/100*min 1 (a.D y/a.e y)
  let speed:=(1-rho/2)*y/(stop-start)
  let w:=omittedUpwardRampBarrier c.M c.r0 c.s start stop speed
  have hA:0 < (n:ℝ)^delta*c.U^2:=by have hh:=c.hN;have hu:=c.hU;positivity
  have hB:0 < (n:ℝ)^(2*delta)*c.U:=by have hh:=c.hN;have hu:=c.hU;positivity
  have hMc:Continuous c.M:=comparisonCap_continuous _ _ _ _ _ _
  have hMp:∀u∈Icc (0:ℝ) 1,0 < c.M u:=fun u hu=>
    (comparisonCap_first_term c.hN c.hU c.numerics.hL c.hE c.hd.le hu.1).1
  have htrial:∃γ:c.Profile,
      (∀u∈Icc c.s 1,γ.val.val ((1-t)*R u+t*max (R u) (w u))=u) ∧
      (∀u∈Icc c.s 1,R u < w u → t*(w u-R u)/(a.Z u-R u)∈Ico (0:ℝ)
        (a.D (a.Z u)/(a.e (R u)+a.D (a.Z u)))) ∧
      (cMove*rho^3*q/200)*min (a.e y) (a.D y)*y^3  ≤ 
        ∫u in (0:ℝ)..1,a.e (R u)*t*(max (R u) (w u)-R u)*(a.Z u-R u):=by
    exact exists_actual_shifted_upward_close_cubic_gain c.hr0 c.hr1 c.hs hA hB c.hc c.hkc hMc c.hm hMp a.alpha a.Z
      a.child_radius_continuous.continuousOn (a.child_radius_monotone.monotoneOn _)
      (fun u _=>a.child_radius_bounds u) c.hd.ne' a.hlam a.childData.hd.ne' a.hchildLam
      hcMove hcMove1 hrho hrho1 hy ha hab hbf hf hq hwidth hforce hspeed hZlarge hroute hRupper
  obtain ⟨γ,hgraph,hactiveFraction,hgain⟩:=htrial
  let Rhat:=c.R γ
  let trial:=fun u=>(1-t)*R u+t*max (R u) (w u)
  have haI:start∈Icc (0:ℝ) 1:=⟨c.hs.1.trans ha,hab.le.trans (hbf.trans hf)⟩
  have hy1:y  ≤  1:=by linarith [(a.child_radius_bounds start).2]
  have hey:0 < a.e y:=laplaceComparisonStrength_pos c.d a.hlam y
  have hDy:0 < a.D y:=laplaceComparisonStrength_pos a.childRadius a.hchildLam y
  have ht0:0  ≤  t:=by dsimp [t];positivity
  have ht1:t  ≤  1:=by
    have hh:=mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (a.D y/a.e y)) (show 0  ≤  (cMove*rho)/100 by positivity)
    dsimp [t]
    nlinarith
  have hheight:0 < 1-rho/2:=by linarith
  have hspeed0:0  ≤  speed:=by dsimp [speed];positivity
  have hrise:speed*(stop-start)=(1-rho/2)*y:=div_mul_cancel₀ _ (sub_pos.mpr hab).ne'
  have hwBounds:∀u∈Icc c.s 1,w u∈Icc c.r0 1:=by
    intro u hu
    have huI:u∈Icc (0:ℝ) 1:=⟨c.hs.1.trans hu.1,hu.2⟩
    have HH:=upwardRampBarrier_bounds hMc c.hm hMp hab.le hspeed0 huI
    have Hs:=inverseCapPrimitive_nonneg hMc c.hm hMp ⟨c.hs.1,c.hs.2⟩
    have HP:=actual_high_only_inverseCapPrimitive_mono hMc c.hm hMp ⟨c.hs.1,c.hs.2⟩ huI hu.1
    have HRamp:0 ≤ truncatedBarrierRamp start stop u:=(truncatedBarrierRamp_bounds hab.le u).1
    have Hmul:=mul_nonneg hspeed0 HRamp
    have Hup:upwardRampBarrier c.M start stop speed u ≤ inverseCapPrimitive c.M 1+speed*(stop-start):=HH.2
    rw [hrise] at Hup
    dsimp only [w,omittedUpwardRampBarrier]
    constructor
    · dsimp only [upwardRampBarrier]
      linarith
    · nlinarith
  have htrialBounds:∀u∈Icc c.s 1,trial u∈Icc c.r0 1:=by
    intro u hu
    have hR:=omittedSweepQuantile_bounds c.hr1 c.hs c.hc c.hk c.hkc c.hm c.hM a.alpha u
    have hw:=hwBounds u hu
    have hV0:c.r0 ≤ max (R u) (w u):=hR.1.trans (le_max_left _ _)
    have hV1:max (R u) (w u)  ≤  1:=max_le hR.2 hw.2
    have hlo:=add_le_add (mul_le_mul_of_nonneg_left hR.1 (sub_nonneg.mpr ht1)) (mul_le_mul_of_nonneg_left hV0 ht0)
    have hhi:=add_le_add (mul_le_mul_of_nonneg_left hR.2 (sub_nonneg.mpr ht1))
      (mul_le_mul_of_nonneg_left hV1 ht0)
    change c.r0 ≤ trial u ∧ trial u ≤ 1
    dsimp only [trial]
    constructor
    · nlinarith
    · nlinarith
  have heq:∀u∈Icc c.s 1,Rhat u=trial u:=fun u hu=>
    actual_shifted_omitted_trial_quantile_eq c.hr0 c.hr1 c.hs c.hc c.hk c.hkc c.hm c.hM γ trial htrialBounds hgraph hu
  have hgapActive:∀u∈Icc c.s 1,R u < w u → R u < a.Z u:=by
    intro u hu hclip
    have hau:start < u:=by
      by_contra hn
      have hramp:truncatedBarrierRamp start stop u=0:=truncatedBarrierRamp_before (le_of_not_gt hn)
      have hw:w u=c.r0+inverseCapPrimitive c.M u-inverseCapPrimitive c.M c.s:=by
        dsimp only [w,omittedUpwardRampBarrier,upwardRampBarrier]
        rw [hramp,mul_zero]
        ring
      have hcap:c.r0+inverseCapPrimitive c.M u-inverseCapPrimitive c.M c.s  ≤  R u:=
        (actual_shifted_omitted_quantile_cap_envelopes c.hr0 c.hr1 c.hs c.hc c.hk c.hkc hMc c.hm hMp a.alpha hu).1
      rw [hw] at hclip
      exact (not_lt_of_ge hcap) hclip
    have hz:y  ≤  a.Z u:=hZlarge.trans (a.child_radius_monotone (hau.le))
    have hw:w u  ≤  (1-rho/4)*y:=by
      have hh:=upwardRampBarrier_bounds hMc c.hm hMp hab.le hspeed0 ⟨c.hs.1.trans hu.1,hu.2⟩
      have HH:upwardRampBarrier c.M start stop speed u ≤ inverseCapPrimitive c.M 1+speed*(stop-start):=hh.2
      have Hs:=inverseCapPrimitive_nonneg hMc c.hm hMp ⟨c.hs.1,c.hs.2⟩
      rw [hrise] at HH
      dsimp only [w,omittedUpwardRampBarrier]
      nlinarith
    nlinarith [mul_pos hrho hy]
  have hgap:∀u∈Icc c.s 1,Rhat u≠R u → a.Z u≠R u:=by
    intro u hu hneq
    have hclip:R u < w u:=by
      by_contra hn
      have hh:=heq u hu
      dsimp only [trial] at hh
      rw [max_eq_left (le_of_not_gt hn)] at hh
      apply hneq
      nlinarith
    exact (hgapActive u hu hclip).ne'
  have hfraction:∀u∈Icc c.s 1,(Rhat u-R u)/(a.Z u-R u)∈Ico (0:ℝ)
      (a.D (a.Z u)/(a.e (R u)+a.D (a.Z u))):=by
    intro u hu
    rw [heq u hu]
    by_cases hclip:R u < w u
    · have hh:=hactiveFraction u hu hclip
      have hd:trial u-R u=t*(w u-R u):=by dsimp [trial];rw [max_eq_right hclip.le];ring
      rw [hd]
      exact hh
    · have hd:trial u-R u=0:=by dsimp [trial];rw [max_eq_left (le_of_not_gt hclip)];ring
      rw [hd,zero_div]
      exact ⟨le_rfl,div_pos (laplaceComparisonStrength_pos _ a.hchildLam _)
        (add_pos (laplaceComparisonStrength_pos _ a.hlam _) (laplaceComparisonStrength_pos _ a.hchildLam _))⟩
  have hupper:=a.optimizer_movement_gain γ hgap hfraction
  have hint:(∫u in (0:ℝ)..1,a.coefficient u*(Rhat u-R u)*(a.Z u-R u))=
      ∫u in (0:ℝ)..1,a.e (R u)*t*(max (R u) (w u)-R u)*(a.Z u-R u):=by
    apply intervalIntegral.integral_congr
    intro u hu
    have huI:u∈Icc (0:ℝ) 1:=by simpa only [uIcc_of_le zero_le_one] using hu
    dsimp only
    by_cases HS:c.s ≤ u
    · rw [a.high_coefficient HS,heq u ⟨HS,huI.2⟩]
      dsimp only [trial]
      ring
    · have HR:R u=c.r0:=c.radius_before a.alpha (not_le.mp HS).le
      have HP:=actual_high_only_inverseCapPrimitive_mono hMc c.hm hMp huI ⟨c.hs.1,c.hs.2⟩ (not_le.mp HS).le
      have HRamp:truncatedBarrierRamp start stop u=0:=truncatedBarrierRamp_before ((not_le.mp HS).le.trans ha)
      have Hw:w u ≤ c.r0:=by
        dsimp only [w,omittedUpwardRampBarrier,upwardRampBarrier]
        rw [HRamp,mul_zero]
        linarith
      rw [a.low_coefficient (not_le.mp HS),zero_mul,zero_mul,HR,max_eq_left Hw,sub_self,mul_zero,zero_mul]
  exact hgain.trans (by rwa [←hint])

theorem comparison_actual_shifted_allmass_downward_close_child_error_lower {n:ℕ} {delta:ℝ}
    (a:ActualShiftedAllMassParentChildCall n delta) {C rho y start stop departure finish q:ℝ}
    (hC:1  ≤  C) (hrho:0 < rho) (hrho1:rho ≤ 1) (hy:0 < y) (hy1:y ≤ 1)
    (ha:a.context.s  ≤  start) (hab:start  ≤  stop) (hstop:stop  ≤  departure) (hb:departure  ≤  finish) (hf:finish  ≤  1)
    (hq:0  ≤  q) (hwidth:q*y  ≤  stop-start)
    (hforce:a.context.r0+inverseCapPrimitive a.context.M 1  ≤  rho*y/4)
    (hspeed:(a.context.M 0)⁻¹  ≤ 
      ((n:ℝ)^(2*delta)*a.context.U)^2/((n:ℝ)^delta*a.context.U^2))
    (htravel:departure+reciprocalFloorTime ((n:ℝ)^delta*a.context.U^2)
      ((n:ℝ)^(2*delta)*a.context.U) 1  ≤  finish)
    (hZsmall:a.Z finish  ≤  (1-rho)*y)
    (hRupper:∀u∈Icc (0:ℝ) finish,a.R u  ≤  C*y)
    (hRlarge:∀u∈Icc start stop,y  ≤  a.R u) :
    (q*rho^2/(400*C^2))*min (a.e y) (a.D y)*y^3  ≤  4*a.err := by
  let c:=a.context
  have hr0:=c.hr0
  let R:=a.R
  let A:=(n:ℝ)^delta*c.U^2
  let B:=(n:ℝ)^(2*delta)*c.U
  let t:=(1/C)/100*min 1 (a.D y/a.e y)
  let w:=downwardRampBarrier A B c.M ((1-rho/2)*y) departure
  let v:=fun u=>min (R u) (w u)
  let trial:=fun u=>harmonicBarrierRadius B t (R u) (v u)
  have hA:0 < A:=by have hh:=c.hN;have hu:=c.hU;dsimp [A];positivity
  have hB:0 < B:=by have hh:=c.hN;have hu:=c.hU;dsimp [B];positivity
  have hMc:Continuous c.M:=comparisonCap_continuous _ _ _ _ _ _
  have hMp:∀u∈Icc (0:ℝ) 1,0 < c.M u:=fun u hu=>
    (comparisonCap_first_term c.hN c.hU c.numerics.hL c.hE c.hd.le hu.1).1
  obtain ⟨γ,hgraph,hmove,hgain⟩:=exists_actual_shifted_downward_close_cubic_gain c.hr0 c.hr1 c.hs hA hB c.hc c.hkc hMc c.hm hMp
    a.alpha a.Z a.child_radius_continuous.continuousOn (a.child_radius_monotone.monotoneOn _)
    (fun u _=>a.child_radius_bounds u) c.hd.ne' a.hlam a.childData.hd.ne' a.hchildLam
    hC hrho hrho1 hy hy1 ha hab hstop hb hf hq hwidth hforce hspeed htravel hZsmall hRupper hRlarge
  let Rhat:=c.R γ
  have hC0:0 < C:=zero_lt_one.trans_le hC
  have hey:0 < a.e y:=laplaceComparisonStrength_pos c.d a.hlam y
  have hDy:0 < a.D y:=laplaceComparisonStrength_pos a.childRadius a.hchildLam y
  have ht0:0  ≤  t:=by dsimp [t];positivity
  have ht1:t  ≤  1:=by
    have hh:=mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (a.D y/a.e y)) (show 0  ≤  (1/C)/100 by positivity)
    have hi:1/C  ≤  1:=by simpa only [one_div] using inv_le_one_of_one_le₀ hC
    dsimp [t]
    nlinarith
  have hheight:0 ≤ (1-rho/2)*y:=mul_nonneg (by linarith) hy.le
  have hheightOrigin:c.r0 ≤ (1-rho/2)*y:=by
    have HP:=inverseCapPrimitive_nonneg hMc c.hm hMp ⟨zero_le_one,le_rfl⟩
    nlinarith
  have hroom:(1-rho/2)*y+inverseCapPrimitive c.M 1 ≤ 1:=by nlinarith
  have hdeparture:departure∈Icc (0:ℝ) 1:=⟨c.hs.1.trans (ha.trans (hab.trans hstop)),hb.trans hf⟩
  have hfinish:finish∈Icc (0:ℝ) 1:=⟨hdeparture.1.trans hb,hf⟩
  have hRBounds:∀u∈Icc (0:ℝ) 1,R u∈Icc c.r0 1:=fun u _=>
    omittedSweepQuantile_bounds c.hr1 c.hs c.hc c.hk c.hkc c.hm c.hM a.alpha u
  have hwBounds:∀u∈Icc (0:ℝ) 1,w u∈Icc c.r0 1:=fun u hu=>
    ⟨hheightOrigin.trans (downwardRampBarrier_ge_height hA hB hMc c.hm hMp hheight hroom hu),
      (downwardRampBarrier_mem (b:=departure) hA hB hMc c.hm hMp hheight hroom hu).2⟩
  have htrialBounds:∀u∈Icc (0:ℝ) 1,trial u∈Icc c.r0 1:=by
    intro u hu
    have hv:v u∈Icc c.r0 1:=⟨le_min (hRBounds u hu).1 (hwBounds u hu).1,
      (min_le_left _ _).trans (hRBounds u hu).2⟩
    exact harmonicBarrierRadius_mem_wall c.hr0 hB ⟨ht0,ht1⟩ (hRBounds u hu) hv
  have heq:∀u∈Icc (0:ℝ) 1,Rhat u=trial u:=by
    intro u hu
    by_cases HS:c.s ≤ u
    · exact actual_shifted_omitted_trial_quantile_eq c.hr0 c.hr1 c.hs c.hc c.hk c.hkc c.hm c.hM γ trial
        (fun u hu=>htrialBounds u ⟨c.hs.1.trans hu.1,hu.2⟩) hgraph ⟨HS,hu.2⟩
    · have HR:R u=c.r0:=c.radius_before a.alpha (not_le.mp HS).le
      have HRhat:Rhat u=c.r0:=c.radius_before γ (not_le.mp HS).le
      have Htrial:trial u=c.r0:=by
        dsimp only [trial,v]
        rw [HR,min_eq_left (hwBounds u hu).1]
        exact harmonicBarrierRadius_diagonal hB c.hr0
      rw [HRhat,Htrial]
  have hwlower:∀u∈Icc (0:ℝ) 1,(1-rho/2)*y  ≤  w u:=by
    intro u hu
    have hh:=native_downward_barrier_base_le (b:=departure) hA hB hMc c.hm hMp hheight hroom hu
    have hp:=inverseCapPrimitive_nonneg hMc c.hm hMp hu
    dsimp only [downwardBarrierBase] at hh
    linarith
  have hactiveGap:∀u∈Icc (0:ℝ) 1,w u < R u → a.Z u < R u:=by
    intro u hu hclip
    have huf:u  ≤  finish:=by
      by_contra hn
      have Hs:c.s ≤ u:=ha.trans (hab.trans (hstop.trans (hb.trans (lt_of_not_ge hn).le)))
      have hh:=actual_shifted_downward_clipped_radius_after c.hr0 c.hr1 c.hs hA hB c.hc c.hkc hMc c.hm hMp hheight hroom hdeparture a.alpha ⟨Hs,hu.2⟩
        (htravel.trans (lt_of_not_ge hn).le)
      change min (R u) (w u)=R u at hh
      rw [min_eq_right hclip.le] at hh
      linarith
    have hZ:a.Z u  ≤  (1-rho)*y:=(a.child_radius_monotone huf).trans hZsmall
    nlinarith [hwlower u hu, mul_pos hrho hy]
  have hinactive:∀u∈Icc (0:ℝ) 1,¬w u < R u → Rhat u=R u:=by
    intro u hu hn
    rw [heq u hu]
    dsimp only [trial,v]
    rw [min_eq_left (le_of_not_gt hn)]
    exact harmonicBarrierRadius_diagonal hB (c.hr0.trans (hRBounds u hu).1)
  have hgap:∀u∈Icc (0:ℝ) 1,Rhat u≠R u → a.Z u≠R u:=by
    intro u hu hn
    have hclip:w u < R u:=by
      by_contra hc
      exact hn (hinactive u hu hc)
    exact (hactiveGap u hu hclip).ne
  have hfraction:∀u∈Icc (0:ℝ) 1,(Rhat u-R u)/(a.Z u-R u)∈Ico (0:ℝ)
      (a.D (a.Z u)/(a.e (R u)+a.D (a.Z u))):=by
    intro u hu
    by_cases hclip:w u < R u
    · rw [native_opposite_difference_ratio,heq u hu]
      exact hmove u hu hclip
    · rw [hinactive u hu hclip,sub_self,zero_div]
      exact ⟨le_rfl,div_pos (laplaceComparisonStrength_pos _ a.hchildLam _)
        (add_pos (laplaceComparisonStrength_pos _ a.hlam _) (laplaceComparisonStrength_pos _ a.hchildLam _))⟩
  have hupper:=a.optimizer_movement_gain γ
    (fun u hu=>hgap u ⟨c.hs.1.trans hu.1,hu.2⟩)
    (fun u hu=>hfraction u ⟨c.hs.1.trans hu.1,hu.2⟩)
  have hint:(∫u in (0:ℝ)..1,a.coefficient u*(Rhat u-R u)*(a.Z u-R u))=
      ∫u in (0:ℝ)..1,a.e (R u)*(R u-trial u)*(R u-a.Z u):=by
    apply intervalIntegral.integral_congr
    intro u hu
    have huI:u∈Icc (0:ℝ) 1:=by simpa only [uIcc_of_le zero_le_one] using hu
    dsimp only
    by_cases HS:c.s ≤ u
    · rw [a.high_coefficient HS,heq u huI]
      ring
    · have HR:R u=c.r0:=c.radius_before a.alpha (not_le.mp HS).le
      have Htrial:trial u=c.r0:=by
        dsimp only [trial,v]
        rw [HR,min_eq_left (hwBounds u huI).1]
        exact harmonicBarrierRadius_diagonal hB c.hr0
      rw [a.low_coefficient (not_le.mp HS),zero_mul,zero_mul,HR,Htrial,sub_self,mul_zero,zero_mul]
  change (q*rho^2/(400*C^2))*min (a.e y) (a.D y)*y^3  ≤ 
    ∫u in (0:ℝ)..1,a.e (R u)*(R u-trial u)*(R u-a.Z u) at hgain
  change (∫u in (0:ℝ)..1,a.coefficient u*(Rhat u-R u)*(a.Z u-R u))  ≤  4*a.err at hupper
  rw [hint] at hupper
  exact hgain.trans hupper

end OAI.SKFluctuations.LaplaceWindowFormalization
