module

public import ComparisonNativeUpwardSmallParentCubicGain
public import ComparisonNativeDownwardChildCubicGain
public import ComparisonNativeChildOptimizerMovement
public import ComparisonNativeChildRampRoom
public import ComparisonNativeChildGainSaving

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 9000000

structure NativeChildBarrierParameters (n:ℕ) (delta:ℝ) where
  E:ℝ
  d:ℝ
  hn:0 < n
  hE:0 < E
  hd:0 < d

namespace NativeChildBarrierParameters
abbrev N {n:ℕ} {delta:ℝ} (c:NativeChildBarrierParameters n delta):=(n:ℝ)
abbrev U {n:ℕ} {delta:ℝ} (c:NativeChildBarrierParameters n delta):=comparisonSmallMass c.N c.E
abbrev L {n:ℕ} {delta:ℝ} (c:NativeChildBarrierParameters n delta):=comparisonConstraintLength c.N c.E c.d
abbrev k {n:ℕ} {delta:ℝ} (c:NativeChildBarrierParameters n delta):=comparisonFloor c.N delta c.U
abbrev M {n:ℕ} {delta:ℝ} (c:NativeChildBarrierParameters n delta):=comparisonCap c.N delta c.U c.L c.E c.d
abbrev floor {n:ℕ} {delta:ℝ} (c:NativeChildBarrierParameters n delta):=c.k 1
theorem hN {n:ℕ} {delta:ℝ} (c:NativeChildBarrierParameters n delta):0 < c.N:=by exact_mod_cast c.hn
theorem hU {n:ℕ} {delta:ℝ} (c:NativeChildBarrierParameters n delta):0 < c.U:=comparisonSmallMass_pos c.hN c.hE
theorem hL {n:ℕ} {delta:ℝ} (c:NativeChildBarrierParameters n delta):0 < c.L:=comparisonConstraintLength_pos c.hN c.hE c.hd
theorem hc {n:ℕ} {delta:ℝ} (c:NativeChildBarrierParameters n delta):0 < c.floor:=comparisonFloor_pos c.hN c.hU (by norm_num)
theorem hk {n:ℕ} {delta:ℝ} (c:NativeChildBarrierParameters n delta):ContinuousOn c.k (Icc (0:ℝ) 1):=comparisonFloor_continuousOn c.hN c.hU le_rfl
theorem hkc {n:ℕ} {delta:ℝ} (c:NativeChildBarrierParameters n delta):∀r∈Icc (0:ℝ) 1,c.floor ≤ c.k r:=fun r hr=>comparisonFloor_lower_on c.hN c.hU le_rfl hr
theorem hm {n:ℕ} {delta:ℝ} (c:NativeChildBarrierParameters n delta):MonotoneOn c.M (Icc (0:ℝ) 1):=comparisonCap_monotoneOn c.hN c.hU.le c.hL c.hE c.hd.le
theorem hM {n:ℕ} {delta:ℝ} (c:NativeChildBarrierParameters n delta):0 ≤ c.M 1:=comparisonCap_nonneg c.hN c.hU.le c.hL c.hE c.hd.le zero_le_one
abbrev Profile {n:ℕ} {delta:ℝ} (c:NativeChildBarrierParameters n delta):=inverseIntegralConstraints 0 0 c.k c.M
abbrev R {n:ℕ} {delta:ℝ} (c:NativeChildBarrierParameters n delta) (α:c.Profile):=comparisonSweepQuantile c.hc c.hk c.hkc c.hm c.hM α
end NativeChildBarrierParameters

structure NativeChildBarrierCall (n:ℕ) (delta:ℝ) where
  context:NativeChildBarrierParameters n delta
  lam:ℝ
  childRadius:ℝ
  childLam:ℝ
  hlam:0 < lam
  hchildRadius:childRadius≠0
  hchildLam:0 < childLam
  alpha:context.Profile
  b:ℝ → ℝ
  h:ℝ → ℝ
  Z:ℝ → ℝ
  hb:MonotoneOn b (Icc (0:ℝ) 1)
  hh:MonotoneOn h (Icc (0:ℝ) 1)
  hh0:0 ≤ h 0
  matrixRoom:lam+childLam ≤ b 0
  hZc:ContinuousOn Z (Icc (0:ℝ) 1)
  hZm:MonotoneOn Z (Icc (0:ℝ) 1)
  hZb:∀u∈Icc (0:ℝ) 1,Z u∈Icc (0:ℝ) 1
  minimum:∀β:context.Profile,
    comparisonVariableEndpointObjective context.hc context.hk context.hkc context.hm context.hM
      n b h context.d lam alpha ≤
    comparisonVariableEndpointObjective context.hc context.hk context.hkc context.hm context.hM
      n b h context.d lam β
  err:ℝ
  childSuccess:pathCompensatedPressure n
    (fun u=>b u-laplaceComparisonStrength context.d lam (context.R alpha u))
    (fun u=>h u+laplaceComparisonStrength context.d lam (context.R alpha u)*context.R alpha u)
    (fun u=>laplaceComparisonStrength childRadius childLam (Z u)) Z 0 ≤
    realOrderedSKPathPressure n
      (fun u=>b u-laplaceComparisonStrength context.d lam (context.R alpha u))
      (fun u=>h u+laplaceComparisonStrength context.d lam (context.R alpha u)*context.R alpha u) 0+err

namespace NativeChildBarrierCall
abbrev R {n:ℕ} {delta:ℝ} (a:NativeChildBarrierCall n delta) := a.context.R a.alpha
abbrev e {n:ℕ} {delta:ℝ} (a:NativeChildBarrierCall n delta) := laplaceComparisonStrength a.context.d a.lam
abbrev D {n:ℕ} {delta:ℝ} (a:NativeChildBarrierCall n delta) := laplaceComparisonStrength a.childRadius a.childLam
end NativeChildBarrierCall

theorem comparison_native_upward_successful_child_error_lower {n:ℕ} {delta:ℝ}
    (a:NativeChildBarrierCall n delta) {cMove y start stop finish q:ℝ}
    (hcMove:0 < cMove) (hcMove1:cMove ≤ 1) (hy:0 < y)
    (ha:0 ≤ start) (hab:start < stop) (hbf:stop ≤ finish) (hf:finish ≤ 1)
    (hq:0 ≤ q) (hwidth:q*y ≤ finish-stop)
    (hforce:inverseCapPrimitive a.context.M 1 ≤ y/4)
    (hspeed:(a.context.M 0)⁻¹+2*y/(stop-start) ≤
      ((n:ℝ)^(2*delta)*a.context.U)^2/((n:ℝ)^delta*a.context.U^2))
    (hZlarge:4*y ≤ a.Z start)
    (hroute:(∀u∈Icc start 1,cMove*y ≤ a.R u) ∨ a.e 0 ≤ a.D y)
    (hRupper:∀u∈Icc stop finish,a.R u ≤ y) :
    (3*cMove*q/100)*min (a.e y) (a.D y)*y^3 ≤ 4*a.err := by
  let c:=a.context
  let R:=a.R
  let t:=cMove/100*min 1 (a.D y/a.e y)
  let speed:=2*y/(stop-start)
  let w:=upwardRampBarrier c.M start stop speed
  have hA:0 < (n:ℝ)^delta*c.U^2:=by have hh:=c.hN;have hu:=c.hU;positivity
  have hB:0 < (n:ℝ)^(2*delta)*c.U:=by have hh:=c.hN;have hu:=c.hU;positivity
  have hMc:Continuous c.M:=comparisonCap_continuous _ _ _ _ _ _
  have hMp:∀u∈Icc (0:ℝ) 1,0 < c.M u:=fun u hu=>
    (comparisonCap_first_term c.hN c.hU c.hL c.hE c.hd.le hu.1).1
  have htrial:∃γ:c.Profile,
      (∀u∈Icc (0:ℝ) 1,γ.val.val ((1-t)*R u+t*max (R u) (w u))=u) ∧
      (∀u∈Icc (0:ℝ) 1,R u < w u → t*(w u-R u)/(a.Z u-R u)∈Ico (0:ℝ)
        (a.D (a.Z u)/(a.e (R u)+a.D (a.Z u)))) ∧
      (3*cMove*q/100)*min (a.e y) (a.D y)*y^3 ≤
        ∫u in (0:ℝ)..1,a.e (R u)*t*(max (R u) (w u)-R u)*(a.Z u-R u):=by
    rcases hroute with houter|hsmall
    · exact exists_native_upward_child_cubic_gain hA hB c.hc c.hkc hMc c.hm hMp a.alpha a.Z
        a.hZc a.hZm a.hZb c.hd.ne' a.hlam a.hchildRadius a.hchildLam hcMove hcMove1 hy ha hab hbf hf
        hq hwidth hforce hspeed hZlarge houter hRupper
    · exact exists_native_upward_small_parent_cubic_gain hA hB c.hc c.hkc hMc c.hm hMp a.alpha a.Z
        a.hZc a.hZm a.hZb c.hd.ne' a.hlam a.hchildRadius a.hchildLam hcMove hcMove1 hy ha hab hbf hf
        hq hwidth hforce hspeed hZlarge hsmall hRupper
  obtain ⟨γ,hgraph,hactiveFraction,hgain⟩:=htrial
  let Rhat:=c.R γ
  let trial:=fun u=>(1-t)*R u+t*max (R u) (w u)
  have haI:start∈Icc (0:ℝ) 1:=⟨ha,hab.le.trans (hbf.trans hf)⟩
  have hy4:y ≤ 1/4:=by linarith [(a.hZb start haI).2]
  have hey:0 < a.e y:=laplaceComparisonStrength_pos c.d a.hlam y
  have hDy:0 < a.D y:=laplaceComparisonStrength_pos a.childRadius a.hchildLam y
  have ht0:0 ≤ t:=by dsimp [t];positivity
  have ht1:t ≤ 1:=by
    have hh:=mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (a.D y/a.e y)) (show 0 ≤ cMove/100 by positivity)
    dsimp [t]
    nlinarith
  have hspeed0:0 ≤ speed:=by dsimp [speed];positivity
  have hrise:speed*(stop-start)=2*y:=div_mul_cancel₀ _ (sub_pos.mpr hab).ne'
  have hwBounds:∀u∈Icc (0:ℝ) 1,w u∈Icc (0:ℝ) 1:=by
    intro u hu
    have hh:=upwardRampBarrier_bounds hMc c.hm hMp hab.le hspeed0 hu
    change 0 ≤ w u ∧ w u ≤ inverseCapPrimitive c.M 1+speed*(stop-start) at hh
    exact ⟨hh.1,by rw [hrise] at hh;linarith [hh.2]⟩
  have htrialBounds:∀u∈Icc (0:ℝ) 1,trial u∈Icc (0:ℝ) 1:=by
    intro u hu
    have hR:=comparisonSweepQuantile_bounds c.hc c.hk c.hkc c.hm c.hM a.alpha u
    have hw:=hwBounds u hu
    have hV0:0 ≤ max (R u) (w u):=hR.1.trans (le_max_left _ _)
    have hV1:max (R u) (w u) ≤ 1:=max_le hR.2 hw.2
    have hlo:=add_nonneg (mul_nonneg (sub_nonneg.mpr ht1) hR.1) (mul_nonneg ht0 hV0)
    have hhi:=add_le_add (mul_le_mul_of_nonneg_left hR.2 (sub_nonneg.mpr ht1))
      (mul_le_mul_of_nonneg_left hV1 ht0)
    change 0 ≤ trial u ∧ trial u ≤ 1
    dsimp only [trial]
    constructor
    · exact hlo
    · nlinarith
  have heq:∀u∈Icc (0:ℝ) 1,Rhat u=trial u:=fun u hu=>
    comparison_native_trial_quantile_eq c.hc c.hk c.hkc c.hm c.hM γ trial htrialBounds hgraph hu
  have hgapActive:∀u∈Icc (0:ℝ) 1,R u < w u → R u < a.Z u:=by
    intro u hu hclip
    have hau:start < u:=by
      by_contra hn
      have hramp:truncatedBarrierRamp start stop u=0:=truncatedBarrierRamp_before (le_of_not_gt hn)
      have hw:w u=inverseCapPrimitive c.M u:=by simp only [w,upwardRampBarrier,hramp,mul_zero,add_zero]
      have hcap:inverseCapPrimitive c.M u ≤ R u:=
        (comparisonSweepQuantile_cap_envelopes c.hc c.hk c.hkc hMc c.hm hMp a.alpha hu).1
      rw [hw] at hclip
      exact (not_lt_of_ge hcap) hclip
    have hz:4*y ≤ a.Z u:=hZlarge.trans (a.hZm haI hu hau.le)
    have hw:w u ≤ (9/4:ℝ)*y:=by
      have hh:=upwardRampBarrier_bounds hMc c.hm hMp hab.le hspeed0 hu
      have hh':w u ≤ inverseCapPrimitive c.M 1+speed*(stop-start):=hh.2
      rw [hrise] at hh'
      linarith
    linarith
  have hgap:∀u∈Icc (0:ℝ) 1,Rhat u≠R u → a.Z u≠R u:=by
    intro u hu hneq
    have hclip:R u < w u:=by
      by_contra hn
      have hh:=heq u hu
      dsimp only [trial] at hh
      rw [max_eq_left (le_of_not_gt hn)] at hh
      apply hneq
      nlinarith
    exact (hgapActive u hu hclip).ne'
  have hfraction:∀u∈Icc (0:ℝ) 1,(Rhat u-R u)/(a.Z u-R u)∈Ico (0:ℝ)
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
  have hupper:=comparison_native_actual_optimizer_movement_gain c.hc c.hk c.hkc c.hm c.hM n c.hn
    a.alpha γ a.b a.h a.Z c.hd.ne' a.hlam a.hchildRadius a.hchildLam a.hb a.hh a.matrixRoom a.hh0
    a.hZc a.hZm a.hZb a.minimum hgap hfraction a.childSuccess
  have hint:(∫u in (0:ℝ)..1,a.e (R u)*(Rhat u-R u)*(a.Z u-R u))=
      ∫u in (0:ℝ)..1,a.e (R u)*t*(max (R u) (w u)-R u)*(a.Z u-R u):=by
    apply intervalIntegral.integral_congr
    intro u hu
    have huI:u∈Icc (0:ℝ) 1:=by simpa only [uIcc_of_le zero_le_one] using hu
    dsimp only
    rw [heq u huI]
    dsimp only [trial]
    ring
  exact hgain.trans (by rwa [←hint])

theorem native_opposite_difference_ratio (a b c:ℝ):
    (a-b)/(c-b)=(b-a)/(b-c):=by
  rw [show a-b=-(b-a) by ring,show c-b=-(b-c) by ring,neg_div_neg_eq]

theorem comparison_native_downward_successful_child_error_lower {n:ℕ} {delta:ℝ}
    (a:NativeChildBarrierCall n delta) {C y start stop departure finish q:ℝ}
    (hC:1 ≤ C) (hy:0 < y) (hy4:y ≤ 1/4)
    (ha:0 ≤ start) (hab:start ≤ stop) (hstop:stop ≤ departure) (hb:departure ≤ finish) (hf:finish ≤ 1)
    (hq:0 ≤ q) (hwidth:q*y ≤ stop-start)
    (hforce:inverseCapPrimitive a.context.M 1 ≤ y/4)
    (hspeed:(a.context.M 0)⁻¹ ≤
      ((n:ℝ)^(2*delta)*a.context.U)^2/((n:ℝ)^delta*a.context.U^2))
    (htravel:departure+reciprocalFloorTime ((n:ℝ)^delta*a.context.U^2)
      ((n:ℝ)^(2*delta)*a.context.U) 1 ≤ finish)
    (hZsmall:a.Z finish ≤ y)
    (hRupper:∀u∈Icc (0:ℝ) finish,a.R u ≤ C*y)
    (hRlarge:∀u∈Icc start stop,4*y ≤ a.R u) :
    (q/(100*C^2))*min (a.e y) (a.D y)*y^3 ≤ 4*a.err := by
  let c:=a.context
  let R:=a.R
  let A:=(n:ℝ)^delta*c.U^2
  let B:=(n:ℝ)^(2*delta)*c.U
  let t:=(1/C)/100*min 1 (a.D y/a.e y)
  let w:=downwardRampBarrier A B c.M (2*y) departure
  let v:=fun u=>min (R u) (w u)
  let trial:=fun u=>harmonicBarrierRadius B t (R u) (v u)
  have hA:0 < A:=by have hh:=c.hN;have hu:=c.hU;dsimp [A];positivity
  have hB:0 < B:=by have hh:=c.hN;have hu:=c.hU;dsimp [B];positivity
  have hMc:Continuous c.M:=comparisonCap_continuous _ _ _ _ _ _
  have hMp:∀u∈Icc (0:ℝ) 1,0 < c.M u:=fun u hu=>
    (comparisonCap_first_term c.hN c.hU c.hL c.hE c.hd.le hu.1).1
  obtain ⟨γ,hgraph,hmove,hgain⟩:=exists_native_downward_child_cubic_gain hA hB c.hc c.hkc hMc c.hm hMp
    a.alpha a.Z a.hZc a.hZm a.hZb c.hd.ne' a.hlam a.hchildRadius a.hchildLam
    hC hy hy4 ha hab hstop hb hf hq hwidth hforce hspeed htravel hZsmall hRupper hRlarge
  let Rhat:=c.R γ
  have hC0:0 < C:=zero_lt_one.trans_le hC
  have hey:0 < a.e y:=laplaceComparisonStrength_pos c.d a.hlam y
  have hDy:0 < a.D y:=laplaceComparisonStrength_pos a.childRadius a.hchildLam y
  have ht0:0 ≤ t:=by dsimp [t];positivity
  have ht1:t ≤ 1:=by
    have hh:=mul_le_mul_of_nonneg_left (min_le_left (1:ℝ) (a.D y/a.e y)) (show 0 ≤ (1/C)/100 by positivity)
    have hi:1/C ≤ 1:=by simpa only [one_div] using inv_le_one_of_one_le₀ hC
    dsimp [t]
    nlinarith
  have hheight:0 ≤ 2*y:=by positivity
  have hroom:2*y+inverseCapPrimitive c.M 1 ≤ 1:=by linarith
  have hdeparture:departure∈Icc (0:ℝ) 1:=⟨ha.trans (hab.trans hstop),hb.trans hf⟩
  have hfinish:finish∈Icc (0:ℝ) 1:=⟨hdeparture.1.trans hb,hf⟩
  have hRBounds:∀u∈Icc (0:ℝ) 1,R u∈Icc (0:ℝ) 1:=fun u _=>
    comparisonSweepQuantile_bounds c.hc c.hk c.hkc c.hm c.hM a.alpha u
  have hwBounds:∀u∈Icc (0:ℝ) 1,w u∈Icc (0:ℝ) 1:=fun u hu=>
    downwardRampBarrier_mem (b:=departure) hA hB hMc c.hm hMp hheight hroom hu
  have htrialBounds:∀u∈Icc (0:ℝ) 1,trial u∈Icc (0:ℝ) 1:=by
    intro u hu
    have hv:v u∈Icc (0:ℝ) 1:=⟨le_min (hRBounds u hu).1 (hwBounds u hu).1,
      (min_le_left _ _).trans (hRBounds u hu).2⟩
    exact harmonicBarrierRadius_mem hB ⟨ht0,ht1⟩ (hRBounds u hu) hv
  have heq:∀u∈Icc (0:ℝ) 1,Rhat u=trial u:=fun u hu=>
    comparison_native_trial_quantile_eq c.hc c.hk c.hkc c.hm c.hM γ trial htrialBounds hgraph hu
  have hwlower:∀u∈Icc (0:ℝ) 1,2*y ≤ w u:=by
    intro u hu
    have hh:=native_downward_barrier_base_le (b:=departure) hA hB hMc c.hm hMp hheight hroom hu
    have hp:=inverseCapPrimitive_nonneg hMc c.hm hMp hu
    dsimp only [downwardBarrierBase] at hh
    linarith
  have hactiveGap:∀u∈Icc (0:ℝ) 1,w u < R u → a.Z u < R u:=by
    intro u hu hclip
    have huf:u ≤ finish:=by
      by_contra hn
      have hh:=downward_clipped_radius_after hA hB c.hc c.hkc hMc c.hm hMp hheight hroom hdeparture a.alpha hu
        (htravel.trans (lt_of_not_ge hn).le)
      change min (R u) (w u)=R u at hh
      rw [min_eq_right hclip.le] at hh
      linarith
    have hZ:a.Z u ≤ y:=(a.hZm hu hfinish huf).trans hZsmall
    linarith [hwlower u hu]
  have hinactive:∀u∈Icc (0:ℝ) 1,¬w u < R u → Rhat u=R u:=by
    intro u hu hn
    rw [heq u hu]
    dsimp only [trial,v]
    rw [min_eq_left (le_of_not_gt hn)]
    exact harmonicBarrierRadius_diagonal hB (hRBounds u hu).1
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
  have hupper:=comparison_native_actual_optimizer_movement_gain c.hc c.hk c.hkc c.hm c.hM n c.hn
    a.alpha γ a.b a.h a.Z c.hd.ne' a.hlam a.hchildRadius a.hchildLam a.hb a.hh a.matrixRoom a.hh0
    a.hZc a.hZm a.hZb a.minimum hgap hfraction a.childSuccess
  have hint:(∫u in (0:ℝ)..1,a.e (R u)*(Rhat u-R u)*(a.Z u-R u))=
      ∫u in (0:ℝ)..1,a.e (R u)*(R u-trial u)*(R u-a.Z u):=by
    apply intervalIntegral.integral_congr
    intro u hu
    have huI:u∈Icc (0:ℝ) 1:=by simpa only [uIcc_of_le zero_le_one] using hu
    dsimp only
    rw [heq u huI]
    ring
  change (q/(100*C^2))*min (a.e y) (a.D y)*y^3 ≤
    ∫u in (0:ℝ)..1,a.e (R u)*(R u-trial u)*(R u-a.Z u) at hgain
  change (∫u in (0:ℝ)..1,a.e (R u)*(Rhat u-R u)*(a.Z u-R u)) ≤ 4*a.err at hupper
  rw [hint] at hupper
  exact hgain.trans hupper

theorem eventually_comparison_native_child_excludes_upward_separation
    {delta gamma Dbound m c0 cScale cMove qRamp qBand:ℝ}
    (hdelta:0 < delta) (hgamma:0 < gamma) (hm:0 < m) (hc0:0 < c0)
    (hcScale:0 < cScale) (hcScale1:cScale ≤ 1)
    (hcMove:0 < cMove) (hcMove1:cMove ≤ 1) (hqRamp:0 < qRamp) (hqBand:0 < qBand) :
    ∀ᶠ n:ℕ in atTop,∀a:NativeChildBarrierCall n delta,∀x y start stop finish:ℝ,
      a.context.d ≤ Dbound → Real.sqrt (n:ℝ)*a.context.E ≤ a.context.d^2 →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*a.context.d ≤ a.context.E →
      x∈Ioc (0:ℝ) 1 → y∈Ioc (0:ℝ) 1 → comparisonLowerScale n a.context.E a.context.d ≤ x →
      cScale*x ≤ y → a.e x ≤ x^2 →
      a.childRadius=c0*x → a.childLam=(c0*x)^2 →
      a.err ≤ (n:ℝ)^(20*delta)*actualChildErrorBudget n delta c0 a.context.d a.lam x →
      0 ≤ start → start < stop → stop ≤ finish → finish ≤ 1 →
      qRamp*y ≤ stop-start → qBand*y ≤ finish-stop →
      4*y ≤ a.Z start → ((∀u∈Icc start 1,cMove*y ≤ a.R u) ∨ a.e 0 ≤ a.D y) →
      (∀u∈Icc stop finish,a.R u ≤ y) → False := by
  have hroom:=eventually_comparison_native_upward_ramp_room (gamma:=gamma) (D:=Dbound)
    (m:=m) (delta:=delta) (cScale:=cScale) (q:=qRamp) hgamma hm hdelta hcScale hqRamp
  have hsmall:=eventually_actual_child_error_below_separated_gain (delta:=delta) (c0:=c0)
    (cScale:=cScale) (A:=3*cMove*qBand/100) hdelta hc0 hcScale hcScale1 (by positivity)
  filter_upwards [hroom,hsmall] with n hnroom hnsmall
  intro a x y start stop finish hdD hupper hlower hx hy hax hscale hweak hdc hlc herr
    ha hab hbf hf hwidthRamp hwidthBand hZlarge hroute hRupper
  have hscaleA:cScale*comparisonLowerScale n a.context.E a.context.d ≤ y:=
    (mul_le_mul_of_nonneg_left hax hcScale.le).trans hscale
  obtain ⟨hforce,hspeed⟩:=hnroom a.context.E a.context.d y start stop a.context.hE a.context.hd
    hdD hupper hlower hscaleA hwidthRamp
  have hgain:=comparison_native_upward_successful_child_error_lower a hcMove hcMove1 hy.1 ha hab hbf hf
    hqBand.le hwidthBand hforce hspeed hZlarge hroute hRupper
  have herror:=hnsmall a.context.d a.lam x y a.context.hd.ne' a.hlam hx hy hscale hweak
  rw [←hlc,←hdc] at herror
  have hh:=mul_le_mul_of_nonneg_left herr (by norm_num : (0:ℝ) ≤ 4)
  linarith

theorem eventually_comparison_native_child_excludes_downward_separation
    {delta gamma Dbound m c0 cScale C qTravel qBand:ℝ}
    (hdelta:0 < delta) (hgamma:0 < gamma) (hm:0 < m) (hc0:0 < c0)
    (hcScale:0 < cScale) (hcScale1:cScale ≤ 1)
    (hC:1 ≤ C) (hqTravel:0 < qTravel) (hqBand:0 < qBand) :
    ∀ᶠ n:ℕ in atTop,∀a:NativeChildBarrierCall n delta,∀x y start stop departure finish:ℝ,
      a.context.d ≤ Dbound → Real.sqrt (n:ℝ)*a.context.E ≤ a.context.d^2 →
      gamma*(n:ℝ)^(-(2:ℝ)/3+m)*a.context.d ≤ a.context.E →
      x∈Ioc (0:ℝ) 1 → y∈Ioc (0:ℝ) 1 → comparisonLowerScale n a.context.E a.context.d ≤ x →
      cScale*x ≤ y → a.e x ≤ x^2 → y ≤ 1/4 →
      a.childRadius=c0*x → a.childLam=(c0*x)^2 →
      a.err ≤ (n:ℝ)^(20*delta)*actualChildErrorBudget n delta c0 a.context.d a.lam x →
      0 ≤ start → start ≤ stop → stop ≤ departure → departure ≤ finish → finish ≤ 1 →
      qTravel*y ≤ finish-departure → qBand*y ≤ stop-start → a.Z finish ≤ y →
      (∀u∈Icc (0:ℝ) finish,a.R u ≤ C*y) →
      (∀u∈Icc start stop,4*y ≤ a.R u) → False := by
  have hroom:=eventually_comparison_native_upward_ramp_room (gamma:=gamma) (D:=Dbound)
    (m:=m) (delta:=delta) (cScale:=cScale) (q:=1) hgamma hm hdelta hcScale zero_lt_one
  have htravel:=eventually_comparison_native_downward_ramp_room (gamma:=gamma) (m:=m)
    (delta:=delta) (cScale:=cScale) (q:=qTravel) hgamma hm hdelta hcScale hqTravel
  have hC0:0 < C:=zero_lt_one.trans_le hC
  have hsmall:=eventually_actual_child_error_below_separated_gain (delta:=delta) (c0:=c0)
    (cScale:=cScale) (A:=qBand/(100*C^2)) hdelta hc0 hcScale hcScale1 (by positivity)
  filter_upwards [hroom,htravel,hsmall] with n hnroom hntravel hnsmall
  intro a x y start stop departure finish hdD hupper hlower hx hy hax hscale hweak hy4 hdc hlc herr
    ha hab hstop hb hf hwidthTravel hwidthBand hZsmall hRupper hRlarge
  have hscaleA:cScale*comparisonLowerScale n a.context.E a.context.d ≤ y:=
    (mul_le_mul_of_nonneg_left hax hcScale.le).trans hscale
  obtain ⟨hforce,hspeed⟩:=hnroom a.context.E a.context.d y 0 y a.context.hE a.context.hd
    hdD hupper hlower hscaleA (by simp)
  have hspeed':(a.context.M 0)⁻¹ ≤
      ((n:ℝ)^(2*delta)*a.context.U)^2/((n:ℝ)^delta*a.context.U^2):=by
    have hp:0 ≤ 2*y/(y-0):=div_nonneg (mul_nonneg (by norm_num) hy.1.le) (by linarith [hy.1])
    exact (le_add_of_nonneg_right hp).trans hspeed
  have ht:=hntravel a.context.E a.context.d y a.context.hE a.context.hd hupper hlower hscaleA
  have htravel':departure+reciprocalFloorTime ((n:ℝ)^delta*a.context.U^2)
      ((n:ℝ)^(2*delta)*a.context.U) 1 ≤ finish:=by
    have hh:=add_le_add_left ht departure
    linarith
  have hgain:=comparison_native_downward_successful_child_error_lower a hC hy.1 hy4 ha hab hstop hb hf
    hqBand.le hwidthBand hforce hspeed' htravel' hZsmall hRupper hRlarge
  have herror:=hnsmall a.context.d a.lam x y a.context.hd.ne' a.hlam hx hy hscale hweak
  rw [←hlc,←hdc] at herror
  have hh:=mul_le_mul_of_nonneg_left herr (by norm_num : (0:ℝ) ≤ 4)
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
