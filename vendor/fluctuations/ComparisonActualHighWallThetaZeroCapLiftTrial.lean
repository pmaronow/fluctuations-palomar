module

public import ComparisonActualHighOnlyOmittedCapEnvelopes
public import ComparisonActualHighWallOverlapAmplitude

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false

theorem interval_cap_lift_max_ae_slope {a b:ℝ} (hab:a ≤ b)
    {r w lower upper:ℝ→ℝ} {C D:ℝ≥0}
    (hr:LipschitzOnWith C r (Icc a b)) (hw:LipschitzOnWith D w (Icc a b))
    (hdr:∀ᵐu,u∈Icc a b → lower u ≤ deriv r u ∧ deriv r u ≤ upper (r u))
    (hdw:∀ᵐu,u∈Icc a b → lower u ≤ deriv w u ∧ deriv w u ≤ upper (w u)) :
    ∀ᵐu,u∈Icc a b → lower u ≤ deriv (fun v=>max (r v) (w v)) u ∧
      deriv (fun v=>max (r v) (w v)) u ≤ upper (max (r u) (w u)) := by
  have hrv:AbsolutelyContinuousOnInterval r a b:=by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hab] using hr
  have hwv:AbsolutelyContinuousOnInterval w a b:=by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hab] using hw
  have hqv:AbsolutelyContinuousOnInterval (fun u=>max (r u) (w u)) a b:=by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K:=max C D)
    simpa only [uIcc_of_le hab] using real_max_lipschitzOn hr hw
  filter_upwards [hdr,hdw,hrv.ae_differentiableAt,hwv.ae_differentiableAt,hqv.ae_differentiableAt]
    with u hdr hdw hr hw hq hu
  have hui:u∈uIcc a b:=by simpa only [uIcc_of_le hab] using hu
  rcases differentiable_max_selection (hr hui) (hw hui) (hq hui) with H|H
  · rw [H.1,H.2];exact hdr hu
  · rw [H.1,H.2];exact hdw hu

namespace ActualHighWallData
variable {n:ℕ} {delta:ℝ} (a:ActualHighWallData n delta)

abbrev zeroOriginProfile:=inverseIntegralConstraints 0 a.s a.k a.M
abbrev zeroOriginRadius (alpha:a.zeroOriginProfile):=omittedSweepQuantile zero_le_one ⟨a.hs.1.le,a.hs1⟩
  a.hc (comparisonFloor_continuousOn a.hN a.hU le_rfl)
  (fun r hr=>comparisonFloor_lower_on a.hN a.hU le_rfl hr) a.hm a.hM alpha

def capLiftBarrier (u:ℝ):=a.rmin+inverseCapPrimitive a.M u-inverseCapPrimitive a.M a.s
def capLiftRadius (alpha:a.zeroOriginProfile) (u:ℝ):=max (a.zeroOriginRadius alpha u) (a.capLiftBarrier u)

theorem cap_lift_feasible_original_profile (alpha:a.zeroOriginProfile) :
    ∃gamma:a.Profile,∀u∈Icc a.s 1,
      gamma.val.val (a.capLiftRadius alpha u)=u ∧
      0 ≤ a.capLiftRadius alpha u-a.zeroOriginRadius alpha u ∧
      a.capLiftRadius alpha u-a.zeroOriginRadius alpha u ≤ a.rmin := by
  let hs:Icc (0:ℝ) 1 := ⟨a.s,⟨a.hs.1.le,a.hs1⟩⟩
  have hMc:Continuous a.M:=concreteWallCap_continuous _ _ _ _
  have hMp:∀u∈Icc (0:ℝ) 1,0 < a.M u:=by
    intro u hu
    have H:=a.hq.trans (concreteWallCap_ge a.hN a.hE a.hd hu.1)
    linarith
  have hM2:∀u∈Icc (0:ℝ) 1,2 ≤ a.M u:=fun u hu=>a.hq.trans (concreteWallCap_ge a.hN a.hE a.hd hu.1)
  let r:=a.zeroOriginRadius alpha
  let w:=a.capLiftBarrier
  let q:=a.capLiftRadius alpha
  have hr:LipschitzOnWith _ r (Icc a.s 1):=
    (omittedSweepQuantile_lipschitz zero_le_one hs.property a.hc
      (comparisonFloor_continuousOn a.hN a.hU le_rfl)
      (fun r hr=>comparisonFloor_lower_on a.hN a.hU le_rfl hr) a.hm a.hM alpha).lipschitzOnWith.mono
        (Icc_subset_Icc le_rfl le_rfl)
  have Hprim:=inverseCapPrimitive_lipschitz hMc a.hm hMp
  have hw:LipschitzOnWith ⟨(a.M 0)⁻¹,inv_nonneg.mpr (hMp 0 ⟨le_rfl,zero_le_one⟩).le⟩ w (Icc a.s 1):=by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    have H:=Hprim.dist_le_mul u ⟨a.hs.1.le.trans hu.1,hu.2⟩ v ⟨a.hs.1.le.trans hv.1,hv.2⟩
    simpa only [w,capLiftBarrier,Real.dist_eq,show
      a.rmin+inverseCapPrimitive a.M u-inverseCapPrimitive a.M a.s-
      (a.rmin+inverseCapPrimitive a.M v-inverseCapPrimitive a.M a.s)=
        inverseCapPrimitive a.M u-inverseCapPrimitive a.M v by ring] using H
  have hq:LipschitzOnWith _ q (Icc a.s 1):=real_max_lipschitzOn hr hw
  have hws: w a.s=a.rmin:=by dsimp [w,capLiftBarrier];ring
  have hW:∀u∈Icc a.s 1,a.rmin ≤ w u ∧ w u ≤ 1:=by
    intro u hu
    have hmono:=actual_high_only_inverseCapPrimitive_mono hMc a.hm hMp hs.property ⟨a.hs.1.le.trans hu.1,hu.2⟩ hu.1
    have HI:=inverseCapPrimitive_integrable hMc a.hm hMp
    have HIs:=HI.mono_set (by rw [uIcc_of_le a.hs.1.le,uIcc_of_le zero_le_one];exact Icc_subset_Icc le_rfl a.hs1)
    have HIu:=HI.mono_set (by rw [uIcc_of_le hu.1,uIcc_of_le zero_le_one];exact Icc_subset_Icc a.hs.1.le hu.2)
    have Hsum:=intervalIntegral.integral_add_adjacent_intervals HIs HIu
    have Hb:(∫v in a.s..u,(a.M v)⁻¹) ≤ (u-a.s)/2:=by
      have HH:(∫v in a.s..u,(a.M v)⁻¹) ≤ ∫v in a.s..u,(1/2:ℝ):=by
        apply intervalIntegral.integral_mono_on hu.1 HIu intervalIntegrable_const
        intro v hv
        have H:=(inv_le_inv₀ (hMp v ⟨a.hs.1.le.trans hv.1,hv.2.trans hu.2⟩)
          (by norm_num : (0:ℝ) < 2)).mpr (hM2 v ⟨a.hs.1.le.trans hv.1,hv.2.trans hu.2⟩)
        norm_num only [invOf_eq_inv,inv_div,inv_one] at H
        exact H
      simpa only [intervalIntegral.integral_const,smul_eq_mul,div_eq_mul_inv,mul_comm,one_mul] using HH
    change inverseCapPrimitive a.M a.s ≤ inverseCapPrimitive a.M u at hmono
    dsimp only [w,capLiftBarrier]
    constructor
    · linarith only [hmono]
    · have HR:=a.hrbounds.2.2
      dsimp only [inverseCapPrimitive] at hmono ⊢
      linarith only [Hsum,Hb,HR,hu.2,a.hs.1]
  have hrb:∀u,r u∈Icc (0:ℝ) 1:=fun u=>omittedSweepQuantile_bounds zero_le_one hs.property a.hc
    (comparisonFloor_continuousOn a.hN a.hU le_rfl)
    (fun r hr=>comparisonFloor_lower_on a.hN a.hU le_rfl hr) a.hm a.hM alpha u
  have hqb:MapsTo q (Icc a.s 1) (Icc a.rmin 1):=by
    intro u hu
    exact ⟨(hW u hu).1.trans (le_max_right _ _),max_le (hrb u).2 (hW u hu).2⟩
  have hq0:q a.s=a.rmin:=by
    have Hr0:r a.s=0:=omittedSweepQuantile_left zero_le_one hs.property a.hc
      (comparisonFloor_continuousOn a.hN a.hU le_rfl)
      (fun r hr=>comparisonFloor_lower_on a.hN a.hU le_rfl hr) a.hm a.hM alpha
    change max (r a.s) (w a.s)=a.rmin
    rw [Hr0,hws,max_eq_right a.hrbounds.1.le]
  have hq1:q 1=1:=by
    have Hr1:r 1=1:=omittedSweepQuantile_one zero_le_one hs.property a.hc
      (comparisonFloor_continuousOn a.hN a.hU le_rfl)
      (fun r hr=>comparisonFloor_lower_on a.hN a.hU le_rfl hr) a.hm a.hM alpha
    change max (r 1) (w 1)=1
    rw [Hr1,max_eq_left (hW 1 ⟨a.hs1,le_rfl⟩).2]
  have Hderw:∀ᵐu,u∈Icc a.s 1 → (a.M u)⁻¹ ≤ deriv w u ∧ deriv w u ≤ (a.k (w u))⁻¹:=by
    filter_upwards [volume.ae_ne (0:ℝ),volume.ae_ne (1:ℝ)] with u hu0 hu1 hu
    have hui:u∈Ioo (0:ℝ) 1:=⟨lt_of_le_of_ne (a.hs.1.le.trans hu.1) hu0.symm,lt_of_le_of_ne hu.2 hu1⟩
    have H:=((inverseCapPrimitive_hasDerivAt hMc a.hm hMp hui).const_add a.rmin).sub_const (inverseCapPrimitive a.M a.s)
    change HasDerivAt w ((a.M u)⁻¹) u at H
    rw [H.deriv]
    refine ⟨le_rfl,?_⟩
    have HK:=comparisonFloor_le_half a.hN a.hU (a.hrbounds.1.le.trans (hW u hu).1) a.hq
    have HKp:=a.hc.trans_le (a.hkc _ ⟨(hW u hu).1,(hW u hu).2⟩)
    exact (inv_le_inv₀ (hMp u ⟨a.hs.1.le.trans hu.1,hu.2⟩) HKp).mpr
      (HK.trans (by linarith [hM2 u ⟨a.hs.1.le.trans hu.1,hu.2⟩]))
  have Hderr:=omittedSweepQuantile_ae_slope zero_le_one hs.property a.hc
    (comparisonFloor_continuousOn a.hN a.hU le_rfl)
    (fun r hr=>comparisonFloor_lower_on a.hN a.hU le_rfl hr) a.hm a.hM alpha hMc
    (fun u hu=>hMp u ⟨a.hs.1.le.trans hu.1,hu.2⟩)
  have Hder:=interval_cap_lift_max_ae_slope (lower:=fun u=>(a.M u)⁻¹) (upper:=fun r=>(a.k r)⁻¹) a.hs1 hr hw Hderr Hderw
  obtain ⟨gamma,Hgamma⟩:=exists_omitted_inverse_profile_of_forward_slope a.hr hs.property hq hqb hq0 hq1 a.hk hMc a.hm
    (fun r hr=>a.hc.trans_le (a.hkc r hr)) (fun u hu=>hMp u ⟨a.hs.1.le.trans hu.1,hu.2⟩) Hder
  refine ⟨gamma,?_⟩
  intro u hu
  have Hcap:=actual_high_only_omitted_quantile_cap_envelopes hs.property a.hc
    (comparisonFloor_continuousOn a.hN a.hU le_rfl)
    (fun r hr=>comparisonFloor_lower_on a.hN a.hU le_rfl hr) hMc a.hm hMp alpha hu
  refine ⟨Hgamma u hu,sub_nonneg.mpr (le_max_left _ _),?_⟩
  have HH:w u ≤ r u+a.rmin:=by dsimp [w,capLiftBarrier,r,zeroOriginRadius] at Hcap ⊢;linarith only [Hcap.1]
  have HR:=a.hrbounds.1.le
  change max (r u) (w u)-r u ≤ a.rmin
  exact (sub_le_iff_le_add).mpr (max_le (by linarith only [HR]) (by linarith only [HH]))

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
