module

public import ComparisonSignedCavityActualStarMismatch
public import ComparisonNativeOverlapRawAmplitude
public import ComparisonNativeMaskMassTransport

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 5000000
attribute [local instance] Classical.propDecidable

theorem exists_good_point_off_mask_ae {a z t : ℝ} {f mask : ℝ → ℝ} {P : ℝ → Prop}
    (haz : a < z) (_ht : 0 ≤ t)
    (hf : IntegrableOn f (Ioo a z)) (hm : IntegrableOn mask (Ioo a z))
    (hf0 : ∀ᵐu, u∈Ioo a z → 0 ≤ f u)
    (hmask : ∀ᵐu, u∈Ioo a z → mask u=0 ∨ mask u=1)
    (hP : ∀ᵐu, u∈Ioo a z → P u)
    (hsmall : (∫u in Ioo a z,f u) < t*((z-a)-(∫u in Ioo a z,mask u))) :
    ∃u∈Ioo a z,mask u=0 ∧ f u ≤ t ∧ P u := by
  by_contra hn
  have hbad : ∀u∈Ioo a z, mask u=0 → P u → t < f u := by
    intro u hu hm0 hp
    exact lt_of_not_ge (fun hle=>hn ⟨u,hu,hm0,hle,hp⟩)
  have H:=integral_mono_ae (integrable_const t) (hf.add (hm.const_mul t)) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,ae_restrict_of_ae hf0,
      ae_restrict_of_ae hmask,ae_restrict_of_ae hP] with u hu hf0 hm hp
    change t ≤ f u+t*mask u
    rcases hm hu with hm|hm
    · simpa only [hm,mul_zero,add_zero] using (hbad u hu hm (hp hu)).le
    · simpa only [hm,mul_one] using (le_add_of_nonneg_left (hf0 hu) : t ≤ f u+t))
  have he : (∫_u in Ioo a z,t)=t*(z-a) := by
    rw [setIntegral_const,measureReal_def,Real.volume_Ioo,ENNReal.toReal_ofReal (sub_pos.mpr haz).le]
    simp only [smul_eq_mul,mul_comm]
  change (∫_u in Ioo a z,t) ≤ ∫u in Ioo a z,f u+t*mask u at H
  rw [he,integral_add hf (hm.const_mul t),integral_const_mul] at H
  linarith

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem cavityCapTravel_nonneg
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    0 ≤ M.cavityCapTravel := by
  unfold cavityCapTravel
  exact mul_nonneg (div_nonneg M.context.hL.le (Real.rpow_pos_of_pos M.context.hN delta).le)
    (Real.log_nonneg ((le_div_iff₀ M.context.hU).mpr (by linarith)))

def Potential.positiveRadiusSet
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) : Set ℝ := Icc (0:ℝ) 1 ∩ p.H ⁻¹' Ioi 0

theorem Potential.positiveRadiusSet_measurable
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) : MeasurableSet p.positiveRadiusSet := by
  have hc : ContinuousOn p.H (Icc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using p.hH.continuousOn
  have hclosed : IsClosed (Icc (0:ℝ) 1 ∩ p.H ⁻¹' Iic 0) :=
    hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have he : p.positiveRadiusSet=Icc (0:ℝ) 1 \ (Icc (0:ℝ) 1 ∩ p.H ⁻¹' Iic 0) := by
    ext r
    simp only [positiveRadiusSet,mem_inter_iff,mem_preimage,mem_Ioi,Set.mem_sdiff,mem_Iic]
    constructor
    · rintro ⟨hr,hpos⟩
      exact ⟨hr,fun hh=>not_le_of_gt hpos hh.2⟩
    · rintro ⟨hr,hnot⟩
      exact ⟨hr,lt_of_not_ge (fun hh=>hnot ⟨hr,hh⟩)⟩
  rw [he]
  exact measurableSet_Icc.diff hclosed.measurableSet

def Potential.positiveMassMask
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (u : ℝ) : ℝ := p.positiveRadiusSet.indicator (fun _=>1) (M.R u)

theorem Potential.positiveMassMask_zero_iff
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (u : ℝ) : p.positiveMassMask u=0 ↔ p.H (M.R u) ≤ 0 := by
  have hr := comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u
  by_cases hp : 0 < p.H (M.R u)
  · have hm : M.R u∈p.positiveRadiusSet := ⟨hr,hp⟩
    simp [positiveMassMask,hm,not_le_of_gt hp]
  · have hm : M.R u∉p.positiveRadiusSet := fun h=>hp h.2
    simp [positiveMassMask,hm,le_of_not_gt hp]

theorem Potential.positiveMassMask_integrable
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) : IntegrableOn p.positiveMassMask (Icc (0:ℝ) 1) := by
  have hm : Measurable p.positiveMassMask :=
    (measurable_const.indicator p.positiveRadiusSet_measurable).comp
      (comparisonSweepQuantile_continuous M.context.hc M.context.hk M.context.hkc
        M.context.hm M.context.hM M.alpha).measurable
  have hi : IntervalIntegrable p.positiveMassMask volume 0 1 := by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hm zero_le_one
      (fun u _=>by dsimp [positiveMassMask];by_cases h:M.R u∈p.positiveRadiusSet <;> simp [h])
      (intervalIntegrable_const (c:=(1:ℝ)))
  exact intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one |>.mp hi

theorem Potential.positiveMassMask_mass_le
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) :
    (∫u in Icc (0:ℝ) 1,p.positiveMassMask u) ≤ M.context.N^(-delta)*M.context.U := by
  rw [show (∫u in Icc (0:ℝ) 1,p.positiveMassMask u)=
      ∫r in Icc (0:ℝ) 1,deriv M.alpha.val.val r*p.positiveRadiusSet.indicator (fun _=>1) r by
    exact comparison_quantile_weighted_integral M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha _]
  have hsub : p.positiveRadiusSet ⊆ Icc (0:ℝ) 1 := inter_subset_left
  have hf : ∀ᵐr,r∈Icc (0:ℝ) 1 → r∈p.positiveRadiusSet →
      deriv M.alpha.val.val r=comparisonFloor M.context.N delta M.context.U r := by
    filter_upwards [p.hfloor] with r hr hri hp
    exact hr hri hp.2
  have H:=comparisonFloor_region_mass M.context.hN M.context.hU
    (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) p.positiveRadiusSet
    p.positiveRadiusSet_measurable M.alpha.val.val hf
  have he : (fun r=>deriv M.alpha.val.val r*p.positiveRadiusSet.indicator (fun _=>1) r)=
      p.positiveRadiusSet.indicator (deriv M.alpha.val.val) := by
    funext r
    by_cases h:r∈p.positiveRadiusSet <;> simp [h]
  rw [he,setIntegral_indicator p.positiveRadiusSet_measurable,inter_eq_right.mpr hsub]
  rw [setIntegral_indicator p.positiveRadiusSet_measurable,inter_eq_right.mpr hsub] at H
  exact H

theorem Potential.exists_thermal_good_star_off_floor
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {a z t : ℝ} (ha : 0 ≤ a) (haz : a < z) (hz : z ≤ 1)
    (ht : 0 ≤ t) (haway : ∀u∈Ioo a z,M.cavityCapTravel < M.R u)
    (hsmall : (∫u in Ioo a z,orderedPathB (n+1) M.bf M.hf u-
      (orderedPathS (n+1) M.bf M.hf u)^2) <
      t*((z-a)-M.context.N^(-delta)*M.context.U)) :
    ∃u∈Ioo a z,p.H (M.R u) ≤ 0 ∧
      orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2 ≤ t ∧
      (orderedPathS (n+1) M.bf M.hf u-M.R u)^2 ≤ 16*M.cavityCapTravel^2+2*t := by
  let f:=fun u=>orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2
  have hsub : Ioo a z ⊆ Icc (0:ℝ) 1 := fun u hu=>⟨ha.trans hu.1.le,hu.2.le.trans hz⟩
  have hiF : IntegrableOn f (Icc (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      (native_comparison_thermal_intervalIntegrable M)
  have hf0 u (hu : u∈Icc (0:ℝ) 1) : 0 ≤ f u := by
    have hr:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha u
    have H:=M.cavityRadiusPointDefect_nonneg hr
    simpa only [cavityRadiusPointDefect,comparisonSweepQuantile_mass_spec
      M.context.hc M.context.hk M.context.hkc M.context.hm M.context.hM M.alpha hu] using H
  have hmask0 u : 0 ≤ p.positiveMassMask u := by
    dsimp [positiveMassMask]
    by_cases h:M.R u∈p.positiveRadiusSet <;> simp [h]
  have hmass : (∫u in Ioo a z,p.positiveMassMask u) ≤ M.context.N^(-delta)*M.context.U := by
    exact (setIntegral_mono_set p.positiveMassMask_integrable
      (Eventually.of_forall (fun u=>hmask0 u)) (Eventually.of_forall hsub)).trans
      p.positiveMassMask_mass_le
  have hP : ∀ᵐu,u∈Ioo a z → p.H (M.R u) ≤ 0 →
      (orderedPathS (n+1) M.bf M.hf u-M.R u)^2 ≤
        16*M.cavityCapTravel^2+2*f u := by
    filter_upwards [p.nonpositive_squared_mismatch_ae_mass] with u hu hui hh
    exact hu (hsub hui) (haway u hui) hh
  have hbudget : (∫u in Ioo a z,f u) <
      t*((z-a)-(∫u in Ioo a z,p.positiveMassMask u)) := by
    exact hsmall.trans_le (mul_le_mul_of_nonneg_left (sub_le_sub_left hmass _) ht)
  obtain ⟨u,hu,hm,hf,hp⟩:=exists_good_point_off_mask_ae haz ht
    (hiF.mono_set hsub) (p.positiveMassMask_integrable.mono_set hsub)
    (Eventually.of_forall (fun u hu=>hf0 u (hsub hu)))
    (Eventually.of_forall (fun u _=>by
      dsimp [positiveMassMask]
      by_cases h:M.R u∈p.positiveRadiusSet <;> simp [h])) hP hbudget
  have hh:=(p.positiveMassMask_zero_iff u).mp hm
  refine ⟨u,hu,hh,hf,?_⟩
  exact (hp hh).trans (by linarith)

theorem Potential.exists_thermal_good_star_mean_bounds
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {a z c C W : ℝ}
    (ha : 0 ≤ a) (haz : a < z) (hz : z ≤ 1) (hc : 0 < c) (hW : 0 < W)
    (htravelsmall : M.cavityCapTravel ≤ c*W/32)
    (hband : ∀u∈Ioo a z,c*W ≤ M.R u ∧ M.R u ≤ C*W)
    (hsmall : (∫u in Ioo a z,orderedPathB (n+1) M.bf M.hf u-
      (orderedPathS (n+1) M.bf M.hf u)^2) <
      ((c*W)^2/64)*((z-a)-M.context.N^(-delta)*M.context.U)) :
    ∃u∈Ioo a z,p.H (M.R u) ≤ 0 ∧
      orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2 ≤ (c*W)^2/64 ∧
      |orderedPathS (n+1) M.bf M.hf u-M.R u| ≤ c*W/4 ∧
      (3*c/4)*W ≤ orderedPathS (n+1) M.bf M.hf u ∧
      orderedPathS (n+1) M.bf M.hf u ≤ (C+c/4)*W := by
  have hcw : 0 < c*W := mul_pos hc hW
  have htravel := M.cavityCapTravel_nonneg
  obtain ⟨u,hu,hh,hf,hm⟩:=p.exists_thermal_good_star_off_floor ha haz hz
    (by positivity : 0 ≤ (c*W)^2/64)
    (fun u hu=>by linarith [(hband u hu).1]) hsmall
  have hp:=pow_le_pow_left₀ htravel htravelsmall 2
  have hsq : (orderedPathS (n+1) M.bf M.hf u-M.R u)^2 ≤ (c*W/4)^2 := by
    nlinarith [sq_nonneg (c*W)]
  have habs : |orderedPathS (n+1) M.bf M.hf u-M.R u| ≤ c*W/4 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ c*W/4)).mp
    simpa only [sq_abs] using hsq
  refine ⟨u,hu,hh,hf,habs,?_,?_⟩ <;> nlinarith [(abs_le.mp habs).1,(abs_le.mp habs).2,
    (hband u hu).1,(hband u hu).2]

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
