module

public import ComparisonActualHighOnlyOriginalFloorMass
public import ComparisonActualHighOnlyInitialCharges
public import ComparisonActualHighOnlyFlatWeightedAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 20000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem coefficient_measurable
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    Measurable M.coefficient := by
  have hg := (laplaceComparisonStrength_contDiff M.context.d M.lam).continuous.measurable.comp
    (omittedSweepQuantile_continuous zero_le_one ⟨M.data.hs.1,M.data.hs1⟩ M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha).measurable
  have H:=hg.indicator (s:={u : ℝ | M.data.s≤u}) (measurableSet_le measurable_const measurable_id)
  convert H using 1
  funext u
  simp only [coefficient,ActualHighOnlyComparisonData.coefficient,omittedStrengthCoefficient,
    Set.indicator_apply,mem_ofPred_eq,Function.comp_apply]

theorem coefficient_intervalIntegrable
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    IntervalIntegrable M.coefficient volume 0 1 := by
  simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul M.coefficient_measurable M.hlam.le
    (fun u _=>show M.coefficient u∈Icc 0 M.lam from ⟨M.coefficient_nonneg u,M.coefficient_le_lam u⟩)
    (intervalIntegrable_const (c:=(1:ℝ)))

def Potential.offFloorWeightedDiscrepancy
    {M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock} (p : M.Potential) (u : ℝ) : ℝ :=
  |M.coefficient u*
    (orderedPathS (n+1) M.bf M.hf u-M.R u)| * (1-p.positiveMassMask u)

theorem Potential.offFloorWeightedDiscrepancy_intervalIntegrable
    {M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock} (p : M.Potential) :
    IntervalIntegrable p.offFloorWeightedDiscrepancy volume 0 1 := by
  have hD:IntervalIntegrable (fun u=>orderedPathS (n+1) M.bf M.hf u-M.R u) volume 0 1:=
    (show MonotoneOn (orderedPathS (n+1) M.bf M.hf) (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one] using M.mass_mean_monotone).intervalIntegrable.sub
      ((omittedSweepQuantile_continuous zero_le_one ⟨M.data.hs.1,M.data.hs1⟩ M.context.hc M.context.hk M.context.hkc
        M.context.hm M.context.hM M.alpha).intervalIntegrable 0 1)
  have he:IntervalIntegrable M.coefficient volume 0 1:=M.coefficient_intervalIntegrable
  have heb:∀u∈Ioc (0:ℝ) 1,|M.coefficient u| ≤ M.lam:=by
    intro u _
    rw [abs_of_nonneg (M.coefficient_nonneg _)]
    exact M.coefficient_le_lam _
  have hW:IntervalIntegrable (fun u=>|M.coefficient u*
      (orderedPathS (n+1) M.bf M.hf u-M.R u)|) volume 0 1:=by
    have H:=Hierarchy.intervalIntegrable_mul_bounded hD he heb
    simpa only [mul_comm] using H.abs
  have hMask:IntervalIntegrable (fun u=>1-p.positiveMassMask u) volume 0 1:=
    intervalIntegrable_const.sub ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr p.positiveMassMask_integrable)
  have hb:∀u∈Ioc (0:ℝ) 1,|1-p.positiveMassMask u| ≤ 1:=by
    intro u _
    dsimp only [Potential.positiveMassMask]
    by_cases H:M.R u∈p.positiveRadiusSet <;> simp [H]
  exact Hierarchy.intervalIntegrable_mul_bounded hW hMask hb

theorem Potential.offFloorWeightedDiscrepancy_nonneg
    {M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock} (p : M.Potential) (u : ℝ) :
    0 ≤ p.offFloorWeightedDiscrepancy u := by
  dsimp only [offFloorWeightedDiscrepancy,Potential.positiveMassMask]
  by_cases H:M.R u∈p.positiveRadiusSet
  · simp only [indicator_of_mem H,sub_self,mul_zero]
    exact le_rfl
  · rw [indicator_of_notMem H,sub_zero,mul_one]
    exact abs_nonneg _

theorem Potential.offFloorWeightedDiscrepancy_mass_le
    {M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock} (p : M.Potential)
    {v loss : ℝ} (hv : v∈Icc (0:ℝ) 1) (hloss : 0 ≤ loss)
    (Hpoint : ∀ᵐu,u∈Icc (0:ℝ) v → p.H (M.R u) ≤ 0 →
      |M.coefficient u*
        (orderedPathS (n+1) M.bf M.hf u-M.R u)|/M.xs^3 ≤ loss) :
    (∫u in 0..v,p.offFloorWeightedDiscrepancy u) ≤ loss*M.xs^3*v := by
  have hi:=p.offFloorWeightedDiscrepancy_intervalIntegrable.mono_set (by
    rw [uIcc_of_le hv.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hv.2)
  have HX:∀ᵐu∂volume.restrict (Icc (0:ℝ) v),p.offFloorWeightedDiscrepancy u ≤ loss*M.xs^3:=by
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae Hpoint] with u hu hh
    by_cases hp:p.H (M.R u) ≤ 0
    · have HM: p.positiveMassMask u=0:=(p.positiveMassMask_zero_iff u).mpr hp
      dsimp only [offFloorWeightedDiscrepancy]
      rw [HM,sub_zero,mul_one]
      exact (div_le_iff₀ (pow_pos M.hxs 3)).mp (hh hu hp)
    · have HM:p.positiveMassMask u=1:=by
        have HR:=omittedSweepQuantile_bounds zero_le_one ⟨M.data.hs.1,M.data.hs1⟩ M.context.hc M.context.hk M.context.hkc
          M.context.hm M.context.hM M.alpha u
        simp only [Potential.positiveMassMask,indicator_of_mem (show M.R u∈p.positiveRadiusSet from ⟨HR,lt_of_not_ge hp⟩)]
      dsimp only [offFloorWeightedDiscrepancy]
      rw [HM,sub_self,mul_zero]
      exact mul_nonneg hloss (pow_pos M.hxs 3).le
  have H:=intervalIntegral.integral_mono_ae_restrict hv.1 hi (intervalIntegrable_const) HX
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using H

variable {M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

 theorem Potential.original_off_floor_weighted_integral_exact (p : M.Potential)
    {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) :
    (∫w : ParisiFinite.OrderPoint in p.originalOrderFloorᶜ,
      |M.coefficient w*
        (orderedPathS (n+1) M.bf M.hf w-M.R w)/M.xs^3|
        ∂comparisonNormalizedClockMass M.xs v) =
      (∫u in 0..v,p.offFloorWeightedDiscrepancy u)/M.xs^4 := by
  rw [← integral_indicator p.originalOrderFloor_measurable.compl]
  have heq : (fun w : ParisiFinite.OrderPoint => p.originalOrderFloorᶜ.indicator
      (fun w => |M.coefficient w*
        (orderedPathS (n+1) M.bf M.hf w-M.R w)/M.xs^3|) w) =
      fun w : ParisiFinite.OrderPoint => |p.offFloorWeightedDiscrepancy w/M.xs^3| := by
    funext w
    by_cases H : w ∈ p.originalOrderFloor
    · have HP : p.positiveMassMask w=1 := by
        rw [← p.originalOrderFloor_indicator w,indicator_of_mem H]
      rw [indicator_of_notMem (show w ∉ p.originalOrderFloorᶜ from not_not.mpr H)]
      simp only [Potential.offFloorWeightedDiscrepancy, HP, sub_self, mul_zero, zero_div, abs_zero]
    · have HP : p.positiveMassMask w=0 := by
        rw [← p.originalOrderFloor_indicator w,indicator_of_notMem H]
      rw [indicator_of_mem (show w ∈ p.originalOrderFloorᶜ from H)]
      simp only [Potential.offFloorWeightedDiscrepancy, HP, sub_zero, mul_one, abs_div, abs_abs]
  rw [heq,comparison_normalized_cubic_residual_integral_exact _ M.hxs hv]
  simp_rw [abs_of_nonneg (p.offFloorWeightedDiscrepancy_nonneg _)]

theorem actual_high_strength_off_floor_weighted_mass_saving_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : ∀ᶠn in atTop,(M n).data.s ≤ 1/4)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2)
      atTop atTop)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃eta : ℕ→ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∃p : (M n).Potential,∀v∈Icc (0:ℝ) 1,v ≤ C*(M n).xs →
        (∫u in 0..v,p.offFloorWeightedDiscrepancy u)/(M n).xs^4 ≤ eta n := by
  let eta n:=C*actualWeightedCapTravelRate delta dim n
  have heta n:0 ≤ eta n:=mul_nonneg hC (actual_weighted_cap_travel_rate_nonneg delta dim n)
  have HEta:Tendsto eta atTop (𝓝 0):=by
    simpa only [mul_zero] using (actual_weighted_cap_travel_rate_tendsto_zero_along hdelta dim hdim).const_mul C
  refine ⟨eta,heta,HEta,?_⟩
  filter_upwards [actual_high_only_strength_flat_weighted_point_along hcl hAz dim M hs hlarge C hC,
    eventually_actual_cap_log_loss_le_along dim hdim M] with n hn hlog
  obtain ⟨p,hp⟩:=hn
  refine ⟨p,?_⟩
  intro v hv hvC
  have Hpoint:∀ᵐu,u∈Icc (0:ℝ) v → p.H ((M n).R u) ≤ 0 →
      |(M n).coefficient u*
        (orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)|/(M n).xs^3 ≤
        actualWeightedCapTravelRate delta dim n:=by
    filter_upwards [hp] with u hu hui hnonpos
    exact (hu ⟨hui.1,hui.2.trans hv.2⟩ (hui.2.trans hvC) hnonpos).trans hlog
  have H:=p.offFloorWeightedDiscrepancy_mass_le hv (actual_weighted_cap_travel_rate_nonneg delta dim n) Hpoint
  have HS:=mul_le_mul_of_nonneg_left hvC
    (mul_nonneg (actual_weighted_cap_travel_rate_nonneg delta dim n) (pow_pos (M n).hxs 3).le)
  apply (div_le_iff₀ (pow_pos (M n).hxs 4)).2
  apply H.trans
  convert HS using 1
  dsimp only [eta]
  ring

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
