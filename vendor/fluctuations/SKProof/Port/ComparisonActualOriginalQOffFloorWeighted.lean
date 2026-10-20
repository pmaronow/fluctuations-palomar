module

public import SKProof.Port.ComparisonActualOriginalQOriginalFloorMass
public import SKProof.Port.ComparisonActualOriginalQInitialCharges
public import SKProof.Port.ComparisonActualOriginalQFlatWeightedAlong
public import ComparisonActualHighWallThetaZeroErrorTransport
public import SKProof.Port.OriginalQHighOnlyBridge
public import SKProof.OriginalQWeightedCapCalibration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 20000000
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem coefficient_intervalIntegrable
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    IntervalIntegrable M.sweepCoefficient volume 0 1 := by
  simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul M.coefficient_measurable M.hlam.le
    (fun u _=>show M.sweepCoefficient u∈Icc 0 M.lam from ⟨M.coefficient_nonneg u,M.coefficient_le_lam u⟩)
    (intervalIntegrable_const (c:=(1:ℝ)))

def Potential.offFloorWeightedDiscrepancy
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock} (p : M.Potential) (u : ℝ) : ℝ :=
  |M.sweepCoefficient u*
    (orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u)| * (1-p.positiveMassMask u)

theorem Potential.offFloorWeightedDiscrepancy_intervalIntegrable
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock} (p : M.Potential) :
    IntervalIntegrable p.offFloorWeightedDiscrepancy volume 0 1 := by
  have hD:IntervalIntegrable (fun u=>orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u) volume 0 1:=
    (show MonotoneOn (orderedPathS (n+1) M.sweepBf M.sweepHf) (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one] using M.mass_mean_monotone).intervalIntegrable.sub
      ((M.sweepRadius_continuous).intervalIntegrable 0 1)

  have he:IntervalIntegrable M.sweepCoefficient volume 0 1:=M.coefficient_intervalIntegrable
  have heb:∀u∈Ioc (0:ℝ) 1,|M.sweepCoefficient u| ≤ M.lam:=by
    intro u _
    rw [abs_of_nonneg (M.coefficient_nonneg _)]
    exact M.coefficient_le_lam _
  have hW:IntervalIntegrable (fun u=>|M.sweepCoefficient u*
      (orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u)|) volume 0 1:=by
    have H:=Hierarchy.intervalIntegrable_mul_bounded hD he heb
    simpa only [mul_comm] using H.abs
  have hMask:IntervalIntegrable (fun u=>1-p.positiveMassMask u) volume 0 1:=
    intervalIntegrable_const.sub ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr p.positiveMassMask_integrable)
  have hb:∀u∈Ioc (0:ℝ) 1,|1-p.positiveMassMask u| ≤ 1:=by
    intro u _
    dsimp only [Potential.positiveMassMask]
    by_cases H:M.sweepRadius u∈p.positiveRadiusSet <;> simp [H]
  exact Hierarchy.intervalIntegrable_mul_bounded hW hMask hb

theorem Potential.offFloorWeightedDiscrepancy_nonneg
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock} (p : M.Potential) (u : ℝ) :
    0 ≤ p.offFloorWeightedDiscrepancy u := by
  dsimp only [offFloorWeightedDiscrepancy,Potential.positiveMassMask]
  by_cases H:M.sweepRadius u∈p.positiveRadiusSet
  · simp only [indicator_of_mem H,sub_self,mul_zero]
    exact le_rfl
  · rw [indicator_of_notMem H,sub_zero,mul_one]
    exact abs_nonneg _

theorem Potential.offFloorWeightedDiscrepancy_mass_le
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock} (p : M.Potential)
    {v loss : ℝ} (hv : v∈Icc (0:ℝ) 1) (hloss : 0 ≤ loss)
    (Hpoint : ∀ᵐu,u∈Icc (0:ℝ) v → p.H (M.sweepRadius u) ≤ 0 →
      |M.sweepCoefficient u*
        (orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u)|/M.xs^3 ≤ loss) :
    (∫u in 0..v,p.offFloorWeightedDiscrepancy u) ≤ loss*M.xs^3*v := by
  have hi:=p.offFloorWeightedDiscrepancy_intervalIntegrable.mono_set (by
    rw [uIcc_of_le hv.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hv.2)
  have HX:∀ᵐu∂volume.restrict (Icc (0:ℝ) v),p.offFloorWeightedDiscrepancy u ≤ loss*M.xs^3:=by
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae Hpoint] with u hu hh
    by_cases hp:p.H (M.sweepRadius u) ≤ 0
    · have HM: p.positiveMassMask u=0:=(p.positiveMassMask_zero_iff u).mpr hp
      dsimp only [offFloorWeightedDiscrepancy]
      rw [HM,sub_zero,mul_one]
      exact (div_le_iff₀ (pow_pos M.hxs 3)).mp (hh hu hp)
    · have HM:p.positiveMassMask u=1:=by
        have HR:=M.sweepRadius_bounds u

        simp only [Potential.positiveMassMask,indicator_of_mem (show M.sweepRadius u∈p.positiveRadiusSet from ⟨HR,lt_of_not_ge hp⟩)]
      dsimp only [offFloorWeightedDiscrepancy]
      rw [HM,sub_self,mul_zero]
      exact mul_nonneg hloss (pow_pos M.hxs 3).le
  have H:=intervalIntegral.integral_mono_ae_restrict hv.1 hi (intervalIntegrable_const) HX
  convert H using 1
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul]
  ring

variable {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

 theorem Potential.original_off_floor_weighted_integral_exact (p : M.Potential)
    {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) :
    (∫w : ParisiFinite.OrderPoint in p.originalOrderFloorᶜ,
      |M.sweepCoefficient w*
        (orderedPathS (n+1) M.sweepBf M.sweepHf w-M.sweepRadius w)/M.xs^3|
        ∂comparisonNormalizedClockMass M.xs v) =
      (∫u in 0..v,p.offFloorWeightedDiscrepancy u)/M.xs^4 := by
  rw [← integral_indicator p.originalOrderFloor_measurable.compl]
  have heq : (fun w : ParisiFinite.OrderPoint => p.originalOrderFloorᶜ.indicator
      (fun w => |M.sweepCoefficient w*
        (orderedPathS (n+1) M.sweepBf M.sweepHf w-M.sweepRadius w)/M.xs^3|) w) =
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
    (M : (n : ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : ∀ᶠn in atTop,(M n).data.s ≤ 1/4)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/(M n).xs^2)
      atTop atTop)
    (C : ℝ) (hC : 0 ≤ C) :
    ∃eta : ℕ→ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∃p : (M n).Potential,∀v∈Icc (0:ℝ) 1,v ≤ C*(M n).xs →
        (∫u in 0..v,p.offFloorWeightedDiscrepancy u)/(M n).xs^4 ≤ eta n := by
  let charge n:=(M n).lam*((M n).data.rmin+(M n).cavityCapTravel)/(M n).xs^3
  let eta n:=C*charge n
  have hcharge n:0 ≤ charge n:=div_nonneg
    (mul_nonneg (M n).hlam.le
      (add_nonneg (M n).data.rmin_nonneg (M n).cavityCapTravel_nonneg))
    (pow_pos (M n).hxs 3).le
  have heta n:0 ≤ eta n:=mul_nonneg hC (hcharge n)
  have HEta:Tendsto eta atTop (𝓝 0):=by
    simpa only [mul_zero] using
      (actual_theta_zero_weighted_cap_and_origin_tendsto_zero_along_original_q
        hdelta dim hdim M).const_mul C
  refine ⟨eta,heta,HEta,?_⟩
  filter_upwards [actual_strength_flat_weighted_point_along_original_q
    hcl hAz dim M hs hlarge C hC] with n hn
  obtain ⟨p,hp⟩:=hn
  refine ⟨p,?_⟩
  intro v hv hvC
  have Hpoint:∀ᵐu,u∈Icc (0:ℝ) v → p.H ((M n).sweepRadius u) ≤ 0 →
      |(M n).sweepCoefficient u*
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u-(M n).sweepRadius u)|/(M n).xs^3 ≤
        charge n:=by
    filter_upwards [hp] with u hu hui hnonpos
    exact hu ⟨hui.1,hui.2.trans hv.2⟩ (hui.2.trans hvC) hnonpos
  have H:=p.offFloorWeightedDiscrepancy_mass_le hv (hcharge n) Hpoint
  have HS:=mul_le_mul_of_nonneg_left hvC
    (mul_nonneg (hcharge n) (pow_pos (M n).hxs 3).le)
  apply (div_le_iff₀ (pow_pos (M n).hxs 4)).2
  apply H.trans
  convert HS using 1
  dsimp only [eta]
  ring

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
