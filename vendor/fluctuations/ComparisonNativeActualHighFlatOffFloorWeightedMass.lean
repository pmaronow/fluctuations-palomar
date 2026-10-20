module

public import ComparisonNativeActualHighFlatWeightedPointAlong
public import ComparisonNativeActualInitialMassMismatch

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 20000000
namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def Potential.offFloorWeightedDiscrepancy
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock} (p : M.Potential) (u : ℝ) : ℝ :=
  |laplaceComparisonStrength M.context.d M.lam (M.R u)*
    (orderedPathS (n+1) M.bf M.hf u-M.R u)| * (1-p.positiveMassMask u)

theorem Potential.offFloorWeightedDiscrepancy_intervalIntegrable
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock} (p : M.Potential) :
    IntervalIntegrable p.offFloorWeightedDiscrepancy volume 0 1 := by
  have hD:IntervalIntegrable (fun u=>orderedPathS (n+1) M.bf M.hf u-M.R u) volume 0 1:=
    (show MonotoneOn (orderedPathS (n+1) M.bf M.hf) (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one] using M.mass_mean_monotone).intervalIntegrable.sub
      ((comparisonSweepQuantile_continuous M.context.hc M.context.hk M.context.hkc
        M.context.hm M.context.hM M.alpha).intervalIntegrable 0 1)
  have he:IntervalIntegrable (fun u=>laplaceComparisonStrength M.context.d M.lam (M.R u)) volume 0 1:=
    ((laplaceComparisonStrength_contDiff M.context.d M.lam).continuous.comp
      (comparisonSweepQuantile_continuous M.context.hc M.context.hk M.context.hkc
        M.context.hm M.context.hM M.alpha)).intervalIntegrable 0 1
  have heb:∀u∈Ioc (0:ℝ) 1,|laplaceComparisonStrength M.context.d M.lam (M.R u)| ≤ M.lam:=by
    intro u _
    rw [abs_of_pos (laplaceComparisonStrength_pos M.context.d M.hlam _)]
    exact laplaceComparisonStrength_le M.context.d M.hlam.le _
  have hW:IntervalIntegrable (fun u=>|laplaceComparisonStrength M.context.d M.lam (M.R u)*
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
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock} (p : M.Potential) (u : ℝ) :
    0 ≤ p.offFloorWeightedDiscrepancy u := by
  dsimp only [offFloorWeightedDiscrepancy,Potential.positiveMassMask]
  by_cases H:M.R u∈p.positiveRadiusSet
  · simp only [indicator_of_mem H,sub_self,mul_zero]
    exact le_rfl
  · rw [indicator_of_notMem H,sub_zero,mul_one]
    exact abs_nonneg _

theorem Potential.offFloorWeightedDiscrepancy_mass_le
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock} (p : M.Potential)
    {v loss : ℝ} (hv : v∈Icc (0:ℝ) 1) (hloss : 0 ≤ loss)
    (Hpoint : ∀ᵐu,u∈Icc (0:ℝ) v → p.H (M.R u) ≤ 0 →
      |laplaceComparisonStrength M.context.d M.lam (M.R u)*
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
        have HR:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
          M.context.hm M.context.hM M.alpha u
        simp only [Potential.positiveMassMask,indicator_of_mem (show M.R u∈p.positiveRadiusSet from ⟨HR,lt_of_not_ge hp⟩)]
      dsimp only [offFloorWeightedDiscrepancy]
      rw [HM,sub_self,mul_zero]
      exact mul_nonneg hloss (pow_pos M.hxs 3).le
  have H:=intervalIntegral.integral_mono_ae_restrict hv.1 hi (intervalIntegrable_const) HX
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using H

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
