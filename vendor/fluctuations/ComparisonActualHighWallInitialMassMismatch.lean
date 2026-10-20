module

public import ComparisonActualHighWallAllCapMismatch
public import ComparisonSignedCavityMinimumSourceClocks
public import ComparisonNativeOriginalLowErrorCutMoments

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel Cavity
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem full_mass_mean_monotone
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    MonotoneOn (orderedPathS (n+1) M.bf M.hf) (Icc (0:ℝ) 1) := by
  intro u hu v hv huv
  by_cases hu0 : u=0
  · subst u
    simpa only [orderedPathS,orderedPathPair_zero] using
      (physicalOrderedPathS_mem_unit n M.bf M.hf (M.data.bf_monotone M.alpha)
        (M.data.hf_monotone M.alpha) hv).1
  · have hp : 0<u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
    exact (orderedPath_SK_monotone (n+1) (by omega) M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)).1
      ⟨hp,hu.2⟩ ⟨hp.trans_le huv,hv.2⟩ huv

theorem full_mass_squared_mismatch_intervalIntegrable
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    IntervalIntegrable (fun u=>(orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u)^2) volume 0 1 := by
  have hi : IntervalIntegrable (fun u=>orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u) volume 0 1 :=
    (show MonotoneOn (orderedPathS (n+1) M.bf M.hf) (uIcc (0:ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one] using M.full_mass_mean_monotone).intervalIntegrable.sub
      ((M.data.wallRadius_lipschitz M.alpha).continuous.intervalIntegrable 0 1)
  have hb : ∀u∈Ioc (0:ℝ) 1,|orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u|≤1 := by
    intro u hu
    have HS:=physicalOrderedPathS_mem_unit n M.bf M.hf (M.data.bf_monotone M.alpha)
      (M.data.hf_monotone M.alpha) (Ioc_subset_Icc_self hu)
    have HR:=M.data.wallRadius_bounds M.alpha u
    exact abs_le.mpr ⟨by linarith only [HS.1,HR.2],by linarith only [HS.2,HR.1,M.data.hrbounds.1]⟩
  simpa only [pow_two] using Hierarchy.intervalIntegrable_mul_bounded hi hi hb

theorem Potential.full_positiveMassMask_intervalIntegrable
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) : IntervalIntegrable p.positiveMassMask volume 0 1 := by
  have hm : Measurable p.positiveMassMask := by
    rw [p.positiveMassMask_extended]
    exact measurable_const.indicator (measurableSet_lt measurable_const
      (p.starExtendedH_continuous.comp (M.data.wallRadius_lipschitz M.alpha).continuous).measurable)
  have H := intervalIntegrable_bounded_measurable_mul hm zero_le_one
    (fun u _=>by dsimp [Potential.positiveMassMask]; by_cases h:0<p.H (M.data.wallRadius M.alpha u) <;> simp [comparisonCalibrationFloor,h])
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ=>(1:ℝ)) volume 0 1)
  simpa only [mul_one] using H

theorem Potential.full_nonpositive_squared_mismatch_ae_mass
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) :
    ∀ᵐu,u∈Icc M.data.s 1→p.H (M.data.wallRadius M.alpha u)≤0→
      (orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u)^2≤
        16*(M.data.rmin+M.cavityCapTravel)^2+2*(orderedPathB (n+1) M.bf M.hf u-
          (orderedPathS (n+1) M.bf M.hf u)^2) := by
  have H := ae_inverse_pullback
    (inverseIntegralConstraints_lipschitz M.data.hm M.data.hM M.alpha.property)
    (fun u (_ : u∈Icc M.data.s 1)=>M.data.wallRadius_bounds M.alpha u)
    (fun u hu=>M.data.wallRadius_spec M.alpha hu) p.full_all_nonpositive_squared_mismatch_ae
  filter_upwards [H] with u hu hui hh
  have H' := hu hui hh
  simpa only [full_radius_thermal,radiusS,radiusB,M.data.wallRadius_spec M.alpha hui] using H'

theorem full_thermal_nonneg_on_unit
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    0≤orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2 := by
  by_cases hu0 : u=0
  · subst u
    simp only [orderedPathB,orderedPathS,orderedPathPair_zero]
    norm_num
  · exact sub_nonneg.mpr (orderedPath_SK_bounds (n+1) (by omega) M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),hu.2⟩).2.2.1

theorem full_original_thermal_intervalIntegrable
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    IntervalIntegrable (fun u=>orderedPathB (n+1) M.bf M.hf u-
      (orderedPathS (n+1) M.bf M.hf u)^2) volume 0 1 :=
  physicalOrderedThermal_intervalIntegrable n M.bf M.hf (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)

theorem Potential.full_initial_mass_squared_mismatch_le
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {v A : ℝ} (hv : v∈Icc (0:ℝ) 1) (hs : M.data.s≤v) (hA : 0≤A)
    (hamp : ∀u∈Ioc (0:ℝ) v,(orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u)^2≤A) :
    (∫u in 0..v,(orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u)^2)≤
      16*(M.data.rmin+M.cavityCapTravel)^2*v+
      2*(∫u in 0..v,orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2)+
      A*(M.data.s+M.data.N^(-delta)*comparisonSmallMass M.data.N M.data.E) := by
  let F:=fun u=>orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2
  let f:=fun u=>(orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u)^2
  have hi:=M.full_mass_squared_mismatch_intervalIntegrable.mono_set (by
    rw [uIcc_of_le hv.1,uIcc_of_le zero_le_one];exact Icc_subset_Icc le_rfl hv.2)
  have hilo:IntervalIntegrable f volume 0 M.data.s:=hi.mono_set (by
    rw [uIcc_of_le M.data.hs.1.le,uIcc_of_le hv.1];exact Icc_subset_Icc le_rfl hs)
  have hihi:IntervalIntegrable f volume M.data.s v:=hi.mono_set (by
    rw [uIcc_of_le hs,uIcc_of_le hv.1];exact Icc_subset_Icc M.data.hs.1.le le_rfl)
  have hlow:(∫u in 0..M.data.s,f u)≤A*M.data.s:=by
    have H:=intervalIntegral.integral_mono_ae_restrict M.data.hs.1.le hilo intervalIntegrable_const
      (by filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with u hu hu0
          exact hamp u ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),hu.2.trans hs⟩)
    simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm] using H
  have himask:IntervalIntegrable p.positiveMassMask volume M.data.s v:=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hs).mpr
      ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp p.full_positiveMassMask_intervalIntegrable |>.mono_set (Icc_subset_Icc M.data.hs.1.le hv.2))
  have hiF := M.full_original_thermal_intervalIntegrable.mono_set (by
    rw [uIcc_of_le hv.1,uIcc_of_le zero_le_one];exact Icc_subset_Icc le_rfl hv.2)
  have hihiF := hiF.mono_set (by
    rw [uIcc_of_le hs,uIcc_of_le hv.1];exact Icc_subset_Icc M.data.hs.1.le le_rfl)
  have hiloF := hiF.mono_set (by
    rw [uIcc_of_le M.data.hs.1.le,uIcc_of_le hv.1];exact Icc_subset_Icc le_rfl hs)
  have hpoint:∀ᵐu∂volume.restrict (Icc M.data.s v),
      f u≤16*(M.data.rmin+M.cavityCapTravel)^2+2*F u+A*p.positiveMassMask u:=by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae p.full_nonpositive_squared_mismatch_ae_mass,
      ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with u hu hpoint hu0
    have hui:u∈Icc M.data.s 1:=⟨hu.1,hu.2.trans hv.2⟩
    by_cases hp:p.H (M.data.wallRadius M.alpha u)≤0
    · have hm:=(p.positiveMassMask_zero_iff u).mpr hp
      rw [hm,mul_zero,add_zero]
      simpa only [f,F] using hpoint hui hp
    · have hm:p.positiveMassMask u=1:=by
        exact indicator_of_mem (show 0<p.H (M.data.wallRadius M.alpha u) from lt_of_not_ge hp) (fun _=>1)
      rw [hm,mul_one]
      have H:=hamp u ⟨lt_of_le_of_ne (M.data.hs.1.le.trans hu.1) (Ne.symm hu0),hu.2⟩
      have HF:=M.full_thermal_nonneg_on_unit ⟨M.data.hs.1.le.trans hu.1,hu.2.trans hv.2⟩
      change 0≤F u at HF
      dsimp only [f]
      nlinarith only [H,HF,sq_nonneg (M.data.rmin+M.cavityCapTravel)]
  have hhigh:=intervalIntegral.integral_mono_ae_restrict hs hihi
    ((intervalIntegrable_const.add (hihiF.const_mul 2)).add (himask.const_mul A)) hpoint
  rw [intervalIntegral.integral_add (intervalIntegrable_const.add (hihiF.const_mul 2)) (himask.const_mul A),
    intervalIntegral.integral_add intervalIntegrable_const (hihiF.const_mul 2),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hhigh
  simp only [smul_eq_mul] at hhigh
  have hmask:(∫u in M.data.s..v,p.positiveMassMask u)≤M.data.N^(-delta)*comparisonSmallMass M.data.N M.data.E := by
    rw [intervalIntegral.integral_of_le hs,integral_Ioc_eq_integral_Ioo]
    exact (p.positiveMassMask_on_band le_rfl hs hv.2).2
  have HM:=mul_le_mul_of_nonneg_left hmask hA
  have hFlow : 0≤∫u in 0..M.data.s,F u:=intervalIntegral.integral_nonneg M.data.hs.1.le
    (fun u hu=>M.full_thermal_nonneg_on_unit ⟨hu.1,hu.2.trans M.data.hs1⟩)
  rw [←intervalIntegral.integral_add_adjacent_intervals hilo hihi,
    ←intervalIntegral.integral_add_adjacent_intervals hiloF hihiF]
  nlinarith only [hlow,hhigh,HM,hFlow,mul_nonneg (sq_nonneg (M.data.rmin+M.cavityCapTravel)) M.data.hs.1.le]

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
