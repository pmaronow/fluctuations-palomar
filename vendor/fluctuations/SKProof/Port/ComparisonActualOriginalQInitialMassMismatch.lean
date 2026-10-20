module

public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQInitialCharges
public import SKProof.Port.ComparisonActualOriginalQOriginalFloorMass
public import SKProof.Port.ComparisonActualOriginalQAllCapMismatch
public import ComparisonSignedCavityMinimumSourceClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4000000
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_thermal_nonneg_on_unit
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    0≤orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2 := by
  by_cases hu0 : u=0
  · subst u
    simp only [orderedPathB,orderedPathS,orderedPathPair_zero]
    norm_num
  · exact sub_nonneg.mpr (orderedPath_SK_bounds (n+1) (by omega) M.sweepBf M.sweepHf
      M.sweep_bf_monotone M.sweep_hf_monotone ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),hu.2⟩).2.2.1

theorem original_thermal_intervalIntegrable
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    IntervalIntegrable (fun u=>orderedPathB (n+1) M.sweepBf M.sweepHf u-
      (orderedPathS (n+1) M.sweepBf M.sweepHf u)^2) volume 0 1 :=
  physicalOrderedThermal_intervalIntegrable n M.sweepBf M.sweepHf M.sweep_bf_monotone M.sweep_hf_monotone

theorem Potential.initial_mass_squared_mismatch_le
    {M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) {v A : ℝ} (hv : v∈Icc (0:ℝ) 1) (hs : M.data.s≤v) (hA : 0≤A)
    (hamp : ∀u∈Ioc (0:ℝ) v,(orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u)^2≤A) :
    (∫u in 0..v,(orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u)^2)≤
      16*M.cavityCapTravel^2*v+
      2*(∫u in 0..v,orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2)+
      A*(2*M.data.s+M.data.N^(-delta)*M.data.U) := by
  let F:=fun u=>orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2
  let f:=fun u=>(orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u)^2
  have hi:=M.mass_squared_mismatch_intervalIntegrable.mono_set (by
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
      (p.positiveMassMask_integrable.mono_set (Icc_subset_Icc M.data.hs.1.le hv.2))
  have hiF := M.original_thermal_intervalIntegrable.mono_set (by
    rw [uIcc_of_le hv.1,uIcc_of_le zero_le_one];exact Icc_subset_Icc le_rfl hv.2)
  have hihiF := hiF.mono_set (by
    rw [uIcc_of_le hs,uIcc_of_le hv.1];exact Icc_subset_Icc M.data.hs.1.le le_rfl)
  have hiloF := hiF.mono_set (by
    rw [uIcc_of_le M.data.hs.1.le,uIcc_of_le hv.1];exact Icc_subset_Icc le_rfl hs)
  have hpoint:∀ᵐu∂volume.restrict (Icc M.data.s v),
      f u≤16*M.cavityCapTravel^2+2*F u+A*p.positiveMassMask u:=by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae p.all_nonpositive_squared_mismatch_ae_high_mass,
      ae_restrict_of_ae (volume.ae_ne (0:ℝ))] with u hu hpoint hu0
    have hui:u∈Icc M.data.s 1:=⟨hu.1,hu.2.trans hv.2⟩
    by_cases hp:p.H (M.sweepRadius u)≤0
    · have hm:=(p.positiveMassMask_zero_iff u).mpr hp
      rw [hm,mul_zero,add_zero]
      simpa only [f,F] using hpoint hui hp
    · have hm:p.positiveMassMask u=1:=by
        have HR:=M.sweepRadius_bounds u

        simp only [Potential.positiveMassMask,indicator_of_mem (show M.sweepRadius u∈p.positiveRadiusSet from ⟨HR,lt_of_not_ge hp⟩)]
      rw [hm,mul_one]
      have H:=hamp u ⟨lt_of_le_of_ne (M.data.hs.1.le.trans hu.1) (Ne.symm hu0),hu.2⟩
      have HF:=M.actual_thermal_nonneg_on_unit ⟨M.data.hs.1.le.trans hu.1,hu.2.trans hv.2⟩
      change 0≤F u at HF
      dsimp only [f]
      nlinarith only [H,HF,sq_nonneg M.cavityCapTravel]
  have hhigh:=intervalIntegral.integral_mono_ae_restrict hs hihi
    ((intervalIntegrable_const.add (hihiF.const_mul 2)).add (himask.const_mul A)) hpoint
  rw [intervalIntegral.integral_add (intervalIntegrable_const.add (hihiF.const_mul 2)) (himask.const_mul A),
    intervalIntegral.integral_add intervalIntegrable_const (hihiF.const_mul 2),
    intervalIntegral.integral_const,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hhigh
  simp only [smul_eq_mul] at hhigh
  have hmask:(∫u in M.data.s..v,p.positiveMassMask u)≤M.data.s+M.data.N^(-delta)*M.data.U:=by
    rw [intervalIntegral.integral_of_le hs,←integral_Icc_eq_integral_Ioc]
    apply le_trans _ p.positiveMassMask_mass_le
    apply setIntegral_mono_set p.positiveMassMask_integrable
      (ae_of_all _ (fun u=>by dsimp only [Potential.positiveMassMask];exact indicator_nonneg (fun _ _=>zero_le_one) _))
      (Eventually.of_forall (Icc_subset_Icc M.data.hs.1.le hv.2))
  have HM:=mul_le_mul_of_nonneg_left hmask hA
  have hFlow : 0≤∫u in 0..M.data.s,F u:=intervalIntegral.integral_nonneg M.data.hs.1.le
    (fun u hu=>M.actual_thermal_nonneg_on_unit ⟨hu.1,hu.2.trans M.data.hs1⟩)
  rw [←intervalIntegral.integral_add_adjacent_intervals hilo hihi,
    ←intervalIntegral.integral_add_adjacent_intervals hiloF hihiF]
  nlinarith only [hlow,hhigh,HM,hFlow,mul_nonneg (sq_nonneg M.cavityCapTravel) M.data.hs.1.le]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
