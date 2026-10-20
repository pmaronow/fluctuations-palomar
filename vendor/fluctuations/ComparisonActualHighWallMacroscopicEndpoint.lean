module

public import ComparisonActualHighWallMacroscopicHighOnlyChildExclusion
public import ComparisonNativeActualWeakStrengthLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 16000000
namespace ActualHighWallData
variable {n:ℕ} {delta:ℝ} (a:ActualHighWallData n delta)

theorem changed_matrix_distance_le_total (alpha:a.Profile) {u:ℝ} (hu:u∈Icc (0:ℝ) 1):
    |a.b alpha u-a.T| ≤ a.T:=by
  have HC:=a.admissible alpha
  have Hb:0 ≤ a.b alpha u:=HC.2.2.1.trans (HC.1 ⟨le_rfl,zero_le_one⟩ hu hu.1)
  have Hh:0 ≤ a.h alpha u:=HC.2.2.2.trans (HC.2.1 ⟨le_rfl,zero_le_one⟩ hu hu.1)
  have HT:=a.total_clock_le alpha u hu
  rw [(a.clock_coe alpha hu).1,(a.clock_coe alpha hu).2] at HT
  rw [abs_of_nonpos (by linarith : a.b alpha u-a.T ≤ 0)]
  linarith

theorem high_matrix_distance_le_square (alpha:a.Profile) {u:ℝ} (hu:u∈Icc a.s 1):
    |a.b alpha u-a.T| ≤ a.d^2:=by
  dsimp only [b]
  rw [wallChangedMatrix_on a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
    a.T a.epsilon a.theta alpha hu]
  rw [show a.T-a.g (constrainedQuantile a.hr a.hc a.hk a.hkc a.hm a.hM alpha ⟨u,hu⟩)-a.T=
    -a.g (constrainedQuantile a.hr a.hc a.hk a.hkc a.hm a.hM alpha ⟨u,hu⟩) by ring,
    abs_neg,abs_of_nonneg (laplaceComparisonStrength_nonneg a.d _ (sq_nonneg a.d))]
  exact laplaceComparisonStrength_le a.d (sq_nonneg a.d) _

theorem changed_field_le_square (alpha:a.Profile) {u:ℝ} (hu:u∈Icc (0:ℝ) 1):
    |a.h alpha u| ≤ a.d^2:=by
  have HC:=a.admissible alpha
  have Hh:0 ≤ a.h alpha u:=HC.2.2.2.trans (HC.2.1 ⟨le_rfl,zero_le_one⟩ hu hu.1)
  rw [abs_of_nonneg Hh]
  by_cases HS:u<a.s
  · have H:=a.low_field_cubic alpha hu HS
    rw [(a.clock_coe alpha hu).2] at H
    have HD:=mul_le_mul_of_nonneg_left a.hd1 (sq_nonneg a.d)
    nlinarith [sq_nonneg a.d]
  · have HS':u∈Icc a.s 1:=⟨le_of_not_gt HS,hu.2⟩
    dsimp only [h]
    rw [wallChangedField_on a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous
      a.T a.epsilon a.theta a.tau a.d alpha HS']
    have HR:=(constrainedQuantile a.hr a.hc a.hk a.hkc a.hm a.hM alpha ⟨u,HS'⟩).property
    have HE:=laplaceComparisonStrength_le a.d (sq_nonneg a.d)
      (constrainedQuantile a.hr a.hc a.hk a.hkc a.hm a.hM alpha ⟨u,HS'⟩)
    have HE0:=laplaceComparisonStrength_nonneg a.d
      (constrainedQuantile a.hr a.hc a.hk a.hkc a.hm a.hM alpha ⟨u,HS'⟩) (sq_nonneg a.d)
    exact (mul_le_mul_of_nonneg_left HR.2 HE0).trans (by simpa using HE)

theorem changed_endpoint_cost_le_cutoff_and_square (alpha:a.Profile):
    comparisonEndpointL1Cost a.T (a.b alpha) (a.h alpha) ≤ a.T*a.s/4+(3/4:ℝ)*a.d^2:=by
  have HC:=a.admissible alpha
  have Hb:IntervalIntegrable (a.b alpha) volume 0 1:=
    (show MonotoneOn (a.b alpha) (uIcc (0:ℝ) 1) by simpa only [uIcc_of_le zero_le_one] using HC.1).intervalIntegrable
  have Hh:IntervalIntegrable (a.h alpha) volume 0 1:=
    (show MonotoneOn (a.h alpha) (uIcc (0:ℝ) 1) by simpa only [uIcc_of_le zero_le_one] using HC.2.1).intervalIntegrable
  have HI:IntervalIntegrable (fun u=>|a.b alpha u-a.T|) volume 0 1:=(Hb.sub intervalIntegrable_const).abs
  have HIs:IntervalIntegrable (fun u=>|a.b alpha u-a.T|) volume 0 a.s:=HI.mono_set (by
    rw [uIcc_of_le a.hs.1.le,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl a.hs1)
  have HIt:IntervalIntegrable (fun u=>|a.b alpha u-a.T|) volume a.s 1:=HI.mono_set (by
    rw [uIcc_of_le a.hs1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc a.hs.1.le le_rfl)
  have Hlow:=intervalIntegral.integral_mono_on a.hs.1.le HIs (intervalIntegrable_const (c:=a.T))
    (fun u hu=>a.changed_matrix_distance_le_total alpha ⟨hu.1,hu.2.trans a.hs1⟩)
  have Hhigh:=intervalIntegral.integral_mono_on a.hs1 HIt (intervalIntegrable_const (c:=a.d^2))
    (fun u hu=>a.high_matrix_distance_le_square alpha hu)
  have HH:=intervalIntegral.integral_mono_on zero_le_one Hh.abs (intervalIntegrable_const (c:=a.d^2))
    (fun u hu=>a.changed_field_le_square alpha hu)
  have HB:=intervalIntegral.integral_add_adjacent_intervals HIs HIt
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at Hlow Hhigh HH
  unfold comparisonEndpointL1Cost
  nlinarith [mul_nonneg a.hs.1.le (sq_nonneg a.d)]

end ActualHighWallData
namespace ActualHighWallOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T:ℝ} {N:ℕ→ℕ}

theorem changed_endpoint_and_radius_origin_zero_of_weak_bounded_test
    (M:(n:ℕ)→ActualHighWallOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)
    (hunit:∀ᶠn in atTop,(M n).xs ≤ 1)
    (hT:∀n,(M n).data.T=T)
    (hs:Tendsto (fun n=>(M n).data.s) atTop (𝓝 0))
    (hweak:Tendsto (fun n=>(M n).data.g ((M n).xs)/(M n).xs^2) atTop (𝓝 0)):
    Tendsto (fun n=>(M n).data.rmin) atTop (𝓝 0) ∧
      Tendsto (fun n=>comparisonEndpointL1Cost T ((M n).data.b (M n).alpha) ((M n).data.h (M n).alpha)) atTop (𝓝 0):=by
  have Hlam:=actual_comparison_parameter_tendsto_zero_of_weak_bounded_call
    (hunit.mono fun n hn=>⟨(M n).data.hd,(sq_nonneg (M n).data.d),(M n).hxs,hn,le_rfl⟩) hweak
  have Hd:Tendsto (fun n=>(M n).data.d) atTop (𝓝 0):=by
    have H:=Real.continuous_sqrt.continuousAt.tendsto.comp Hlam
    simpa only [Function.comp_def,Real.sqrt_sq (M _).data.hd.le,Real.sqrt_zero] using H
  have Hr:Tendsto (fun n=>(M n).data.rmin) atTop (𝓝 0):=
    squeeze_zero (fun n=>(M n).data.hrbounds.1.le) (fun n=>(M n).data.hrbounds.2.1)
      (by simpa using Hd.div_const 4)
  refine ⟨Hr,?_⟩
  have Hupper:Tendsto (fun n=>T*(M n).data.s/4+(3/4:ℝ)*(M n).data.d^2) atTop (𝓝 0):=by
    simpa only [mul_zero,zero_div,add_zero] using (hs.const_mul T |>.div_const 4).add (Hlam.const_mul (3/4:ℝ))
  apply squeeze_zero (fun n=>actual_high_only_endpoint_l1_cost_nonneg T ((M n).data.b (M n).alpha) ((M n).data.h (M n).alpha))
    (fun n=>by simpa only [hT n] using (M n).data.changed_endpoint_cost_le_cutoff_and_square (M n).alpha) Hupper

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
