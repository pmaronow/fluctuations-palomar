module

public import ComparisonNativeActualWeakHistoryEndpointCost
public import ComparisonActualHighWallSourceClockBudget
public import ComparisonActualHighWallFixedCovarianceMargins

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 14000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {dim : ℕ→ℕ}

theorem actual_weak_general_bare_history_endpoint_cost_tendsto_zero
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakSelectedHistoryChain c0 root M)
    (Hroot : Tendsto (fun n=>comparisonEndpointL1Cost T (root n).b (root n).h) atTop (𝓝 0)) :
    Tendsto (fun n=>comparisonEndpointL1Cost T (M n).b (M n).h) atTop (𝓝 0) := by
  obtain ⟨eta,heta,hetalim,Hpert⟩:=H.uniform_clock_perturbation
  have Hupper : Tendsto (fun n=>comparisonEndpointL1Cost T (root n).b (root n).h+
      (3/4:ℝ)*eta n) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using Hroot.add (hetalim.const_mul (3/4:ℝ))
  have Hbound : ∀ᶠn in atTop,comparisonEndpointL1Cost T (M n).b (M n).h ≤
      comparisonEndpointL1Cost T (root n).b (root n).h+(3/4:ℝ)*eta n := by
    filter_upwards [Hpert] with n hn
    have hbM : IntervalIntegrable (M n).b volume 0 1 := (show MonotoneOn (M n).b (uIcc (0:ℝ) 1) from by
      simpa only [uIcc_of_le zero_le_one] using (M n).hb).intervalIntegrable
    have hhM : IntervalIntegrable (M n).h volume 0 1 := (show MonotoneOn (M n).h (uIcc (0:ℝ) 1) from by
      simpa only [uIcc_of_le zero_le_one] using (M n).hh).intervalIntegrable
    have hbR : IntervalIntegrable (root n).b volume 0 1 := (show MonotoneOn (root n).b (uIcc (0:ℝ) 1) from by
      simpa only [uIcc_of_le zero_le_one] using (root n).hb).intervalIntegrable
    have hhR : IntervalIntegrable (root n).h volume 0 1 := (show MonotoneOn (root n).h (uIcc (0:ℝ) 1) from by
      simpa only [uIcc_of_le zero_le_one] using (root n).hh).intervalIntegrable
    have HB:=intervalIntegral.integral_mono_on zero_le_one
      (hbM.sub intervalIntegrable_const).abs
      ((hbR.sub intervalIntegrable_const).abs.add intervalIntegrable_const)
      (fun u hu=>by
        have H':=abs_sub_le ((M n).b u) ((root n).b u) T
        linarith only [H',(hn u hu).1])
    have HH:=intervalIntegral.integral_mono_on zero_le_one hhM.abs
      (hhR.abs.add intervalIntegrable_const) (fun u hu=>by
        have H':=abs_sub_le ((M n).h u) ((root n).h u) 0
        simp only [sub_zero] at H'
        linarith only [H',(hn u hu).2])
    rw [intervalIntegral.integral_add (hbR.sub intervalIntegrable_const).abs intervalIntegrable_const] at HB
    rw [intervalIntegral.integral_add hhR.abs intervalIntegrable_const] at HH
    simp only [intervalIntegral.integral_const,sub_zero,one_smul] at HB HH
    unfold comparisonEndpointL1Cost
    linarith only [HB,HH]
  apply squeeze_zero' _ Hbound Hupper
  exact Eventually.of_forall (fun n=>by
    unfold comparisonEndpointL1Cost
    have HB:=intervalIntegral.integral_nonneg (μ:=volume) zero_le_one (fun u _=>abs_nonneg ((M n).b u-T))
    have HH:=intervalIntegral.integral_nonneg (μ:=volume) zero_le_one (fun u _=>abs_nonneg ((M n).h u))
    positivity)

end NativeOverlapMinimum
namespace ActualHighWallData
variable {n : ℕ} {delta : ℝ}

theorem endpoint_L1_cost_le (a : ActualHighWallData n delta) (alpha : a.Profile) :
    comparisonEndpointL1Cost a.T (a.b alpha) (a.h alpha) ≤ a.T*a.s+a.d^2 := by
  have hT : 0 < a.T:=a.hepsilon.1.trans a.hepsilon.2
  have Had:=a.admissible alpha
  have Hbounds u (hu : u∈Icc (0:ℝ) 1) :
      0 ≤ a.b alpha u ∧ a.b alpha u ≤ a.T ∧ 0 ≤ a.h alpha u ∧ a.h alpha u ≤ a.d^2 := by
    have Hb:=Had.2.2.1.trans (Had.1 (by norm_num) hu hu.1)
    have Hh:=Had.2.2.2.trans (Had.2.1 (by norm_num) hu hu.1)
    have Htot:=a.total_clock_le alpha u hu
    have Hfield:=a.field_le_strength alpha hu
    rw [(a.clock_coe alpha hu).1,(a.clock_coe alpha hu).2] at Htot
    rw [(a.clock_coe alpha hu).2] at Hfield
    exact ⟨Hb,by linarith,Hh,Hfield⟩
  have Hmatrix u (hu : u∈Icc (0:ℝ) 1) : |a.b alpha u-a.T| ≤ a.T := by
    obtain ⟨hb,hbT,_,_⟩:=Hbounds u hu
    rw [abs_of_nonpos (sub_nonpos.mpr hbT)]
    linarith
  have Hhigh u (hu : u∈Icc a.s 1) : |a.b alpha u-a.T| ≤ a.d^2 := by
    have hbT:=(Hbounds u ⟨a.hs.1.le.trans hu.1,hu.2⟩).2.1
    rw [abs_of_nonpos (sub_nonpos.mpr hbT)]
    linarith [a.changed_high_matrix_lower alpha hu]
  have Hfield u (hu : u∈Icc (0:ℝ) 1) : |a.h alpha u| ≤ a.d^2 := by
    have H:=Hbounds u hu
    simpa only [abs_of_nonneg H.2.2.1] using H.2.2.2
  have hbI : IntervalIntegrable (fun u=>|a.b alpha u-a.T|) volume 0 1 :=
    ((show MonotoneOn (a.b alpha) (uIcc (0:ℝ) 1) from by simpa only [uIcc_of_le zero_le_one] using Had.1).intervalIntegrable.sub intervalIntegrable_const).abs
  have hhI : IntervalIntegrable (fun u=>|a.h alpha u|) volume 0 1 :=
    (show MonotoneOn (a.h alpha) (uIcc (0:ℝ) 1) from by simpa only [uIcc_of_le zero_le_one] using Had.2.1).intervalIntegrable.abs
  have Hlow:=intervalIntegral.integral_mono_on a.hs.1.le
    (hbI.mono_set (by rw [uIcc_of_le a.hs.1.le,uIcc_of_le zero_le_one];exact Icc_subset_Icc le_rfl a.hs1))
    intervalIntegrable_const (fun u hu=>Hmatrix u ⟨hu.1,hu.2.trans a.hs1⟩)
  have Hhi:=intervalIntegral.integral_mono_on a.hs1
    (hbI.mono_set (by rw [uIcc_of_le a.hs1,uIcc_of_le zero_le_one];exact Icc_subset_Icc a.hs.1.le le_rfl))
    intervalIntegrable_const Hhigh
  have Hf:=intervalIntegral.integral_mono_on zero_le_one hhI intervalIntegrable_const Hfield
  have Hsplit:=intervalIntegral.integral_add_adjacent_intervals
    (hbI.mono_set (by rw [uIcc_of_le a.hs.1.le,uIcc_of_le zero_le_one];exact Icc_subset_Icc le_rfl a.hs1))
    (hbI.mono_set (by rw [uIcc_of_le a.hs1,uIcc_of_le zero_le_one];exact Icc_subset_Icc a.hs.1.le le_rfl))
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at Hlow Hhi Hf
  have Hbm : (∫u in (0:ℝ)..1,|a.b alpha u-a.T|) ≤ a.T*a.s+a.d^2 := by
    have Hsmall : (1-a.s)*a.d^2 ≤ a.d^2:=by nlinarith [a.hs.1.le,sq_nonneg a.d]
    linarith only [Hsplit,Hlow,Hhi,Hsmall]
  unfold comparisonEndpointL1Cost
  have HBnonneg := intervalIntegral.integral_nonneg (μ:=volume) zero_le_one (fun u _=>abs_nonneg (a.b alpha u-a.T))
  have HFnonneg := intervalIntegral.integral_nonneg (μ:=volume) zero_le_one (fun u _=>abs_nonneg (a.h alpha u))
  have Hpos : 0 ≤ a.T*a.s:=mul_nonneg hT.le a.hs.1.le
  nlinarith only [Hbm,Hf,HBnonneg,HFnonneg,Hpos,sq_nonneg a.d]

theorem endpoint_L1_cost_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock T : ℝ} {dim : ℕ→ℕ}
    (P : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hT : ∀ᶠn in atTop,(P n).data.T=T)
    (hs : Tendsto (fun n=>(P n).data.s) atTop (𝓝 0))
    (hd : Tendsto (fun n=>(P n).data.d) atTop (𝓝 0)) :
    Tendsto (fun n=>comparisonEndpointL1Cost T ((P n).data.b (P n).alpha)
      ((P n).data.h (P n).alpha)) atTop (𝓝 0) := by
  have Hlim : Tendsto (fun n=>T*(P n).data.s+(P n).data.d^2) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ)≠0),add_zero] using
      (hs.const_mul T).add (hd.pow 2)
  apply squeeze_zero' _ _ Hlim
  · exact Eventually.of_forall (fun n=>by
      unfold comparisonEndpointL1Cost
      have HB:=intervalIntegral.integral_nonneg (μ:=volume) zero_le_one
        (fun u _=>abs_nonneg ((P n).data.b (P n).alpha u-T))
      have HH:=intervalIntegral.integral_nonneg (μ:=volume) zero_le_one
        (fun u _=>abs_nonneg ((P n).data.h (P n).alpha u))
      positivity)
  · filter_upwards [hT] with n hn
    simpa only [hn] using (P n).data.endpoint_L1_cost_le (P n).alpha

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
