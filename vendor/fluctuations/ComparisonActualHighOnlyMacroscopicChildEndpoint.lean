module

public import ComparisonActualHighOnlyClocks
public import ComparisonActualHighOnlyMacroscopicEndpointCost
public import ComparisonNativeActualWeakStrengthLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
namespace ActualHighOnlyOverlapMinimum

theorem changed_endpoint_cost_le_parent_add_strength_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (T : ℝ) :
    comparisonEndpointL1Cost T
      (fun u=>M.b u-M.coefficient u)
      (fun u=>M.h u+M.coefficient u*M.R u) ≤
        comparisonEndpointL1Cost T M.b M.h+(3/4:ℝ)*M.lam := by
  have Hclocks := M.context.clocks_admissible M.alpha M.lam_mem
  have hbM : IntervalIntegrable M.b volume 0 1 :=
    (show MonotoneOn M.b (uIcc (0:ℝ) 1) by simpa only [uIcc_of_le zero_le_one] using M.hb).intervalIntegrable
  have hhM : IntervalIntegrable M.h volume 0 1 :=
    (show MonotoneOn M.h (uIcc (0:ℝ) 1) by simpa only [uIcc_of_le zero_le_one] using M.hh).intervalIntegrable
  have hbc : IntervalIntegrable (fun u=>M.b u-M.coefficient u) volume 0 1 :=
    (show MonotoneOn _ (uIcc (0:ℝ) 1) by simpa only [uIcc_of_le zero_le_one] using Hclocks.1).intervalIntegrable
  have hhc : IntervalIntegrable (fun u=>M.h u+M.coefficient u*M.R u) volume 0 1 :=
    (show MonotoneOn _ (uIcc (0:ℝ) 1) by simpa only [uIcc_of_le zero_le_one] using Hclocks.2.1).intervalIntegrable
  have HB := intervalIntegral.integral_mono_on zero_le_one (hbc.sub intervalIntegrable_const).abs
    ((hbM.sub intervalIntegrable_const).abs.add (intervalIntegrable_const (c:=M.lam))) (fun u hu=>by
      have He0 := M.coefficient_nonneg u
      have He := M.coefficient_le_lam u
      have Htri := abs_add_le (M.b u-T) (-M.coefficient u)
      rw [abs_neg,abs_of_nonneg He0] at Htri
      have Heq : M.b u-M.coefficient u-T=
        (M.b u-T)+(-M.coefficient u) := by ring
      rw [Heq]
      linarith only [Htri,He])
  have HH := intervalIntegral.integral_mono_on zero_le_one hhc.abs
    (hhM.abs.add (intervalIntegrable_const (c:=M.lam))) (fun u hu=>by
      have HR := omittedSweepQuantile_bounds zero_le_one ⟨M.context.hs.1,M.context.hs1⟩ M.context.hc M.context.hk M.context.hkc M.context.hm M.context.hM M.alpha u
      have He0 := M.coefficient_nonneg u
      have He := M.coefficient_le_lam u
      have Htri := abs_add_le (M.h u) (M.coefficient u*M.R u)
      rw [abs_of_nonneg (mul_nonneg He0 HR.1)] at Htri
      have Hmul := mul_le_mul_of_nonneg_left HR.2 He0
      linarith only [Htri,Hmul,He])
  rw [intervalIntegral.integral_add (hbM.sub intervalIntegrable_const).abs intervalIntegrable_const] at HB
  rw [intervalIntegral.integral_add hhM.abs intervalIntegrable_const] at HH
  simp only [intervalIntegral.integral_const,sub_zero,one_smul] at HB HH
  unfold comparisonEndpointL1Cost
  linarith only [HB,HH]

theorem changed_endpoint_cost_tendsto_zero_of_weak_bounded_call_high_only
    {m delta cl cu Az C0 Ct D Bclock T : ℝ} {N : ℕ→ℕ}
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ→ℝ) (hx : ∀n,0 < x n) (hxunit : ∀ᶠn in atTop,x n ≤ 1)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (x n)/(x n)^2)
      atTop (𝓝 0))
    (hparent : Tendsto (fun n=>comparisonEndpointL1Cost T (M n).b (M n).h) atTop (𝓝 0)) :
    Tendsto (fun n=>comparisonEndpointL1Cost T
      (fun u=>(M n).b u-(M n).coefficient u)
      (fun u=>(M n).h u+(M n).coefficient u*(M n).R u))
      atTop (𝓝 0) := by
  have hlam := actual_comparison_parameter_tendsto_zero_of_weak_bounded_call
    (hxunit.mono fun n hn=>⟨(M n).context.hd,(M n).hlam.le,hx n,hn,(M n).hld⟩) hweak
  have Hupper : Tendsto (fun n=>comparisonEndpointL1Cost T (M n).b (M n).h+(3/4:ℝ)*(M n).lam)
      atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using hparent.add (hlam.const_mul (3/4:ℝ))
  apply squeeze_zero (fun n=>by
    unfold comparisonEndpointL1Cost
    have HB:=intervalIntegral.integral_nonneg (μ:=volume) zero_le_one (fun u _=>abs_nonneg
      ((M n).b u-(M n).coefficient u-T))
    have HH:=intervalIntegral.integral_nonneg (μ:=volume) zero_le_one (fun u _=>abs_nonneg
      ((M n).h u+(M n).coefficient u*(M n).R u))
    positivity) (fun n=>changed_endpoint_cost_le_parent_add_strength_high_only (M n) T) Hupper

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
