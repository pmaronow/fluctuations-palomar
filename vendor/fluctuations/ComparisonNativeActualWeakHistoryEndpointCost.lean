module

public import ComparisonNativeActualWeakHistoryGlobalClocks
public import ComparisonMacroscopicShellEndpoint

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {N : ℕ→ℕ}

theorem actual_weak_history_endpoint_cost_tendsto_zero
    {root M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (Hhistory : ActualWeakSelectedHistoryChain c0 root M)
    (Hroot : Tendsto (fun n=>comparisonEndpointL1Cost T (root n).b (root n).h)
      atTop (𝓝 0))
    (hhroot : ∀ᶠn in atTop,∀u,(root n).h u=0) :
    Tendsto (fun n=>comparisonEndpointL1Cost T (M n).b (M n).h) atTop (𝓝 0) := by
  obtain ⟨eta,heta,hetalim,Hpert⟩:=Hhistory.uniform_clock_perturbation
  have Hupper : Tendsto (fun n=>comparisonEndpointL1Cost T (root n).b (root n).h+
      (3/4:ℝ)*eta n) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero] using Hroot.add (hetalim.const_mul (3/4:ℝ))
  have Hbound : ∀ᶠn in atTop,comparisonEndpointL1Cost T (M n).b (M n).h ≤
      comparisonEndpointL1Cost T (root n).b (root n).h+(3/4:ℝ)*eta n := by
    filter_upwards [Hpert,hhroot] with n hn hnr
    have hbM : IntervalIntegrable (M n).b volume 0 1 :=
      (show MonotoneOn (M n).b (uIcc (0:ℝ) 1) from by simpa only [uIcc_of_le zero_le_one] using (M n).hb).intervalIntegrable
    have hhM : IntervalIntegrable (M n).h volume 0 1 :=
      (show MonotoneOn (M n).h (uIcc (0:ℝ) 1) from by simpa only [uIcc_of_le zero_le_one] using (M n).hh).intervalIntegrable
    have hbR : IntervalIntegrable (root n).b volume 0 1 :=
      (show MonotoneOn (root n).b (uIcc (0:ℝ) 1) from by simpa only [uIcc_of_le zero_le_one] using (root n).hb).intervalIntegrable
    have HB:=intervalIntegral.integral_mono_on zero_le_one
      (hbM.sub intervalIntegrable_const).abs
      ((hbR.sub intervalIntegrable_const).abs.add intervalIntegrable_const)
      (fun u hu=>by
        have H:=abs_sub_le ((M n).b u) ((root n).b u) T
        linarith only [H,(hn u hu).1])
    rw [intervalIntegral.integral_add (hbR.sub intervalIntegrable_const).abs intervalIntegrable_const] at HB
    simp only [intervalIntegral.integral_const,sub_zero,one_smul] at HB
    have HH:=intervalIntegral.integral_mono_on zero_le_one hhM.abs
      (intervalIntegrable_const (c:=eta n)) (fun u hu=>by
        simpa only [hnr u,sub_zero] using (hn u hu).2)
    simp only [intervalIntegral.integral_const,sub_zero,one_smul] at HH
    have HR : (∫u in (0:ℝ)..1, |(root n).h u|)=0 := by
      simp only [hnr,abs_zero,intervalIntegral.integral_zero]
    unfold comparisonEndpointL1Cost
    rw [HR]
    linarith only [HB,HH]
  apply squeeze_zero' _ Hbound Hupper
  exact Filter.Eventually.of_forall (fun n=>by
    unfold comparisonEndpointL1Cost
    have HB:=intervalIntegral.integral_nonneg (μ:=volume) zero_le_one (fun u _=>abs_nonneg ((M n).b u-T))
    have HH:=intervalIntegral.integral_nonneg (μ:=volume) zero_le_one (fun u _=>abs_nonneg ((M n).h u))
    positivity)

theorem actual_weak_shrinking_shell_history_endpoint_cost_tendsto_zero
    {root M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (Hhistory : ActualWeakSelectedHistoryChain c0 root M)
    {E : ℝ} (epsilon shell : ℕ→ℝ)
    (hepsilon : ∀n,epsilon n∈Icc (0:ℝ) E)
    (hshell : ∀n,shell n∈Icc (0:ℝ) 1) (hshelllim : Tendsto shell atTop (𝓝 0))
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T (epsilon n) (shell n) u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0) :
    Tendsto (fun n=>comparisonEndpointL1Cost T (M n).b (M n).h) atTop (𝓝 0) := by
  apply actual_weak_history_endpoint_cost_tendsto_zero Hhistory _ hh
  have Heq : (fun n=>comparisonEndpointL1Cost T (initialShellMatrixClock T (epsilon n) (shell n)) (fun _=>0)) =ᶠ[atTop] (fun n=>comparisonEndpointL1Cost T (root n).b (root n).h) := by
    filter_upwards [hb,hh] with n hn hn'
    have Hb : (root n).b=initialShellMatrixClock T (epsilon n) (shell n):=funext hn
    have Hh : (root n).h=(fun _=>0):=funext hn'
    rw [Hb,Hh]
  exact (shell_endpoint_cost_tendsto_zero hepsilon hshell hshelllim).congr' Heq

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
