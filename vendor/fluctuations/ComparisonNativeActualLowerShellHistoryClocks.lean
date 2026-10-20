module

public import ComparisonNativeActualLowerShellClockScale
public import ComparisonNativeActualWeakHistoryVaryingSourceClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option maxHeartbeats 6000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ}

theorem actual_weak_lower_shell_history_clock_data
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hT : 0 ≤ T)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (shell : ℕ→ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=
      initialShellMatrixClock T (((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3)) (shell n) u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualWeakSelectedHistoryChain c0 root M) :
    NativeSequentialPositiveBandClocks M T ∧
      (∃Cf : ℝ,0 ≤ Cf ∧ ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T) ∧ (M n).h 0=0 := by
  let epsilon:=fun n=>(root n).context.N^(-(1:ℝ)/3)
  have hepsilon : ∀n,0 ≤ epsilon n := fun n=>Real.rpow_nonneg (root n).context.hN.le _
  have hb' : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T (epsilon n) (shell n) u := by
    simpa only [epsilon,NativeOverlapContext.N] using hb
  have Hsmall:=actual_lower_shell_covariance_defect_tendsto_zero hm hC0 dim hdim root
  refine ⟨actual_weak_varying_shell_history_sequential_clocks hm hdelta hcl hAz hC0 hc0 hc01
    hmargin hcapmargin hgapmargin hdim epsilon shell hepsilon Hsmall hb' hh Hhistory,?_,?_⟩
  · exact actual_weak_varying_history_small_source_clocks hm hdelta hcl hAz hC0 hc0
      hmargin hcapmargin dim hdim root M epsilon shell hepsilon hT hb' hh Hhistory
  · obtain ⟨ps,Hps⟩:=Hhistory.literal_readout_varying_shell epsilon shell hb' hh
    filter_upwards [Hps] with n hn
    exact (M n).actual_shell_history_total_root (ps.map (fun P=>P n)) (hepsilon n)
      hn.2.1 hn.2.2

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
