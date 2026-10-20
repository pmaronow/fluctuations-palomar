module

public import ComparisonNativeActualGeneralProfileHistoryAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 10000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ}

theorem actual_weak_bounded_shell_history_clock_data
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hT : 0 ≤ T)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℕ→ℝ)
    (hepsilon : ∀n,epsilon n∈Icc (0:ℝ) (((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3)))
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T (epsilon n) (shell n) u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualWeakSelectedHistoryChain c0 root M) :
    NativeSequentialPositiveBandClocks M T ∧
      (∃Cf : ℝ,0 ≤ Cf ∧ ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf) ∧
      ∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T) ∧ (M n).h 0=0 := by
  have Heps n : 0 ≤ epsilon n := (hepsilon n).1
  have Hsmall : Tendsto (fun n=>epsilon n/
      (comparisonLowerScale (root n).context.N (root n).context.E (root n).context.d)^2)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>div_nonneg (Heps n) (sq_nonneg _)) _
      (actual_lower_shell_covariance_defect_tendsto_zero hm hC0 dim hdim root)
    intro n
    exact div_le_div_of_nonneg_right (hepsilon n).2 (sq_nonneg _)
  refine ⟨actual_weak_varying_shell_history_sequential_clocks hm hdelta hcl hAz hC0 hc0 hc01
    hmargin hcapmargin hgapmargin hdim epsilon shell Heps Hsmall hb hh Hhistory,?_,?_⟩
  · exact actual_weak_varying_history_small_source_clocks hm hdelta hcl hAz hC0 hc0
      hmargin hcapmargin dim hdim root M epsilon shell Heps hT hb hh Hhistory
  · obtain ⟨ps,Hps⟩:=Hhistory.literal_readout_varying_shell epsilon shell hb hh
    filter_upwards [Hps] with n hn
    exact (M n).actual_shell_history_total_root (ps.map (fun P=>P n)) (Heps n)
      hn.2.1 hn.2.2

def actual_bounded_shell_profile_history
    {dim : ℕ→ℕ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hT : 0 < T)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℕ→ℝ)
    (hepsilon : ∀n,epsilon n∈Icc (0:ℝ) (((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3)))
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T (epsilon n) (shell n) u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualWeakSelectedHistoryChain c0 root M)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)) :
    ActualNativeProfileHistory M T c0 where
  root := root
  epsilon := epsilon
  shell := shell
  hepsilon := fun n=>(hepsilon n).1
  hb := hb
  hh := hh
  history := Hhistory
  sequential := (actual_weak_bounded_shell_history_clock_data hm hdelta hcl hAz hC0 hc0 hc01 hT.le
    hmargin hcapmargin hgapmargin dim hdim root M epsilon shell hepsilon hb hh Hhistory).1
  xs_zero := hxs
  hT := hT

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
