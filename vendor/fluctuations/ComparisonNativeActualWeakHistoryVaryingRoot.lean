module

public import ComparisonNativeActualWeakSelectedHistoryClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {N : ℕ→ℕ}

theorem actual_initial_varying_shell_sequential_clocks
    (root : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℕ→ℝ) (hepsilon : ∀n,0 ≤ epsilon n)
    (hsmall : Tendsto (fun n=>epsilon n/
      (comparisonLowerScale (root n).context.N (root n).context.E (root n).context.d)^2)
      atTop (𝓝 0))
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T (epsilon n) (shell n) u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0) :
    NativeSequentialPositiveBandClocks root T := by
  intro y hy hay C eps hC heps
  filter_upwards [hsmall.eventually (gt_mem_nhds heps),hay,hb,hh] with n hn hny hnb hnh
  intro u hu
  let a:=comparisonLowerScale (root n).context.N (root n).context.E (root n).context.d
  have ha : 0 < a := by
    dsimp only [a,comparisonLowerScale]
    exact div_pos (mul_pos (Real.sqrt_pos.mpr (root n).context.hN) (root n).context.hE) (root n).context.hd
  have hypos : 0 < y n:=ha.trans_le hny
  have Hdefect : epsilon n ≤ eps*(y n)^2 := by
    have H:= (div_le_iff₀ (sq_pos_of_pos ha)).mp hn.le
    have Hp:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hny 2) heps.le
    exact H.trans Hp
  have Hbase : |(root n).b u-T| ≤ epsilon n := by
    rw [hnb u]
    unfold initialShellMatrixClock
    split_ifs
    · have Heq : T-epsilon n-T= -epsilon n := by ring
      rw [Heq,abs_neg,abs_of_nonneg (hepsilon n)]
    · simpa using hepsilon n
  refine ⟨Hbase.trans Hdefect,?_⟩
  rw [hnh u,abs_zero]
  exact mul_nonneg heps.le (pow_nonneg hypos.le 3)

theorem actual_weak_varying_shell_history_sequential_clocks
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hN : Tendsto N atTop atTop)
    {root M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (epsilon shell : ℕ→ℝ) (hepsilon : ∀n,0 ≤ epsilon n)
    (hsmall : Tendsto (fun n=>epsilon n/
      (comparisonLowerScale (root n).context.N (root n).context.E (root n).context.d)^2)
      atTop (𝓝 0))
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T (epsilon n) (shell n) u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualWeakSelectedHistoryChain c0 root M) :
    NativeSequentialPositiveBandClocks M T :=
  Hhistory.sequential_clocks hm hdelta hcl hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin hN
    (actual_initial_varying_shell_sequential_clocks root epsilon shell hepsilon hsmall hb hh)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
