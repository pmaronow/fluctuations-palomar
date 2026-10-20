module

public import ComparisonNativeActualWeakHistoryOperations
public import ComparisonNativeActualWeakHistoryGlobalClocks
public import ComparisonNativeActualWeakHistoryVaryingSourceClocks
public import ComparisonNativeActualHistoryScalarEndpointLimits

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option maxHeartbeats 16000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ} {dim : ℕ→ℕ}

theorem eventually_subsequence_extend {a b : ℕ→ℝ} {phi : ℕ→ℕ}
    (hphi : StrictMono phi) (P : ℕ→ℝ→Prop)
    (ha : ∀ᶠk in atTop,P (phi k) (a k))
    (hb : ∀ᶠn in atTop,P n (b n)) :
    ∀ᶠn in atTop,P n (Function.extend phi a b n) := by
  obtain ⟨k0,hk0⟩:=eventually_atTop.mp ha
  filter_upwards [hb,eventually_ge_atTop (phi k0)] with n hn hlarge
  by_cases hmem : ∃k,phi k=n
  · obtain ⟨k,rfl⟩:=hmem
    have hk : k0 ≤ k := by
      by_contra hno
      exact not_lt_of_ge hlarge (hphi (lt_of_not_ge hno))
    rw [hphi.injective.extend_apply]
    exact hk0 k hk
  · rw [Function.extend_apply' a b n hmem]
    exact hn

theorem tendsto_subsequence_extend {a b : ℕ→ℝ} {phi : ℕ→ℕ} {limit : ℝ}
    (hphi : StrictMono phi) (ha : Tendsto a atTop (𝓝 limit))
    (hb : Tendsto b atTop (𝓝 limit)) :
    Tendsto (Function.extend phi a b) atTop (𝓝 limit) := by
  rw [tendsto_def]
  intro s hs
  exact eventually_subsequence_extend hphi (fun _ v=>v∈s) (ha.eventually hs) (hb.eventually hs)

theorem NativeSequentialPositiveBandClocks.comp
    {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : NativeSequentialPositiveBandClocks M T)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (phi : ℕ→ℕ) (hphi : StrictMono phi) :
    NativeSequentialPositiveBandClocks (fun n=>M (phi n)) T := by
  intro y hy hay C eps hC heps
  let z:=Function.extend phi y (fun n=>(M n).xs)
  have hz : Tendsto z atTop (𝓝 0) := tendsto_subsequence_extend hphi hy hx
  have haz : ∀ᶠn in atTop,
      comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d ≤ z n :=
    eventually_subsequence_extend hphi
      (fun n v=>comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d ≤ v)
      hay (Eventually.of_forall (fun n=>(M n).hscale))
  have Hresult:=hphi.tendsto_atTop.eventually (H z hz haz C eps hC heps)
  filter_upwards [Hresult] with n hn
  simpa only [z,hphi.injective.extend_apply] using hn

structure ActualNativeProfileHistory
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (T c0 : ℝ) where
  root : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock
  epsilon : ℕ→ℝ
  shell : ℕ→ℝ
  hepsilon : ∀n,0 ≤ epsilon n
  hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T (epsilon n) (shell n) u
  hh : ∀ᶠn in atTop,∀u,(root n).h u=0
  history : ActualWeakSelectedHistoryChain c0 root M
  sequential : NativeSequentialPositiveBandClocks M T
  xs_zero : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)
  hT : 0 < T

namespace ActualNativeProfileHistory
variable {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}

def comp (G : ActualNativeProfileHistory M T c0) (phi : ℕ→ℕ) (hphi : StrictMono phi) :
    ActualNativeProfileHistory (fun n=>M (phi n)) T c0 where
  root := fun n=>G.root (phi n)
  epsilon := fun n=>G.epsilon (phi n)
  shell := fun n=>G.shell (phi n)
  hepsilon := fun n=>G.hepsilon (phi n)
  hb := hphi.tendsto_atTop.eventually G.hb
  hh := hphi.tendsto_atTop.eventually G.hh
  history := G.history.comp phi hphi.tendsto_atTop
  sequential := G.sequential.comp G.xs_zero phi hphi
  xs_zero := G.xs_zero.comp hphi.tendsto_atTop
  hT := G.hT

theorem literal_readout (G : ActualNativeProfileHistory M T c0) :
    ∃ps : List ((n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock),
      ∀ᶠn in atTop,
        ActualHistoryCutoffChain c0 (ps.map (fun P=>P n)) (M n) ∧
        (∀u,(M n).b u=historyMatrixClock T (G.epsilon n) (G.shell n)
          ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)) u) ∧
        (∀u,(M n).h u=historyFieldClock
          ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)) u) :=
  G.history.literal_readout_varying_shell G.epsilon G.shell G.hb G.hh

theorem total_root (G : ActualNativeProfileHistory M T c0) :
    ∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T) ∧ (M n).h 0=0 := by
  obtain ⟨ps,Hps⟩:=G.literal_readout
  filter_upwards [Hps] with n hn
  exact (M n).actual_shell_history_total_root (ps.map (fun P=>P n)) (G.hepsilon n) hn.2.1 hn.2.2

theorem pullback (G : ActualNativeProfileHistory M T c0) :
    ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1 := by
  obtain ⟨ps,Hps⟩:=G.literal_readout
  filter_upwards [Hps] with n hn
  exact NativePullbackClockRegularity.of_shell_history
    (M n).context.hc (M n).context.hk (M n).context.hkc (M n).context.hm (M n).context.hM
    (M n).alpha T (G.epsilon n) (G.shell n) ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm))
    (M n).b (M n).h hn.2.1 hn.2.2 le_rfl zero_le_one le_rfl

theorem small_source (G : ActualNativeProfileHistory M T c0)
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop) :
    ∃Cf : ℝ,0 ≤ Cf ∧ ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) T Cf :=
  actual_weak_varying_history_small_source_clocks hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin
    dim hdim G.root M G.epsilon G.shell G.hepsilon G.hT.le G.hb G.hh G.history

theorem near_bare (G : ActualNativeProfileHistory M T c0)
    (W : ℕ→ℝ) (hxs : ∀ᶠn in atTop,(M n).xs ≤ W n)
    (hW : Tendsto W atTop (𝓝 0)) :
    ∀C eps : ℝ,0 ≤ C → 0 < eps → ∀ᶠn in atTop,∀u∈Icc (0:ℝ) (C*W n),
      |(M n).b u-T| ≤ eps*(W n)^2 ∧ |(M n).h u| ≤ eps*(W n)^3 := by
  have HW : ∀ᶠn in atTop,
      comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d ≤ W n := by
    filter_upwards [hxs] with n hn
    exact (M n).hscale.trans hn
  intro C eps hC heps
  have Hunit : ∀ᶠn in atTop,C*W n ≤ 1 := by
    have Hlim : Tendsto (fun n=>C*W n) atTop (𝓝 0) := by
      simpa only [mul_zero] using hW.const_mul C
    exact Hlim.eventually (eventually_le_nhds zero_lt_one)
  filter_upwards [G.sequential W hW HW C eps hC heps,Hunit] with n hn hunit
  simpa only [min_eq_left hunit] using hn

theorem uniform_clock_perturbation (G : ActualNativeProfileHistory M T c0) :
    ∃eta : ℕ→ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,
        |(M n).b u-(G.root n).b u| ≤ eta n ∧
        |(M n).h u-(G.root n).h u| ≤ eta n :=
  G.history.uniform_clock_perturbation

end ActualNativeProfileHistory
end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
