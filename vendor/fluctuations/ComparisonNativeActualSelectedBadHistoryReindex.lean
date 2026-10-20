module

public import ComparisonNativeActualHistoryScalarEndpointLimits
public import ComparisonNativeActualSelectedBadHistorySourceClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option maxHeartbeats 10000000
namespace NativeOverlapMinimum

theorem ActualSelectedBadHistoryChain.comp
    {m delta cl cu Az C0 Ct D Bclock c0 : ℝ} {dim : ℕ→ℕ}
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (phi : ℕ→ℕ) (hphi : Tendsto phi atTop atTop) :
    ActualSelectedBadHistoryChain c0 (fun n=>root (phi n)) (fun n=>M (phi n)) := by
  induction Hhistory with
  | root => exact .root
  | @child P M history x hx hxlim htarget hcap hweak hd hE hb hh ih =>
    exact .child ih (fun n=>x (phi n)) (fun n=>hx (phi n)) (hxlim.comp hphi)
      (hphi.eventually htarget) (hphi.eventually hcap) (hweak.comp hphi)
      (hphi.eventually hd) (hphi.eventually hE) (hphi.eventually hb) (hphi.eventually hh)

theorem actual_selected_bad_history_all_index_clock_tail
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hT : 0 ≤ T)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M) :
    ∃n0 : ℕ,∃Cf : ℝ,0 ≤ Cf ∧
      ActualSelectedBadHistoryChain c0 (fun n=>root (n+n0)) (fun n=>M (n+n0)) ∧
      Tendsto (fun n=>dim (n+n0)) atTop atTop ∧
      (∀n,(∀u,(root (n+n0)).b u=initialShellMatrixClock T epsilon shell u) ∧
        (∀u,(root (n+n0)).h u=0) ∧
        (∀u∈Icc (0:ℝ) 1,(M (n+n0)).h u+(M (n+n0)).b u ≤ T) ∧
        (M (n+n0)).h 0=0 ∧ NativeActualSmallSourceClocks (M (n+n0)) T Cf) ∧
      ∃ps : List ((n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock),
        ∀n,ActualHistoryCutoffChain c0 (ps.map (fun P=>P (n+n0))) (M (n+n0)) ∧
          (∀u,(M (n+n0)).b u=historyMatrixClock T epsilon shell
            ((ps.map (fun P=>P (n+n0))).map (fun P=>P.toHistoryTerm)) u) ∧
          (∀u,(M (n+n0)).h u=historyFieldClock
            ((ps.map (fun P=>P (n+n0))).map (fun P=>P.toHistoryTerm)) u) := by
  obtain ⟨Cf,hCf,Hsource⟩ := actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hT hb hh Hhistory
  have Htotal := actual_selected_bad_history_total_clock_and_root
    dim root M epsilon shell hepsilon hb hh Hhistory
  obtain ⟨ps,Hps⟩ := Hhistory.literal_readout epsilon shell hb hh
  have Hall : ∀ᶠn in atTop,
      (∀u,(root n).b u=initialShellMatrixClock T epsilon shell u) ∧
      (∀u,(root n).h u=0) ∧
      (∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T) ∧
      (M n).h 0=0 ∧ NativeActualSmallSourceClocks (M n) T Cf ∧
      ActualHistoryCutoffChain c0 (ps.map (fun P=>P n)) (M n) ∧
      (∀u,(M n).b u=historyMatrixClock T epsilon shell
        ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)) u) ∧
      (∀u,(M n).h u=historyFieldClock
        ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)) u) := by
    filter_upwards [hb,hh,Htotal,Hsource,Hps] with n hnB hnH hnTotal hnSource hnPs
    exact ⟨hnB,hnH,hnTotal.1,hnTotal.2,hnSource,hnPs⟩
  obtain ⟨n0,Hn0⟩ := eventually_atTop.mp Hall
  refine ⟨n0,Cf,hCf,Hhistory.comp (fun n=>n+n0) (tendsto_add_atTop_nat n0),
    hdim.comp (tendsto_add_atTop_nat n0),?_,ps,?_⟩
  · intro n
    obtain ⟨hnB,hnH,hnTotal,hnRoot,hnSource,_⟩ := Hn0 (n+n0) (Nat.le_add_left n0 n)
    exact ⟨hnB,hnH,hnTotal,hnRoot,hnSource⟩
  · intro n
    exact (Hn0 (n+n0) (Nat.le_add_left n0 n)).2.2.2.2.2

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
