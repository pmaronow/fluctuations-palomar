module

public import ComparisonNativeActualHistoryCutoffLedger

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 9000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}

theorem actual_shell_history_total_root {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ps : List (NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock))
    {T epsilon shell : ℝ} (hepsilon : 0≤epsilon)
    (hb : ∀u,M.b u=historyMatrixClock T epsilon shell (ps.map (fun P=>P.toHistoryTerm)) u)
    (hh : ∀u,M.h u=historyFieldClock (ps.map (fun P=>P.toHistoryTerm)) u) :
    (∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤T) ∧ M.h 0=0 := by
  constructor
  · intro u _
    rw [hb,hh]
    change historyFieldAddition (ps.map (fun P=>P.toHistoryTerm)) u+
      (initialShellMatrixClock T epsilon shell u-historyMatrixReduction (ps.map (fun P=>P.toHistoryTerm)) u)≤T
    have hlam : ∀t∈ps.map (fun P=>P.toHistoryTerm),0≤t.lam := by
      intro t ht
      obtain ⟨P,hP,rfl⟩:=List.mem_map.mp ht
      exact P.hlam.le
    have H:=actual_history_field_le_reduction (ps.map (fun P=>P.toHistoryTerm)) hlam u
    have Hshell : initialShellMatrixClock T epsilon shell u≤T := by
      unfold initialShellMatrixClock
      split_ifs <;> linarith
    linarith
  · rw [hh]
    exact actual_history_field_zero _

theorem eventually_actual_shell_history_cutoff_source_clock_bounds
    (hm : 0 < m) (hdelta : 0<delta) (hcl : 0<cl) (hAz : 0≤Az)
    (hC0 : 0<C0) (hc0 : 0<c0)
    (hmargin : delta/4<3*m-99*delta) (hcapmargin : 100*delta<(1:ℝ)/3+m)
    (depth : ℕ) {T : ℝ} (hT : 0≤T) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (ps : List (NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)),
      ActualHistoryCutoffChain c0 ps M → ps.length≤depth →
      ∀epsilon shell : ℝ,0≤epsilon →
      (∀u,M.b u=historyMatrixClock T epsilon shell (ps.map (fun P=>P.toHistoryTerm)) u) →
      (∀u,M.h u=historyFieldClock (ps.map (fun P=>P.toHistoryTerm)) u) →
      ∀u∈Icc (0:ℝ) 1,
      0≤(M.bf u:ℝ) ∧ (M.bf u:ℝ)≤T ∧ 0≤(M.hf u:ℝ) ∧
      (M.hf u:ℝ)≤((Az*max 1 (D^2/c0))*(depth:ℝ)+T/cl+
        bareSourceClockConstant cl Az D)*(M.xs+u) := by
  filter_upwards [eventually_actual_history_regular_caps_le_working_scale (cl:=cl) (cu:=cu)
    (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hdelta hAz hC0 hc0 hmargin hcapmargin depth] with n hn
  intro M ps hchain hdepth epsilon shell hepsilon hb hh u hu
  have Hcap:=hn ps M hchain hdepth
  have Hfield:=M.actual_shell_history_compensated_field_le_regular_caps ps hcl hAz hT hepsilon hb hh hu
  have Htotal:=(M.actual_shell_history_total_root ps hepsilon hb hh).1
  have Htotal':=M.inherited_total_clock_le Htotal u hu
  refine ⟨NNReal.coe_nonneg _,?_,NNReal.coe_nonneg _,?_⟩
  · linarith [(M.hf u).coe_nonneg]
  · have Hextra:=mul_nonneg
      (show 0≤(Az*max 1 (D^2/c0))*(depth:ℝ) by positivity) hu.1
    nlinarith only [Hcap,Hfield,Hextra]

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
