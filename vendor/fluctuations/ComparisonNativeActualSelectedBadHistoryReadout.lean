module

public import ComparisonNativeActualSelectedBadHistoryClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {N : ℕ→ℕ}

theorem ActualSelectedBadHistoryChain.literal_readout
    {root M : (n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock}
    (epsilon shell : ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M) :
    ∃ps : List ((n:ℕ)→NativeOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock),
      ∀ᶠn in atTop,
        ActualHistoryCutoffChain c0 (ps.map (fun P=>P n)) (M n) ∧
        (∀u,(M n).b u=historyMatrixClock T epsilon shell
          ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)) u) ∧
        (∀u,(M n).h u=historyFieldClock
          ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)) u) := by
  induction Hhistory with
  | root=>
    refine ⟨[],?_⟩
    filter_upwards [hb,hh] with n hn hn'
    exact ⟨True.intro,by simpa only [List.map_nil,historyMatrixClock,historyMatrixReduction,sub_zero] using hn,
      by simpa only [List.map_nil,historyFieldClock,historyFieldAddition] using hn'⟩
  | @child P M history x hx hxlim htarget hcap hweak hd hE hbc hhc ih=>
    obtain ⟨ps,hps⟩:=ih
    refine ⟨P::ps,?_⟩
    have Hweak:=hweak.eventually (gt_mem_nhds zero_lt_one)
    filter_upwards [hps,htarget,hcap,Hweak,hd,hE,hbc,hhc] with n hn hntarget hncap hnweak hnd hnE hnb hnh
    refine ⟨?_,?_,?_⟩
    · exact actual_history_cutoff_chain_cons (P n) (M n) (ps.map (fun Q=>Q n)) (x n) (hx n)
        hntarget (by simpa only [one_mul] using (div_le_iff₀ (sq_pos_of_pos (hx n))).mp hnweak.le)
        hncap hnd hnE hnb hnh hn.1
    · intro u
      simp only [List.map_cons,historyMatrixClock,historyMatrixReduction]
      change (M n).b u=initialShellMatrixClock T epsilon shell u-
        (laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)+
          historyMatrixReduction ((ps.map (fun Q=>Q n)).map (fun Q=>Q.toHistoryTerm)) u)
      rw [hnb u,hn.2.1 u]
      unfold historyMatrixClock
      ring
    · intro u
      simp only [List.map_cons,historyFieldClock,historyFieldAddition]
      change (M n).h u=laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)*(P n).R u+
        historyFieldAddition ((ps.map (fun Q=>Q n)).map (fun Q=>Q.toHistoryTerm)) u
      rw [hnh u,hn.2.2 u]
      unfold historyFieldClock
      ring

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
