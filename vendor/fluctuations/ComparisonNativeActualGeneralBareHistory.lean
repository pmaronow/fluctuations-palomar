module

public import ComparisonNativeActualWeakHistoryVaryingReadout
public import ComparisonNativeActualHistoryCutoffSourceClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option maxHeartbeats 12000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {dim : ℕ→ℕ}

theorem ActualWeakSelectedHistoryChain.literal_readout_general_bare
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakSelectedHistoryChain c0 root M) :
    ∃ps : List ((n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock),
      ∀ᶠn in atTop,
        ActualHistoryCutoffChain c0 (ps.map (fun P=>P n)) (M n) ∧
        (∀u,(M n).b u=(root n).b u-
          historyMatrixReduction ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)) u) ∧
        (∀u,(M n).h u=(root n).h u+
          historyFieldAddition ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)) u) := by
  induction H with
  | root => exact ⟨[],Eventually.of_forall (fun n=>⟨True.intro,by simp [historyMatrixReduction],
      by simp [historyFieldAddition]⟩)⟩
  | @child P M history x hx hxunit htarget hcap hweak hd hE hbc hhc ih =>
    obtain ⟨ps,Hps⟩:=ih
    refine ⟨P::ps,?_⟩
    have Hweak:=hweak.eventually (gt_mem_nhds zero_lt_one)
    filter_upwards [Hps,htarget,hcap,Hweak,hd,hE,hbc,hhc] with n hn hnt hncap hnweak hnd hnE hnb hnh
    refine ⟨?_,?_,?_⟩
    · exact actual_history_cutoff_chain_cons (P n) (M n) (ps.map (fun Q=>Q n)) (x n) (hx n)
        hnt (by simpa only [one_mul] using (div_le_iff₀ (sq_pos_of_pos (hx n))).mp hnweak.le)
        hncap hnd hnE hnb hnh hn.1
    · intro u
      simp only [List.map_cons,historyMatrixReduction]
      change (M n).b u=(root n).b u-
        (laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)+
          historyMatrixReduction ((ps.map (fun Q=>Q n)).map (fun Q=>Q.toHistoryTerm)) u)
      rw [hnb u,hn.2.1 u]
      ring
    · intro u
      simp only [List.map_cons,historyFieldAddition]
      change (M n).h u=(root n).h u+
        (laplaceComparisonStrength (P n).context.d (P n).lam ((P n).R u)*(P n).R u+
          historyFieldAddition ((ps.map (fun Q=>Q n)).map (fun Q=>Q.toHistoryTerm)) u)
      rw [hnh u,hn.2.2 u]
      ring

theorem ActualWeakSelectedHistoryChain.cutoff_inherits_root
    (hm : 0 < m) (hdelta : 0 < delta) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakSelectedHistoryChain c0 root M) :
    ∀ᶠn in atTop,
      comparisonLowerScale (root n).context.N (root n).context.E (root n).context.d ≤
        comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d := by
  induction H with
  | root => exact Eventually.of_forall (fun _=>le_rfl)
  | @child P Q history x hx hxunit htarget hcap hweak hd hE hb hh ih =>
    have Hweak:=hweak.eventually (gt_mem_nhds zero_lt_one)
    filter_upwards [ih,hdim.eventually (eventually_actual_parent_cap_and_cutoff_inherit
      (cl:=cl) (cu:=cu) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hdelta hAz hC0 hc0 hmargin hcapmargin),
      Hweak,htarget,hcap,hd,hE] with n hn hncut hnweak hnt hncap hnd hnE
    exact hn.trans ((hncut (P n) (Q n) (x n) (hx n) hnt
      (by simpa only [one_mul] using (div_le_iff₀ (sq_pos_of_pos (hx n))).mp hnweak.le)
      hncap hnd hnE).2)

theorem ActualWeakSelectedHistoryChain.total_root_general_bare
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakSelectedHistoryChain c0 root M)
    (Hroot : ∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(root n).h u+(root n).b u ≤ T) ∧
      (root n).h 0=0) :
    ∀ᶠn in atTop,(∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T) ∧ (M n).h 0=0 := by
  obtain ⟨ps,Hps⟩:=H.literal_readout_general_bare
  filter_upwards [Hroot,Hps] with n hn hnps
  constructor
  · intro u hu
    rw [hnps.2.1,hnps.2.2]
    have hlam : ∀t∈(ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm),0 ≤ t.lam := by
      intro t ht
      obtain ⟨P,hP,rfl⟩:=List.mem_map.mp ht
      exact P.hlam.le
    have Hfield:=actual_history_field_le_reduction _ hlam u
    linarith [hn.1 u hu]
  · rw [hnps.2.2,hn.2,zero_add]
    exact actual_history_field_zero _

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
