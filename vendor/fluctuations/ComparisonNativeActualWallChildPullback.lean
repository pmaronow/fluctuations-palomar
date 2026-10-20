module

public import ComparisonActualHighWallBarePullback
public import ComparisonNativeActualRegularChildSelection
public import ComparisonNativeActualWallRawHistory

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 16000000
namespace NativeChildBarrierParameters
variable {n : ℕ} {delta : ℝ}
theorem pullback_clock_regularity_of_mass_cut_child
    (c : NativeChildBarrierParameters n delta) (alpha : c.Profile)
    (b h : ℝ→ℝ) {s : ℝ} (hs : s∈Icc (0:ℝ) 1)
    (Hbranch : ∀l r,0 ≤ l → l ≤ r → r ≤ 1 → (r < s ∨ s ≤ l) →
      ∃Kb Kh : ℝ≥0,LipschitzOnWith Kb b (Icc l r) ∧ LipschitzOnWith Kh h (Icc l r)) :
    NativePullbackClockRegularity alpha.val.val b h 0 1 := by
  let cut:=c.R alpha s
  have Hcut : cut∈Icc (0:ℝ) 1:=comparisonSweepQuantile_bounds c.hc c.hk
    c.hkc c.hm c.hM alpha s
  have Hspec : alpha.val.val cut=s:=comparisonSweepQuantile_spec c.hc c.hk
    c.hkc c.hm c.hM alpha hs
  have Halpha:=inverseIntegralConstraints_lipschitz c.hm c.hM alpha.property
  refine Or.inr ⟨cut,?_⟩
  intro l r hl hlr hr hside
  have Hl : l∈Icc (0:ℝ) 1:=⟨hl,hlr.trans hr⟩
  have Hr : r∈Icc (0:ℝ) 1:=⟨hl.trans hlr,hr⟩
  have Hside : alpha.val.val r < s ∨ s ≤ alpha.val.val l:=by
    rcases hside with Hleft|Hright
    · have H:=inverseConstraint_strictMonoOn c.hc c.hk c.hkc
        alpha.property Hr Hcut Hleft
      exact Or.inl (by simpa only [Hspec] using H)
    · exact Or.inr (by simpa only [Hspec] using alpha.val.property.2 Hright)
  obtain ⟨Kb,Kh,Hb,Hh⟩:=Hbranch (alpha.val.val l) (alpha.val.val r)
    (alpha.val.property.1 l).1 (alpha.val.property.2 hlr) (alpha.val.property.1 r).2 Hside
  have Hmap : MapsTo alpha.val.val (Icc l r) (Icc (alpha.val.val l) (alpha.val.val r)):=by
    intro x hx
    exact ⟨alpha.val.property.2 hx.1,alpha.val.property.2 hx.2⟩
  have Ha:=Halpha.mono (Icc_subset_Icc hl hr)
  exact ⟨Kb*⟨c.M 1,c.hM⟩,Kh*⟨c.M 1,c.hM⟩,
    Hb.comp Ha Hmap,Hh.comp Ha Hmap⟩
end NativeChildBarrierParameters
namespace NativeOverlapMinimum
namespace ActualNativeWallHistory
variable {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ} {dim : ℕ→ℕ}
variable {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}

theorem child_pullback (G : ActualNativeWallHistory M T c0) (hc0 : 0 < c0) :
    ∀ᶠn in atTop,∀(x : ℝ) (hx : 0 < x),
      let child:=(M n).context.toChildBarrierParameters.actualChild (M n).hlam hc0 hx
      ∀alpha : child.Profile,NativePullbackClockRegularity alpha.val.val
        (fun u=>(M n).b u-laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u))
        (fun u=>(M n).h u+laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*(M n).R u) 0 1 := by
  obtain ⟨ps,Hps⟩:=G.history.literal_readout_general_bare
  filter_upwards [Hps,G.hb,G.hh] with n hn hnb hnh
  intro x hx
  dsimp only
  intro alpha
  let child:=(M n).context.toChildBarrierParameters.actualChild (M n).hlam hc0 hx
  have Hbase:=child.pullback_clock_regularity_of_mass_cut_child alpha _ _
    ⟨(G.wall n).data.hs.1.le,(G.wall n).data.hs1⟩
    ((G.wall n).data.changed_clocks_mass_cut_branches (G.wall n).alpha)
  have Hb : (fun r=>(G.root n).b (alpha.val.val r))=
      (fun r=>((G.wall n).data.bf (G.wall n).alpha (alpha.val.val r):ℝ)) := by
    funext r
    rw [hnb,((G.wall n).data.clock_coe (G.wall n).alpha (alpha.val.property.1 r)).1]
  have Hh : (fun r=>(G.root n).h (alpha.val.val r))=
      (fun r=>((G.wall n).data.hf (G.wall n).alpha (alpha.val.val r):ℝ)) := by
    funext r
    rw [hnh,((G.wall n).data.clock_coe (G.wall n).alpha (alpha.val.property.1 r)).2]
  have Hbase' : NativePullbackClockRegularity alpha.val.val (G.root n).b (G.root n).h 0 1 := by
    unfold NativePullbackClockRegularity
    rw [Hb,Hh]
    exact Hbase
  let ts:=(M n).toHistoryTerm::((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm))
  have H:=Hbase'.perturb_by_history
    (inverseIntegralConstraints_lipschitz child.hm child.hM alpha.property) ts
  have Hbc : (fun u=>(M n).b u-laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u))=
      (fun u=>(G.root n).b u-historyMatrixReduction ts u) := by
    funext u
    simp only [ts,historyMatrixReduction,ComparisonHistoryTerm.matrixReduction,(M n).toHistoryTerm_quantile]
    rw [hn.2.1 u]
    change ((G.root n).b u-historyMatrixReduction ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)) u)-
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)=
      (G.root n).b u-(laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)+
        historyMatrixReduction ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)) u)
    ring
  have Hhc : (fun u=>(M n).h u+laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*(M n).R u)=
      (fun u=>(G.root n).h u+historyFieldAddition ts u) := by
    funext u
    simp only [ts,historyFieldAddition,ComparisonHistoryTerm.fieldAddition,(M n).toHistoryTerm_quantile]
    rw [hn.2.2 u]
    change ((G.root n).h u+historyFieldAddition ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)) u)+
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*(M n).R u=
      (G.root n).h u+(laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*(M n).R u+
        historyFieldAddition ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm)) u)
    ring
  rw [Hbc,Hhc]
  exact H

end ActualNativeWallHistory
end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
