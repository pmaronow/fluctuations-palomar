module

public import SKProof.OriginalQNativeRootHistory
public import ComparisonNativeActualWallChildPullback

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal

namespace NativeOverlapMinimum

theorem OriginalQNativeRootHistory.child_pullback_original_q
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ} {dim : ℕ → ℕ}
    {M : (n : ℕ) → NativeOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock}
    (G : OriginalQNativeRootHistory M T c0) (hc0 : 0 < c0) :
    ∀ᶠn in atTop, ∀(x : ℝ) (hx : 0 < x),
      let child := (M n).context.toChildBarrierParameters.actualChild
        (M n).hlam hc0 hx
      ∀alpha : child.Profile,
        NativePullbackClockRegularity alpha.val.val
          (fun u => (M n).b u-
            laplaceComparisonStrength (M n).context.d
              (M n).lam ((M n).R u))
          (fun u => (M n).h u+
            laplaceComparisonStrength (M n).context.d
              (M n).lam ((M n).R u)*(M n).R u) 0 1 := by
  obtain ⟨ps,Hps⟩ := G.history.literal_readout_general_bare
  filter_upwards [Hps,G.hb,G.hh] with n hn hnb hnh
  intro x hx
  dsimp only
  intro alpha
  let child := (M n).context.toChildBarrierParameters.actualChild
    (M n).hlam hc0 hx
  have hbase := child.pullback_clock_regularity_of_mass_cut_child
    alpha (G.wall n).changedBare (G.wall n).changedField
    ⟨(G.wall n).data.hs.1.le,(G.wall n).data.hs1⟩
    (G.wall n).changed_clocks_mass_cut_branches
  have hbroot : (G.root n).b = (G.wall n).changedBare := funext hnb
  have hhroot : (G.root n).h = (G.wall n).changedField := funext hnh
  have hbase' : NativePullbackClockRegularity alpha.val.val
      (G.root n).b (G.root n).h 0 1 := by
    rw [hbroot,hhroot]
    exact hbase
  let ts := (M n).toHistoryTerm::
    ((ps.map (fun P => P n)).map (fun P => P.toHistoryTerm))
  have hphysical := hbase'.perturb_by_history
    (inverseIntegralConstraints_lipschitz child.hm child.hM
      alpha.property) ts
  have hbc :
      (fun u => (M n).b u-
        laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)) =
      (fun u => (G.root n).b u-historyMatrixReduction ts u) := by
    funext u
    simp only [ts,historyMatrixReduction,ComparisonHistoryTerm.matrixReduction,
      (M n).toHistoryTerm_quantile]
    rw [hn.2.1 u]
    change ((G.root n).b u-
      historyMatrixReduction ((ps.map (fun P => P n)).map
        (fun P => P.toHistoryTerm)) u)-
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u) =
      (G.root n).b u-
        (laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)+
          historyMatrixReduction ((ps.map (fun P => P n)).map
            (fun P => P.toHistoryTerm)) u)
    ring
  have hhc :
      (fun u => (M n).h u+
        laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*
          (M n).R u) =
      (fun u => (G.root n).h u+historyFieldAddition ts u) := by
    funext u
    simp only [ts,historyFieldAddition,ComparisonHistoryTerm.fieldAddition,
      (M n).toHistoryTerm_quantile]
    rw [hn.2.2 u]
    change ((G.root n).h u+
      historyFieldAddition ((ps.map (fun P => P n)).map
        (fun P => P.toHistoryTerm)) u)+
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*
        (M n).R u =
      (G.root n).h u+
        (laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*
          (M n).R u+
          historyFieldAddition ((ps.map (fun P => P n)).map
            (fun P => P.toHistoryTerm)) u)
    ring
  rw [hbc,hhc]
  exact hphysical

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
