module

public import ComparisonNativeActualInheritedHistoryGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 5000000
namespace NativeOverlapMinimum

theorem inherited_shell_history_child_endpoint {n : ℕ}
    {margin delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (ts : List ComparisonHistoryTerm) (T epsilon shell : ℝ)
    (hb : ∀u,M.b u=historyMatrixClock T epsilon shell ts u)
    (hh : ∀u,M.h u=historyFieldClock ts u) (u : ℝ) :
    M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)=
        historyMatrixClock T epsilon shell (M.toHistoryTerm::ts) u ∧
      M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u=
        historyFieldClock (M.toHistoryTerm::ts) u := by
  rw [hb,hh]
  simp only [historyMatrixClock,historyFieldClock,historyMatrixReduction,historyFieldAddition,
    ComparisonHistoryTerm.matrixReduction,ComparisonHistoryTerm.fieldAddition,M.toHistoryTerm_quantile]
  change (initialShellMatrixClock T epsilon shell u-historyMatrixReduction ts u)-
      laplaceComparisonStrength M.context.d M.lam (M.R u)=
        initialShellMatrixClock T epsilon shell u-(laplaceComparisonStrength M.context.d M.lam (M.R u)+
          historyMatrixReduction ts u) ∧
      historyFieldAddition ts u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u=
        laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u+historyFieldAddition ts u
  constructor <;> ring

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
