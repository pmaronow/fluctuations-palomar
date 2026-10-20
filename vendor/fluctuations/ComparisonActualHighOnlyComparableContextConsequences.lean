module

public import ComparisonActualHighOnlyComparableContext

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ActualHighOnlyOverlapMinimum
open scoped Topology
namespace ActualHighOnlyOverlapMinimum.HighOnlyActualComparableBandContext
variable {dim : ℕ→ℕ} {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
theorem omission_over_dominating_scale_zero (G : HighOnlyActualComparableBandContext M T)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) :
    Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0) := by
  apply squeeze_zero (fun n=>div_nonneg (M n).data.hs.1 ((M n).hxs.le.trans (hxs n))) _
    G.omission_over_test_zero
  intro n
  exact div_le_div_of_nonneg_left (M n).data.hs.1 (M n).hxs (hxs n)
end ActualHighOnlyOverlapMinimum.HighOnlyActualComparableBandContext
end OAI.SKFluctuations.LaplaceWindowFormalization
