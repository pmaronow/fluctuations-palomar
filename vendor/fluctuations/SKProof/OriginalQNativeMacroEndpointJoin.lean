module

public import SKProof.OriginalQNativeRootHistory
public import ComparisonNativeMacroSuccessfulChildFactory
public import ComparisonNativeActualGeneralSuccessfulChildPressure

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal

namespace NativeOverlapMinimum

theorem OriginalQNativeRootHistory.macro_clock_inputs_original_q
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ} {dim : ℕ → ℕ}
    {M : (n : ℕ) → NativeOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock}
    (G : OriginalQNativeRootHistory M T c0) :
    (∀ᶠn in atTop, ∀u∈Icc (0:ℝ) 1,
      (M n).h u+(M n).b u ≤ T) ∧
    Tendsto (fun n => comparisonEndpointL1Cost T
      (M n).b (M n).h) atTop (𝓝 0) :=
  ⟨G.total_root_original_q.mono (fun _ h => h.1), G.endpoint_cost_tendsto_zero_original_q⟩

theorem actual_compensated_cost_eq_macro_cost_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock c0 : ℝ}
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hc0 : 0 < c0) :
    M.actualCompensatedChildPressureCost hc0 M.hxs =
      M.macroChildSweepCost hc0 := by
  rfl

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
