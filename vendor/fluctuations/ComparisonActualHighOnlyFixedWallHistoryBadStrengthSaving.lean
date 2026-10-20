module

public import ComparisonActualHighOnlyFixedWallHistory
public import ComparisonActualHighOnlyThetaZeroHistoryBranchCalls
public import ComparisonActualHighOnlyCompleteComparableStrictTest
public import ComparisonSequenceShrinkingMacroTendstoZero

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 28000000
namespace ActualHighOnlyOverlapMinimum

theorem exists_fixed_wall_high_only_history_bad_test_strength_saving
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ m cl cu Az C0 Ct D Bclock c0 : ℝ,
        0 < m → m ≤ (1:ℝ)/120 → 0 < cl → 0 < cu → 0 ≤ Az →
        0 < C0 → 0 ≤ Ct → D ≤ 1 → 0 < c0 → c0 ≤ 1 →
        cl ≤ lower → upper ≤ cu →
        cl < (beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
        (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
          (2*Real.exp (-12*(beta:ℝ)^2)) < cu →
        ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
        ∀ M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
          m (m/10000) cl cu Az C0 Ct D Bclock,
        ActualFixedWallHighOnlyHistory M ((beta:ℝ)^2) c0 →
        (∀ n, (M n).xs ≤ 1) →
        (∀ᶠ n in atTop,
          ¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
            (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) →
        Tendsto (fun n => laplaceComparisonStrength (M n).context.d
          (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0) := by
  classical
  obtain ⟨lower, upper, hlower, hupper, Hmacro⟩ :=
    exists_theta_zero_macro_bad_strength_reindex hbeta hTemp
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro m cl cu Az C0 Ct D Bclock c0 hm hmsmall hcl hcu hAz hC0 hCt hD
    hc0 hc01 hclMacro hcuMacro hclSlack hcuSlack dim hdim M G hunit Hbad
  have hdelta : 0 < m/10000 := by positivity
  let f := fun n => laplaceComparisonStrength (M n).context.d
    (M n).lam (M n).xs/(M n).xs^2
  have hf (n : ℕ) : 0 ≤ f n := div_nonneg
    (laplaceComparisonStrength_pos (M n).context.d (M n).hlam (M n).xs).le
    (sq_nonneg _)
  change Tendsto f atTop (𝓝 0)
  apply comparison_tendsto_zero_of_shrinking_or_macro_subsequences
    (fun n => (M n).xs) f (fun n => (M n).hxs.le) hf
  · intro phi hphi HX
    obtain ⟨Gc⟩ := (G.comp phi hphi).exists_context
      hm hmsmall hcl hAz hC0 hc0 hc01 (hdim.comp hphi.tendsto_atTop) HX
    have HD : ∀ᶠ n in atTop, (M (phi n)).context.d ≤ 1 :=
      Eventually.of_forall (fun n => (M (phi n)).hdD.trans hD)
    have HW := eventually_actual_comparable_context_working_scale_le_one_high_only
      (fun n => M (phi n)) Gc HD
    exact actual_high_only_comparable_bad_test_strength_tendsto_zero
      hm hdelta (by linarith) hcl hcu hAz hC0 hCt hc0 hc01
      (by linarith) (by linarith) (by linarith)
      (fun n => dim (phi n)) (hdim.comp hphi.tendsto_atTop)
      (fun n => M (phi n)) Gc HW hclSlack hcuSlack
      (hphi.tendsto_atTop.eventually Hbad)
  · intro sigma hsigma xlo hxlo Hlo
    exact Hmacro m (m/10000) cl cu Az C0 Ct D Bclock
      hdelta hclMacro hcuMacro hD dim hdim M hunit
      (G.omission_tendsto_zero hmsmall hdim)
      (G.endpoint_cost_tendsto_zero hmsmall hdim) Hbad sigma hsigma xlo hxlo Hlo

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
