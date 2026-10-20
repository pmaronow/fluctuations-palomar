module

public import SKProof.OriginalQHighOnlyHistory
public import ComparisonActualHighOnlyThetaZeroHistoryBadStrengthSaving

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
namespace ActualHighOnlyOverlapMinimum

theorem exists_high_only_history_bad_test_strength_saving_original_q
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
        OriginalQHighOnlyHistory M ((beta:ℝ)^2) c0 →
        (∀ n, (M n).xs ≤ 1) →
        (∀ᶠ n in atTop,
          ¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
            (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) →
        Tendsto (fun n => laplaceComparisonStrength (M n).context.d
          (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0) := by
  obtain ⟨lower, upper, hlower, hupper, H⟩ :=
    exists_theta_zero_high_only_history_bad_test_strength_saving hbeta hTemp
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro m cl cu Az C0 Ct D Bclock c0 hm hmsmall hcl hcu hAz hC0 hCt hD
    hc0 hc01 hclMacro hcuMacro hclSlack hcuSlack dim hdim M G hunit Hbad
  have hdelta : 0 < m/10000 := by positivity
  have hroom : m/10000 < 3*m := by linarith
  have hmargin : (m/10000)/4 < 3*m-99*(m/10000) := by linarith
  have hcapmargin : 100*(m/10000) < (1:ℝ)/3+m := by linarith
  have hgapmargin : 0 < 9*m-298*(m/10000) := by linarith
  obtain ⟨Hcut, HfirstCut, _⟩ := G.root_cutoff_gates hm hmsmall hC0 hc0 hdim
  exact H m (m/10000) cl cu Az C0 Ct D Bclock c0
    hm hdelta hroom hcl hcu hAz hC0 hCt hD hc0 hc01
    hmargin hcapmargin hgapmargin hclMacro hcuMacro hclSlack hcuSlack
    dim hdim G.wall G.root M G.history G.temperature G.same_mass
    G.wall_unit G.wall_target G.wall_weak Hcut HfirstCut G.bare G.field
    (G.omission_tendsto_zero hmsmall hdim)
    (G.root_endpoint_cost_tendsto_zero hmsmall hdim) hunit Hbad

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
