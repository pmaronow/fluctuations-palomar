module

public import ComparisonActualHighOnlyFixedWallSuccessfulChildCostFailure
public import ComparisonActualHighOnlyMacroChildCostFailure

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 26000000
namespace ActualHighOnlyOverlapMinimum

theorem exists_fixed_wall_bad_parent_sharp_child_cost_failure_constants
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ m cl cu Az C0 Ct D Bclock c0 : ℝ,
        0 < m → m ≤ (1:ℝ)/120 → 0 < cl → 0 < cu → 0 ≤ Az → 0 < C0 →
        ∀ hc0 : 0 < c0, c0 ≤ 1 → cl ≤ lower → upper ≤ cu →
        cl < 2*(beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
        (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
          (2*Real.exp (-12*(beta:ℝ)^2)) < cu →
        ∀ dim : ℕ → ℕ, Tendsto dim atTop atTop →
        ∀ M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
          m (m/10000) cl cu Az C0 Ct D Bclock,
        ActualFixedWallHighOnlyHistory M ((beta:ℝ)^2) c0 →
        (∀ n, (M n).xs ≤ 1) →
        (∀ᶠ n in atTop, comparisonConditionalScale (M n).context.N (m/10000)
          (M n).context.E (M n).lam ≤ (M n).xs) →
        Tendsto (fun n => laplaceComparisonStrength (M n).context.d
          (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0) →
        (∀ᶠ n in atTop, (M n).lam+(c0*(M n).xs)^2 ≤ (M n).b (M n).data.s) →
        (∀ᶠ n in atTop, ∀ u ∈ Ico (0:ℝ) (M n).data.s,
          (M n).b u+(M n).lam+(c0*(M n).xs)^2 ≤ (M n).b (M n).data.s) →
        (∀ᶠ n in atTop, ¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
          (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) →
        ∀ᶠ n in atTop, ((dim n+1:ℕ):ℝ)^(20*(m/10000))*actualChildErrorBudget
          (dim n+1) (m/10000) c0 (M n).context.d (M n).lam (M n).xs <
            (M n).macroChildSweepCost hc0 := by
  classical
  obtain ⟨lower, upper, hlower, hupper, Hmacro⟩ :=
    exists_macro_bad_parent_child_cost_failure_constants hbeta hTemp
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro m cl cu Az C0 Ct D Bclock c0 hm hmsmall hcl hcu hAz hC0 hc0 hc01
    hclMacro hcuMacro hclSlack hcuSlack dim hdim M G hunit htarget hweak
    hroomChild hcross Hbad
  have hdelta : 0 < m/10000 := by positivity
  by_contra Hnone
  have Hfreq : ∃ᶠ n in atTop, (M n).macroChildSweepCost hc0 ≤
      ((dim n+1:ℕ):ℝ)^(20*(m/10000))*actualChildErrorBudget
        (dim n+1) (m/10000) c0 (M n).context.d (M n).lam (M n).xs := by
    simpa only [Filter.Frequently, not_le] using Hnone
  obtain ⟨phi, hphi, Hphi⟩ := extraction_of_frequently_atTop Hfreq
  let x := fun n => (M (phi n)).xs
  by_cases HX : Tendsto x atTop (𝓝 0)
  · have Hfailure := eventually_fixed_wall_shrinking_bad_parent_macro_child_cost_failure
      hm hmsmall hcl hcu hAz hC0 hc0 hc01 hclSlack hcuSlack
      (fun n => dim (phi n)) (hdim.comp hphi.tendsto_atTop)
      (fun n => M (phi n)) (G.comp phi hphi) HX
      (hphi.tendsto_atTop.eventually htarget) (hweak.comp hphi.tendsto_atTop)
      (hphi.tendsto_atTop.eventually hroomChild) (hphi.tendsto_atTop.eventually hcross)
      (hphi.tendsto_atTop.eventually Hbad)
    obtain ⟨n, hn⟩ := Hfailure.exists
    exact (not_lt_of_ge (Hphi n)) hn
  · obtain ⟨xlo, hxlo, psi, hpsi, Hpsi⟩ :=
      exists_positive_lower_subsequence_of_nonnegative_not_tendsto_zero
        x (fun n => (M (phi n)).hxs.le) HX
    let sigma := phi ∘ psi
    have hsigma : StrictMono sigma := hphi.comp hpsi
    have hc0Temp : c0^2 < (beta:ℝ)^2 := by
      have H := pow_le_pow_left₀ hc0.le hc01 2
      norm_num only [one_pow] at H
      exact H.trans_lt hTemp
    have Hfailure := Hmacro m (m/10000) cl cu Az C0 Ct D Bclock c0
      hm hdelta hC0 hc0 hc0Temp hclMacro hcuMacro
      (fun n => dim (sigma n)) (hdim.comp hsigma.tendsto_atTop)
      (fun n => M (sigma n)) xlo hxlo
      (fun n => ⟨Hpsi n, hunit (sigma n)⟩)
      ((G.omission_tendsto_zero hmsmall hdim).comp hsigma.tendsto_atTop)
      (hweak.comp hsigma.tendsto_atTop)
      (hsigma.tendsto_atTop.eventually hroomChild)
      (hsigma.tendsto_atTop.eventually hcross)
      ((G.endpoint_cost_tendsto_zero hmsmall hdim).comp hsigma.tendsto_atTop)
      (hsigma.tendsto_atTop.eventually Hbad)
    obtain ⟨n, hn⟩ := Hfailure.exists
    exact (not_lt_of_ge (Hphi (psi n))) hn

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
