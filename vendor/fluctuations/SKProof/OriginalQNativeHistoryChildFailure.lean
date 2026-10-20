module

public import SKProof.OriginalQNativeBadStrengthSaving
public import SKProof.OriginalQNativeChildPressureFailure
public import SKProof.OriginalQNativeMacroEndpointJoin
public import ComparisonNativeMacroSuccessfulChildExclusion

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal

namespace NativeOverlapMinimum

theorem exists_native_child_pressure_failure_original_q
    {beta : ℝ≥0} (hbeta : 0 < beta)
    (hTemp : 1 < (beta:ℝ)^2) :
    ∃lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀m delta cl cu Az C0 Ct D Bclock c0 : ℝ,
      ∀_hm : 0 < m, ∀_hdelta : 0 < delta,
      delta < 3*m → 0 < cl → 0 < cu → 0 ≤ Az →
      0 < C0 → 0 ≤ Ct → D ≤ 1 →
      ∀hc0 : 0 < c0, c0 ≤ 1 →
      delta/4 < 3*m-99*delta →
      100*delta < (1:ℝ)/3+m →
      0 < 9*m-298*delta →
      cl ≤ lower → upper ≤ cu →
      cl < (beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
      (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
        (2*Real.exp (-12*(beta:ℝ)^2)) < cu →
      ∀dim : ℕ → ℕ, ∀_hdim : Tendsto dim atTop atTop,
      ∀M : (n : ℕ) → NativeOverlapMinimum (dim n+1)
        m delta cl cu Az C0 Ct D Bclock,
      ∀_G : OriginalQNativeRootHistory M ((beta:ℝ)^2) c0,
      (∀n, (M n).xs ≤ 1) →
      (∀ᶠn in atTop,
        comparisonConditionalScale (M n).context.N delta
          (M n).context.E (M n).lam ≤ (M n).xs) →
      (∀ᶠn in atTop,
        (M n).lam+(c0*(M n).xs)^2 ≤ (M n).b 0) →
      (∀ᶠn in atTop,
        ¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
          (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) →
      Tendsto (fun n => laplaceComparisonStrength
        (M n).context.d (M n).lam (M n).xs/(M n).xs^2)
        atTop (𝓝 0) ∧
      ∀ᶠn in atTop,
        (M n).context.N^(20*delta)*
          actualChildErrorBudget (dim n+1) delta c0
            (M n).context.d (M n).lam (M n).xs <
        (M n).actualCompensatedChildPressureCost hc0 (M n).hxs := by
  classical
  obtain ⟨lower1,upper1,hlower1,hupper1,Hsaving⟩ :=
    exists_bad_native_strength_saving_original_q hbeta hTemp
  obtain ⟨lower2,upper2,hlower2,hupper2,Hmacro⟩ :=
    macro_successful_child_literal_bad_witness_excluded hbeta hTemp
  refine ⟨min lower1 lower2,max upper1 upper2,
    lt_min hlower1 hlower2,
    hupper1.trans_le (le_max_left _ _),?_⟩
  intro m delta cl cu Az C0 Ct D Bclock c0 hm hdelta hroom
    hcl hcu hAz hC0 hCt hD hc0 hc01 hmargin hcapmargin
    hgapmargin hclMacro hcuMacro hclTemp hcuTemp
    dim hdim M G hxsunit htarget hroomChild hbad
  let T : ℝ := (beta:ℝ)^2
  have hweak := Hsaving m delta cl cu Az C0 Ct D Bclock c0
    hm hdelta hroom hcl hcu hAz hC0 hCt hD hc0 hc01
    hmargin hcapmargin hgapmargin
    (hclMacro.trans (min_le_left _ _))
    ((le_max_left _ _).trans hcuMacro)
    hclTemp hcuTemp dim hdim M G hxsunit hbad
  refine ⟨hweak,?_⟩
  by_contra hnone
  have hfreq : ∃ᶠn in atTop,
      (M n).actualCompensatedChildPressureCost hc0 (M n).hxs ≤
      (M n).context.N^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0
          (M n).context.d (M n).lam (M n).xs := by
    simpa only [Filter.Frequently,not_not,not_le] using hnone
  obtain ⟨phi,hphi,Hphi⟩ := extraction_of_frequently_atTop hfreq
  let x := fun n => (M (phi n)).xs
  by_cases hX : Tendsto x atTop (𝓝 0)
  · have hfail := eventually_bad_weak_child_pressure_fails_original_q
      hm hdelta hroom hcl hcu hAz hC0 hc0 hc01
      hmargin hcapmargin hgapmargin
      (by
        have hpos : 0 < T*Real.exp (-12*T) :=
          mul_pos G.hT (Real.exp_pos _)
        dsimp only [T] at hpos ⊢
        linarith only [hclTemp,hpos])
      hcuTemp (fun n => dim (phi n))
      (hdim.comp hphi.tendsto_atTop)
      (fun n => M (phi n)) (G.comp_original_q phi hphi)
      (fun n => (M (phi n)).xs) (fun _ => le_rfl) hX
      (hphi.tendsto_atTop.eventually htarget)
      (hweak.comp hphi.tendsto_atTop)
      (hphi.tendsto_atTop.eventually hroomChild)
      (hphi.tendsto_atTop.eventually hbad)
    obtain ⟨n,hn⟩ := hfail.exists
    exact not_lt_of_ge (Hphi n) hn
  · obtain ⟨xlo,hxlo,psi,hpsi,Hpsi⟩ :=
      exists_positive_lower_subsequence_of_nonnegative_not_tendsto_zero_comparable
        x (fun n => (M (phi n)).hxs.le) hX
    let sigma := phi ∘ psi
    have hsigma : StrictMono sigma := hphi.comp hpsi
    obtain ⟨htotal,hcost⟩ := G.macro_clock_inputs_original_q
    have hc0T : c0^2 < (beta:ℝ)^2 := by
      have h := pow_le_pow_left₀ hc0.le hc01 2
      norm_num only [one_pow] at h
      exact h.trans_lt hTemp
    have hsuccess : ∀ᶠn in atTop,
        (M (sigma n)).macroChildSweepCost hc0 ≤
          ((dim (sigma n)+1:ℕ):ℝ)^(20*delta)*
            actualChildErrorBudget (dim (sigma n)+1) delta c0
              (M (sigma n)).context.d (M (sigma n)).lam
              (M (sigma n)).xs := by
      filter_upwards [] with n
      rw [←actual_compensated_cost_eq_macro_cost_original_q]
      exact Hphi (psi n)
    have hgood := Hmacro m delta cl cu Az C0 Ct D Bclock c0
      hm hdelta hcl hcu hAz hC0 hc0 hc01 hc0T hmargin
      (hclMacro.trans (min_le_right _ _))
      ((le_max_right _ _).trans hcuMacro)
      (fun n => dim (sigma n)) (hdim.comp hsigma.tendsto_atTop)
      (fun n => M (sigma n)) xlo hxlo
      (fun n => ⟨Hpsi n,hxsunit (sigma n)⟩)
      (hsigma.tendsto_atTop.eventually htarget)
      (hweak.comp hsigma.tendsto_atTop)
      (hsigma.tendsto_atTop.eventually hroomChild)
      (hsigma.tendsto_atTop.eventually htotal)
      (hcost.comp hsigma.tendsto_atTop) hsuccess
    obtain ⟨n,hn⟩ :=
      (hgood.and (hsigma.tendsto_atTop.eventually hbad)).exists
    exact hn.2 hn.1

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
