module

public import ComparisonNativeActualWallRawHistory
public import ComparisonNativeActualWallSuccessfulChildPressure
public import ComparisonNativeActualGeneralHistoryCompleteStrictTest
public import ComparisonNativeActualWeakHistoryEndpointCost
public import ComparisonNativeMacroscopicBadExclusion

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 28000000
set_option linter.unusedVariables false
namespace NativeOverlapMinimum

theorem exists_actual_wall_history_bad_test_strength_saving
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃lower upper : ℝ,0 < lower ∧ 0 < upper ∧
      ∀m delta cl cu Az C0 Ct D Bclock c0 : ℝ,
      ∀hm : 0 < m,∀hdelta : 0 < delta,delta < 3*m →
      0 < cl → 0 < cu → 0 ≤ Az → 0 < C0 → 0 ≤ Ct → D ≤ 1 →
      ∀hc0 : 0 < c0,c0 ≤ 1 →
      delta/4 < 3*m-99*delta → 100*delta < (1:ℝ)/3+m → 0 < 9*m-298*delta →
      cl ≤ lower → upper ≤ cu →
      cl < (beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
      (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*(beta:ℝ)^2)) < cu →
      ∀dim : ℕ→ℕ,∀hdim : Tendsto dim atTop atTop,
      ∀M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀G : ActualNativeWallHistory M ((beta:ℝ)^2) c0,
      Tendsto (fun n=>(G.wall n).data.s) atTop (𝓝 0) →
      Tendsto (fun n=>(G.wall n).data.d) atTop (𝓝 0) →
      (∀n,(M n).xs ≤ 1) →
      (∀ᶠn in atTop,¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
        (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) →
      Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2)
        atTop (𝓝 0) := by
  classical
  obtain ⟨lower,upper,hlower,hupper,Hmacro⟩:=macro_literal_bad_witness_excluded_of_local_strength hbeta hTemp
  refine ⟨lower,upper,hlower,hupper,?_⟩
  intro m delta cl cu Az C0 Ct D Bclock c0 hm hdelta hroom hcl hcu hAz hC0 hCt hD
    hc0 hc01 hmargin hcapmargin hgapmargin hclMacro hcuMacro hclTemp hcuTemp
    dim hdim M G hs hdwall hxsunit Hbad
  let T:ℝ:=(beta:ℝ)^2
  have hT : 0 < T := zero_lt_one.trans hTemp
  have Hcost:=G.endpoint_cost_tendsto_zero hs hdwall
  let f:=fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2
  have hf n : 0 ≤ f n := div_nonneg (laplaceComparisonStrength_pos (M n).context.d (M n).hlam (M n).xs).le (sq_nonneg _)
  have Hsmall : ∀eta : ℝ,0 < eta → ∀ᶠn in atTop,f n < eta := by
    intro eta heta
    by_contra Hnone
    have Hfreq : ∃ᶠn in atTop,eta ≤ f n := by
      simpa only [Filter.Frequently,not_le] using Hnone
    obtain ⟨phi,hphi,Hphi⟩:=extraction_of_frequently_atTop Hfreq
    let x:=fun n=>(M (phi n)).xs
    by_cases HX : Tendsto x atTop (𝓝 0)
    · let Gs:=(G.comp phi hphi).profile HX
      obtain ⟨Gc⟩:=Gs.exists_context hm hdelta hcl hAz hC0 hc0 hc01
        hmargin hcapmargin hgapmargin (hdim.comp hphi.tendsto_atTop)
      have HD : ∀ᶠn in atTop,(M (phi n)).context.d ≤ 1 :=
        Eventually.of_forall fun n=>(M (phi n)).hdD.trans hD
      have HW:=eventually_actual_comparable_context_working_scale_le_one _ Gc HD
      have Hweak:=actual_comparable_context_bad_test_strength_tendsto_zero
        hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
        (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop) (fun n=>M (phi n)) Gc HW
        hclTemp hcuTemp (hphi.tendsto_atTop.eventually Hbad)
      have Heta:=Hweak.eventually (gt_mem_nhds heta)
      obtain ⟨n,hn⟩:=Heta.exists
      exact not_lt_of_ge (Hphi n) hn
    · obtain ⟨xlo,hxlo,psi,hpsi,Hpsi⟩:=
        exists_positive_lower_subsequence_of_nonnegative_not_tendsto_zero x
          (fun n=>(M (phi n)).hxs.le) HX
      let sigma:=phi ∘ psi
      have hsigma : StrictMono sigma:=hphi.comp hpsi
      have Hgap n : (M (sigma n)).context.d^2 ≤ T-(T-1) := by
        have H:=pow_le_pow_left₀ (M (sigma n)).context.hd.le ((M (sigma n)).hdD.trans hD) 2
        norm_num only [one_pow] at H
        linarith only [H]
      have Hgood:=Hmacro m delta cl cu Az C0 Ct D Bclock hdelta hclMacro hcuMacro
        (fun n=>dim (sigma n)+1) ((tendsto_add_atTop_nat 1).comp (hdim.comp hsigma.tendsto_atTop))
        (fun n=>M (sigma n)) eta xlo (T-1) heta hxlo (by dsimp only [T];linarith)
        (fun n=>⟨Hpsi n,hxsunit (sigma n)⟩) (fun n=>Hphi (psi n)) Hgap
        (Hcost.comp hsigma.tendsto_atTop)
      obtain ⟨n,hn⟩:=(Hgood.and (hsigma.tendsto_atTop.eventually Hbad)).exists
      exact hn.2 hn.1
  change Tendsto f atTop (𝓝 0)
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  filter_upwards [Hsmall eps heps] with n hn
  simpa only [Real.dist_eq,sub_zero,abs_of_nonneg (hf n)] using hn

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
