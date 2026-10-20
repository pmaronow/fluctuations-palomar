module

public import ComparisonNativeActualGeneralProfileHistoryAssembly
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

theorem actual_weak_lower_shell_endpoint_cost_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {dim : ℕ→ℕ}
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (shell : ℕ→ℝ) (hshell : ∀n,shell n∈Icc (0:ℝ) 1)
    (hshelllim : Tendsto shell atTop (𝓝 0))
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=
      initialShellMatrixClock T (((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3)) (shell n) u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualWeakSelectedHistoryChain c0 root M) :
    Tendsto (fun n=>comparisonEndpointL1Cost T (M n).b (M n).h) atTop (𝓝 0) := by
  apply actual_weak_shrinking_shell_history_endpoint_cost_tendsto_zero (E:=1) Hhistory
    (fun n=>((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3)) shell _ hshell hshelllim hb hh
  intro n
  have hN : (1:ℝ) ≤ ((dim n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  exact ⟨Real.rpow_nonneg (by positivity) _,Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num)⟩

theorem exists_actual_weak_lower_shell_bad_test_strength_saving
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
      ∀root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀shell : ℕ→ℝ,(∀n,shell n∈Icc (0:ℝ) 1) → Tendsto shell atTop (𝓝 0) →
      (∀ᶠn in atTop,∀u,(root n).b u=
        initialShellMatrixClock ((beta:ℝ)^2) (((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3)) (shell n) u) →
      (∀ᶠn in atTop,∀u,(root n).h u=0) →
      ActualWeakSelectedHistoryChain c0 root M →
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
    dim hdim root M shell hshell hshelllim hb hh Hhistory hxsunit Hbad
  let T:ℝ:=(beta:ℝ)^2
  have hT : 0 < T := zero_lt_one.trans hTemp
  have Hcost:=actual_weak_lower_shell_endpoint_cost_tendsto_zero shell hshell hshelllim hb hh Hhistory
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
    · let G:=actual_lower_shell_profile_history hm hdelta hcl hAz hC0 hc0 hc01 hT
        hmargin hcapmargin hgapmargin (hdim.comp hphi.tendsto_atTop)
        (fun n=>root (phi n)) (fun n=>M (phi n)) (fun n=>shell (phi n))
        (hphi.tendsto_atTop.eventually hb) (hphi.tendsto_atTop.eventually hh)
        (Hhistory.comp phi hphi.tendsto_atTop) HX
      have HD : ∀ᶠn in atTop,(M (phi n)).context.d ≤ 1 :=
        Eventually.of_forall fun n=>(M (phi n)).hdD.trans hD
      have HW:=eventually_actual_weak_history_working_scale_le_one _ G HD
      have Hweak:=actual_weak_history_bad_test_strength_tendsto_zero
        hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
        (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop) (fun n=>M (phi n)) G HW
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
