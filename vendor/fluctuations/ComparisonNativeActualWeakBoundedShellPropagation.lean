module

public import ComparisonNativeActualWeakBoundedShellClockData
public import ComparisonNativeActualWeakLowerShellFinitePropagation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 28000000
set_option linter.unusedVariables false
namespace NativeOverlapMinimum

theorem actual_weak_bounded_shell_endpoint_cost_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ} {dim : ℕ→ℕ}
    {root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (epsilon shell : ℕ→ℝ)
    (hepsilon : ∀n,epsilon n∈Icc (0:ℝ) (((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3)))
    (hshell : ∀n,shell n∈Icc (0:ℝ) 1)
    (hshelllim : Tendsto shell atTop (𝓝 0))
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=
      initialShellMatrixClock T (epsilon n) (shell n) u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualWeakSelectedHistoryChain c0 root M) :
    Tendsto (fun n=>comparisonEndpointL1Cost T (M n).b (M n).h) atTop (𝓝 0) := by
  apply actual_weak_shrinking_shell_history_endpoint_cost_tendsto_zero (E:=1) Hhistory
    epsilon shell _ hshell hshelllim hb hh
  intro n
  have hN : (1:ℝ) ≤ ((dim n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  exact ⟨(hepsilon n).1,(hepsilon n).2.trans (Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num))⟩

theorem exists_actual_weak_bounded_shell_bad_test_strength_saving
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
      ∀epsilon shell : ℕ→ℝ,(∀n,epsilon n∈Icc (0:ℝ) (((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3))) →
      (∀n,shell n∈Icc (0:ℝ) 1) → Tendsto shell atTop (𝓝 0) →
      (∀ᶠn in atTop,∀u,(root n).b u=
        initialShellMatrixClock ((beta:ℝ)^2) (epsilon n) (shell n) u) →
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
    dim hdim root M epsilon shell hepsilon hshell hshelllim hb hh Hhistory hxsunit Hbad
  let T:ℝ:=(beta:ℝ)^2
  have hT : 0 < T := zero_lt_one.trans hTemp
  have Hcost:=actual_weak_bounded_shell_endpoint_cost_tendsto_zero epsilon shell hepsilon hshell hshelllim hb hh Hhistory
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
    · let G:=actual_bounded_shell_profile_history hm hdelta hcl hAz hC0 hc0 hc01 hT
        hmargin hcapmargin hgapmargin (hdim.comp hphi.tendsto_atTop)
        (fun n=>root (phi n)) (fun n=>M (phi n)) (fun n=>epsilon (phi n)) (fun n=>shell (phi n))
        (fun n=>hepsilon (phi n))
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

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 28000000
set_option linter.unusedVariables false
namespace NativeOverlapMinimum
theorem exists_actual_weak_bounded_shell_bad_test_child_pressure_failure
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
      ∀epsilon shell : ℕ→ℝ,(∀n,epsilon n∈Icc (0:ℝ) (((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3))) →
      (∀n,shell n∈Icc (0:ℝ) 1) → Tendsto shell atTop (𝓝 0) →
      (∀ᶠn in atTop,∀u,(root n).b u=
        initialShellMatrixClock ((beta:ℝ)^2) (epsilon n) (shell n) u) →
      (∀ᶠn in atTop,∀u,(root n).h u=0) →
      ActualWeakSelectedHistoryChain c0 root M →
      (∀n,(M n).xs ≤ 1) →
      (∀ᶠn in atTop,comparisonConditionalScale (M n).context.N delta (M n).context.E (M n).lam ≤ (M n).xs) →
      (∀ᶠn in atTop,(M n).lam+(c0*(M n).xs)^2 ≤ (M n).b 0) →
      (∀ᶠn in atTop,¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
        (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) →
      Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2)
        atTop (𝓝 0) ∧
      ∀ᶠn in atTop,(M n).context.N^(20*delta)*
          actualChildErrorBudget (dim n+1) delta c0 (M n).context.d (M n).lam (M n).xs <
        (M n).actualCompensatedChildPressureCost hc0 (M n).hxs  := by
  classical
  obtain ⟨lower1,upper1,hlower1,hupper1,Hsaving⟩:=
    exists_actual_weak_bounded_shell_bad_test_strength_saving hbeta hTemp
  obtain ⟨lower2,upper2,hlower2,hupper2,Hmacro⟩:=
    macro_successful_child_literal_bad_witness_excluded hbeta hTemp
  refine ⟨min lower1 lower2,max upper1 upper2,lt_min hlower1 hlower2,
    hupper1.trans_le (le_max_left _ _),?_⟩
  intro m delta cl cu Az C0 Ct D Bclock c0 hm hdelta hroom hcl hcu hAz hC0 hCt hD
    hc0 hc01 hmargin hcapmargin hgapmargin hclMacro hcuMacro hclTemp hcuTemp
    dim hdim root M epsilon shell hepsilon hshell hshelllim hb hh Hhistory hxsunit htarget hroomChild Hbad
  let T:ℝ:=(beta:ℝ)^2
  have hT : 0 < T := zero_lt_one.trans hTemp
  have Hweak:=Hsaving m delta cl cu Az C0 Ct D Bclock c0 hm hdelta hroom hcl hcu hAz hC0 hCt hD
    hc0 hc01 hmargin hcapmargin hgapmargin
    (hclMacro.trans (min_le_left _ _)) ((le_max_left _ _).trans hcuMacro)
    hclTemp hcuTemp dim hdim root M epsilon shell hepsilon hshell hshelllim hb hh Hhistory hxsunit Hbad
  refine ⟨Hweak,?_⟩
  by_contra Hnone
  have Hfreq : ∃ᶠn in atTop,(M n).actualCompensatedChildPressureCost hc0 (M n).hxs ≤
      (M n).context.N^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0 (M n).context.d (M n).lam (M n).xs := by
    simpa only [Filter.Frequently,not_not,not_le] using Hnone
  obtain ⟨phi,hphi,Hphi⟩:=extraction_of_frequently_atTop Hfreq
  let x:=fun n=>(M (phi n)).xs
  by_cases HX : Tendsto x atTop (𝓝 0)
  · let G:=actual_bounded_shell_profile_history hm hdelta hcl hAz hC0 hc0 hc01 hT
      hmargin hcapmargin hgapmargin (hdim.comp hphi.tendsto_atTop)
      (fun n=>root (phi n)) (fun n=>M (phi n)) (fun n=>epsilon (phi n)) (fun n=>shell (phi n))
        (fun n=>hepsilon (phi n))
      (hphi.tendsto_atTop.eventually hb) (hphi.tendsto_atTop.eventually hh)
      (Hhistory.comp phi hphi.tendsto_atTop) HX
    have Hfail:=eventually_actual_bad_weak_history_child_pressure_fails_of_eventual_room
      hm hdelta hroom hcl hcu hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin
      (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop) (fun n=>M (phi n)) G
      (fun n=>(M (phi n)).xs) (fun _=>le_rfl) HX (hphi.tendsto_atTop.eventually htarget)
      (Hweak.comp hphi.tendsto_atTop) hclTemp hcuTemp
      (hphi.tendsto_atTop.eventually hroomChild) (hphi.tendsto_atTop.eventually Hbad)
    obtain ⟨n,hn⟩:=Hfail.exists
    exact not_lt_of_ge (Hphi n) hn
  · obtain ⟨xlo,hxlo,psi,hpsi,Hpsi⟩:=
      exists_positive_lower_subsequence_of_nonnegative_not_tendsto_zero x
        (fun n=>(M (phi n)).hxs.le) HX
    let sigma:=phi ∘ psi
    have hsigma : StrictMono sigma:=hphi.comp hpsi
    have Htotal:=((actual_weak_bounded_shell_history_clock_data hm hdelta hcl hAz hC0 hc0 hc01 hT.le
      hmargin hcapmargin hgapmargin dim hdim root M epsilon shell hepsilon hb hh Hhistory).2.2).mono
        (fun n hn=>hn.1)
    have Hcost:=actual_weak_bounded_shell_endpoint_cost_tendsto_zero epsilon shell hepsilon hshell hshelllim hb hh Hhistory
    have hc0T : c0^2 < (beta:ℝ)^2 := by
      have H:=pow_le_pow_left₀ hc0.le hc01 2
      norm_num only [one_pow] at H
      exact H.trans_lt hTemp
    have Hsuccess : ∀ᶠn in atTop,(M (sigma n)).macroChildSweepCost hc0 ≤
        ((dim (sigma n)+1:ℕ):ℝ)^(20*delta)*actualChildErrorBudget (dim (sigma n)+1) delta c0
          (M (sigma n)).context.d (M (sigma n)).lam (M (sigma n)).xs := by
      filter_upwards [] with n
      exact Hphi (psi n)
    have Hgood:=Hmacro m delta cl cu Az C0 Ct D Bclock c0 hm hdelta hcl hcu hAz hC0 hc0 hc01 hc0T
      hmargin (hclMacro.trans (min_le_right _ _)) ((le_max_right _ _).trans hcuMacro)
      (fun n=>dim (sigma n)) (hdim.comp hsigma.tendsto_atTop) (fun n=>M (sigma n)) xlo hxlo
      (fun n=>⟨Hpsi n,hxsunit (sigma n)⟩) (hsigma.tendsto_atTop.eventually htarget)
      (Hweak.comp hsigma.tendsto_atTop) (hsigma.tendsto_atTop.eventually hroomChild)
      (hsigma.tendsto_atTop.eventually Htotal) (Hcost.comp hsigma.tendsto_atTop) Hsuccess
    obtain ⟨n,hn⟩:=(Hgood.and (hsigma.tendsto_atTop.eventually Hbad)).exists
    exact hn.2 hn.1

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 28000000
set_option linter.unusedVariables false
namespace NativeOverlapMinimum
theorem exists_actual_weak_bounded_shell_irregular_child_step
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃lower upper : ℝ,0 < lower ∧ 0 < upper ∧
      ∀m delta cl cu Az C0 Ct D c0 : ℝ,
      ∀hm : 0 < m,∀hdelta : 0 < delta,delta < 3*m →
      0 < cl → 0 < cu → 2 ≤ Az → 0 < C0 → 1 ≤ Ct → D ≤ 1 →
      ∀hc0 : 0 < c0,c0 ≤ 1 → c0 ≤ D →
      delta/4 < 3*m-99*delta → 100*delta < (1:ℝ)/3+m → 0 < 9*m-298*delta →
      cl ≤ lower → upper ≤ cu →
      cl < (beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
      (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*(beta:ℝ)^2)) < cu →
      ∀dim : ℕ→ℕ,∀hdim : Tendsto dim atTop atTop,
      ∀root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D ((beta:ℝ)^2),
      ∀epsilon shell : ℕ→ℝ,(∀n,epsilon n∈Icc (0:ℝ) (((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3))) →
      (∀n,shell n∈Icc (0:ℝ) 1) → Tendsto shell atTop (𝓝 0) →
      (∀ᶠn in atTop,∀u,(root n).b u=
        initialShellMatrixClock ((beta:ℝ)^2) (epsilon n) (shell n) u) →
      (∀ᶠn in atTop,∀u,(root n).h u=0) →
      ActualWeakSelectedHistoryChain c0 root M →
      (∀n,(M n).xs ≤ 1) →
      (∀ᶠn in atTop,comparisonConditionalScale (M n).context.N delta (M n).context.E (M n).lam ≤ (M n).xs) →
      (∀ᶠn in atTop,(M n).lam+(c0*(M n).xs)^2 ≤ (M n).b 0) →
      (∀ᶠn in atTop,¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
        (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) →
      Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/(M n).xs^2)
        atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∃Q : NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D ((beta:ℝ)^2),
        Q.context.d=c0*(M n).xs ∧
        Q.context.E=actualChildErrorBudget (dim n+1) delta c0 (M n).context.d (M n).lam (M n).xs ∧
        (M n).context.N^(delta/4)*(M n).context.E ≤ Q.context.E ∧
        Q.xs∈Icc (comparisonConditionalScale Q.context.N delta Q.context.E Q.lam) 1 ∧
        Q.z=min (2*Q.xs) 1 ∧
        ¬(cl*Q.xs ≤ Q.alpha.val.val Q.xs ∧ Q.alpha.val.val Q.xs ≤ cu*Q.xs) ∧
        (∀u,Q.b u=(M n).b u-laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)) ∧
        (∀u,Q.h u=(M n).h u+laplaceComparisonStrength (M n).context.d (M n).lam ((M n).R u)*(M n).R u)  := by
  classical
  obtain ⟨lower,upper,hlower,hupper,Hfailure⟩:=
    exists_actual_weak_bounded_shell_bad_test_child_pressure_failure hbeta hTemp
  refine ⟨lower,upper,hlower,hupper,?_⟩
  intro m delta cl cu Az C0 Ct D c0 hm hdelta hroom hcl hcu hAz hC0 hCt hD
    hc0 hc01 hc0D hmargin hcapmargin hgapmargin hclMacro hcuMacro hclTemp hcuTemp
    dim hdim root M epsilon shell hepsilon hshell hshelllim hb hh Hhistory hxsunit htarget hroomChild Hbad
  let T:ℝ:=(beta:ℝ)^2
  have hAz0 : 0 ≤ Az := (by norm_num : (0:ℝ) ≤ 2).trans hAz
  have hCt0 : 0 ≤ Ct := zero_le_one.trans hCt
  obtain ⟨Hweak,Hfail⟩:=Hfailure m delta cl cu Az C0 Ct D T c0 hm hdelta hroom hcl hcu hAz0 hC0 hCt0 hD
    hc0 hc01 hmargin hcapmargin hgapmargin hclMacro hcuMacro hclTemp hcuTemp
    dim hdim root M epsilon shell hepsilon hshell hshelllim hb hh Hhistory hxsunit htarget hroomChild Hbad
  have hcl1 : cl ≤ 1 := by
    simpa only [mul_one,(M 0).alpha.property.2] using ((M 0).regular 1 ⟨(M 0).hz.2,le_rfl⟩).1
  have hcu1 : 1 ≤ cu := by
    simpa only [mul_one,(M 0).alpha.property.2] using ((M 0).regular 1 ⟨(M 0).hz.2,le_rfl⟩).2
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout_varying_shell epsilon shell hb hh
  have Hweak1:=Hweak.eventually (eventually_le_nhds zero_lt_one)
  have Hselect:=hdim.eventually (eventually_exists_actual_selected_bad_shell_child_from_target (D:=D) (T:=T)
    hm hdelta hroom hcl hcl1 hcu1 hAz hCt hC0 hc0 hmargin)
  refine ⟨Hweak,?_⟩
  filter_upwards [Hfail,Hps,Hweak1,Hselect,htarget,hroomChild]
    with n hnFail hnHist hnWeak hnSelect hnTarget hnRoom
  let ts:=((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm))
  have hlam : ∀t∈ts,0 ≤ t.lam := by
    intro t ht
    obtain ⟨P,hP,rfl⟩:=List.mem_map.mp ht
    exact P.hlam.le
  have hnD : c0*(M n).xs ≤ D := by
    have H:=mul_le_mul_of_nonneg_left (hxsunit n) hc0.le
    simpa only [mul_one] using H.trans (by simpa only [mul_one] using hc0D)
  have hn1 : c0*(M n).xs ≤ 1 := hnD.trans hD
  have heweak : laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs ≤ (M n).xs^2 :=
    (div_le_one₀ (sq_pos_of_pos (M n).hxs)).mp hnWeak
  obtain ⟨lam,hlam,alpha,hattained,Q,hcontext,hQlam,hAlpha,hbQ,hhQ,hRQ,hdQ,hEQ,
    hGrow,hXs,hZ,hBad,hbHist,hhHist,hlamHist⟩:=hnSelect (M n) (M n).xs (M n).hxs
      hn1 hnD hnTarget heweak hnRoom ts (epsilon n) (shell n)
      hnHist.2.1 hnHist.2.2 hlam (hepsilon n).1 hnFail
  refine ⟨Q,hdQ,hEQ,hGrow,?_,hZ,?_,?_,?_⟩
  · rw [hcontext,hQlam]
    exact hXs
  · rcases hBad with Hlo|Hhi
    · exact fun H=>not_lt_of_ge H.1 Hlo
    · exact fun H=>not_lt_of_ge H.2 Hhi
  · exact fun u=>congrFun hbQ u
  · exact fun u=>congrFun hhQ u

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 32000000
set_option linter.unusedVariables false
namespace NativeOverlapMinimum

theorem exists_actual_weak_bounded_shell_finite_propagation
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃lower upper : ℝ,0 < lower ∧ 0 < upper ∧
      ∀m delta cl cu Az C0 Ct D c0 : ℝ,
      ∀hm : 0 < m,∀hdelta : 0 < delta,delta < 3*m →
      0 < cl → 0 < cu → 2 ≤ Az → 0 < C0 → 1 ≤ Ct → D ≤ 1 →
      ∀hc0 : 0 < c0,c0 ≤ 1 → c0 ≤ D →
      (((actualPropagationDepth delta:ℕ):ℝ)+2)*c0^2 ≤ (beta:ℝ)^2-1 →
      delta/4 < 3*m-99*delta → 100*delta < (1:ℝ)/3+m → 0 < 9*m-298*delta →
      cl ≤ lower → upper ≤ cu →
      cl < (beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
      (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*(beta:ℝ)^2)) < cu →
      ∀dim : ℕ→ℕ,∀hdim : Tendsto dim atTop atTop,
      ∀root : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D ((beta:ℝ)^2),
      ∀epsilon shell : ℕ→ℝ,(∀n,epsilon n∈Icc (0:ℝ) (((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3))) →
      (∀n,shell n∈Icc (0:ℝ) 1) → Tendsto shell atTop (𝓝 0) →
      (∀ᶠn in atTop,∀u,(root n).b u=
        initialShellMatrixClock ((beta:ℝ)^2) (epsilon n) (shell n) u) →
      (∀ᶠn in atTop,∀u,(root n).h u=0) →
      (∀ᶠn in atTop,(root n).context.d ≤ c0) → (∀n,(root n).xs ≤ 1) →
      (∀ᶠn in atTop,comparisonConditionalScale (root n).context.N delta
        (root n).context.E (root n).lam ≤ (root n).xs) →
      (∀ᶠn in atTop,¬(cl*(root n).xs ≤ (root n).alpha.val.val (root n).xs ∧
        (root n).alpha.val.val (root n).xs ≤ cu*(root n).xs)) → False := by
  classical
  obtain ⟨lower,upper,hlower,hupper,Hstep⟩:=exists_actual_weak_bounded_shell_irregular_child_step hbeta hTemp
  refine ⟨lower,upper,hlower,hupper,?_⟩
  intro m delta cl cu Az C0 Ct D c0 hm hdelta hroom hcl hcu hAz hC0 hCt hD
    hc0 hc01 hc0D hbudget hmargin hcapmargin hgapmargin hclMacro hcuMacro hclTemp hcuTemp
    dim hdim root epsilon shell hepsilon hshell hshelllim hb hh hrootCap hrootUnit hrootTarget hrootBad
  let T:ℝ:=(beta:ℝ)^2
  let depth:=actualPropagationDepth delta
  have Hbase : ∀ᶠn in atTop,T-1 ≤ (root n).b 0 := by
    filter_upwards [hb] with n hn
    rw [hn 0]
    have hN : (1:ℝ) ≤ ((dim n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have He:=(hepsilon n).2.trans (Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num : -(1:ℝ)/3 ≤ 0))
    unfold initialShellMatrixClock
    split_ifs <;> dsimp only [T] <;> linarith only [He]
  have Hchains : ∀k : ℕ,k ≤ depth →
      ∃phi : ℕ→ℕ,StrictMono phi ∧
        ∃M : (n:ℕ)→NativeOverlapMinimum (dim (phi n)+1) m delta cl cu Az C0 Ct D T,
          ActualWeakNativeErrorGrowthHistory c0 (fun n=>root (phi n)) k M ∧
          (∀n,(M n).xs ≤ 1) ∧
          (∀ᶠn in atTop,comparisonConditionalScale (M n).context.N delta
            (M n).context.E (M n).lam ≤ (M n).xs) ∧
          (∀ᶠn in atTop,¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
            (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      exact ⟨id,strictMono_id,root,.root,hrootUnit,hrootTarget,hrootBad⟩
    | succ k ih =>
      intro hk
      obtain ⟨phi,hphi,M,Hhistory,Hunit,Htarget,Hbad⟩:=ih (Nat.le_of_succ_le hk)
      have hbudgetK : ((k:ℝ)+2)*c0^2 ≤ T-1 := by
        have HK : (k:ℝ) ≤ (depth:ℝ) := by exact_mod_cast Nat.le_of_succ_le hk
        have HB : ((depth:ℝ)+2)*c0^2 ≤ T-1 := by simpa only [depth,T] using hbudget
        have H := mul_le_mul_of_nonneg_right (add_le_add_right HK 2) (sq_nonneg c0)
        simpa only [add_comm] using H.trans (by simpa only [add_comm] using HB)
      have Hroom:=Hhistory.covariance_room hc0.le (hphi.tendsto_atTop.eventually hrootCap)
        (hphi.tendsto_atTop.eventually Hbase) (Eventually.of_forall Hunit) hbudgetK
      obtain ⟨Hweak,Hnext⟩:=Hstep m delta cl cu Az C0 Ct D c0 hm hdelta hroom hcl hcu hAz hC0 hCt hD
        hc0 hc01 hc0D hmargin hcapmargin hgapmargin hclMacro hcuMacro hclTemp hcuTemp
        (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop) (fun n=>root (phi n)) M
        (fun n=>epsilon (phi n)) (fun n=>shell (phi n)) (fun n=>hepsilon (phi n)) (fun n=>hshell (phi n)) (hshelllim.comp hphi.tendsto_atTop)
        (hphi.tendsto_atTop.eventually hb) (hphi.tendsto_atTop.eventually hh)
        Hhistory.weak_history Hunit Htarget Hroom Hbad
      obtain ⟨n0,Hn0⟩:=eventually_atTop.mp Hnext
      let shift:=fun n:ℕ=>n+n0
      have hshift : StrictMono shift:=fun i j hij=>Nat.add_lt_add_right hij n0
      choose Q HQ using fun n=>Hn0 (shift n) (Nat.le_add_left n0 n)
      let sigma:=phi ∘ shift
      have hsigma : StrictMono sigma:=hphi.comp hshift
      have Hnew : ActualWeakNativeErrorGrowthHistory c0 (fun n=>root (sigma n)) (k+1) Q :=
        .child (Hhistory.comp shift hshift.tendsto_atTop)
          (Eventually.of_forall (fun n=>Hunit (shift n)))
          (hshift.tendsto_atTop.eventually Htarget) (Hweak.comp hshift.tendsto_atTop)
          (Eventually.of_forall (fun n=>(HQ n).1))
          (Eventually.of_forall (fun n=>(HQ n).2.1))
          (Eventually.of_forall (fun n=>(HQ n).2.2.2.2.2.2.1))
          (Eventually.of_forall (fun n=>(HQ n).2.2.2.2.2.2.2))
          (Eventually.of_forall (fun n=>(HQ n).2.2.1))
      exact ⟨sigma,hsigma,Q,Hnew,fun n=>(HQ n).2.2.2.1.2,
        Eventually.of_forall (fun n=>(HQ n).2.2.2.1.1),
        Eventually.of_forall (fun n=>(HQ n).2.2.2.2.2.1)⟩
  obtain ⟨phi,hphi,M,Hhistory,_⟩:=Hchains depth le_rfl
  exact Hhistory.false_at_propagation_depth hm hdelta hC0 (hdim.comp hphi.tendsto_atTop)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
