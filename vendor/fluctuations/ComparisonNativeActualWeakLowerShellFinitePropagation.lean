module

public import ComparisonNativeActualWeakLowerShellPropagationStep
public import ComparisonNativeActualWeakErrorGrowthHistory

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 32000000
set_option linter.unusedVariables false
namespace NativeOverlapMinimum

theorem exists_actual_weak_lower_shell_finite_propagation
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
      ∀shell : ℕ→ℝ,(∀n,shell n∈Icc (0:ℝ) 1) → Tendsto shell atTop (𝓝 0) →
      (∀ᶠn in atTop,∀u,(root n).b u=
        initialShellMatrixClock ((beta:ℝ)^2) (((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3)) (shell n) u) →
      (∀ᶠn in atTop,∀u,(root n).h u=0) →
      (∀ᶠn in atTop,(root n).context.d ≤ c0) → (∀n,(root n).xs ≤ 1) →
      (∀ᶠn in atTop,comparisonConditionalScale (root n).context.N delta
        (root n).context.E (root n).lam ≤ (root n).xs) →
      (∀ᶠn in atTop,¬(cl*(root n).xs ≤ (root n).alpha.val.val (root n).xs ∧
        (root n).alpha.val.val (root n).xs ≤ cu*(root n).xs)) → False := by
  classical
  obtain ⟨lower,upper,hlower,hupper,Hstep⟩:=exists_actual_weak_lower_shell_irregular_child_step hbeta hTemp
  refine ⟨lower,upper,hlower,hupper,?_⟩
  intro m delta cl cu Az C0 Ct D c0 hm hdelta hroom hcl hcu hAz hC0 hCt hD
    hc0 hc01 hc0D hbudget hmargin hcapmargin hgapmargin hclMacro hcuMacro hclTemp hcuTemp
    dim hdim root shell hshell hshelllim hb hh hrootCap hrootUnit hrootTarget hrootBad
  let T:ℝ:=(beta:ℝ)^2
  let depth:=actualPropagationDepth delta
  have Hbase : ∀ᶠn in atTop,T-1 ≤ (root n).b 0 := by
    filter_upwards [hb] with n hn
    rw [hn 0]
    have hN : (1:ℝ) ≤ ((dim n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have He:=Real.rpow_le_one_of_one_le_of_nonpos hN (by norm_num : -(1:ℝ)/3 ≤ 0)
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
        (fun n=>shell (phi n)) (fun n=>hshell (phi n)) (hshelllim.comp hphi.tendsto_atTop)
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
