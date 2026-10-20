module

public import ComparisonNativeActualWallHistoryPropagationStep
public import ComparisonNativeActualWeakErrorGrowthHistory

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 32000000
set_option linter.unusedVariables false
namespace NativeOverlapMinimum

theorem exists_actual_wall_history_finite_propagation
    {beta : ℝ≥0} (hbeta : 0 < beta) (hTemp : 1 < (beta:ℝ)^2) :
    ∃lower upper : ℝ,0 < lower ∧ 0 < upper ∧
      ∀m delta cl cu Az C0 Ct D c0 rho : ℝ,
      ∀hm : 0 < m,∀hdelta : 0 < delta,delta < 3*m →
      0 < cl → 0 < cu → 2 ≤ Az → 0 < C0 → 1 ≤ Ct → D ≤ 1 →
      ∀hc0 : 0 < c0,c0 ≤ 1 → c0 ≤ D →
      (((actualPropagationDepth delta:ℕ):ℝ)+2)*c0^2 ≤ rho →
      delta/4 < 3*m-99*delta → 100*delta < (1:ℝ)/3+m → 0 < 9*m-298*delta →
      cl ≤ lower → upper ≤ cu →
      cl < (beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
      (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*(beta:ℝ)^2)) < cu →
      ∀dim : ℕ→ℕ,∀hdim : Tendsto dim atTop atTop,
      ∀root : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D ((beta:ℝ)^2),
      ∀Groot : ActualNativeWallHistory root ((beta:ℝ)^2) c0,
      Tendsto (fun n=>(Groot.wall n).data.s) atTop (𝓝 0) →
      Tendsto (fun n=>(Groot.wall n).data.d) atTop (𝓝 0) →
      (∀ᶠn in atTop,rho ≤ (root n).b 0) →
      (∀ᶠn in atTop,(root n).context.d ≤ c0) → (∀n,(root n).xs ≤ 1) →
      (∀ᶠn in atTop,comparisonConditionalScale (root n).context.N delta
        (root n).context.E (root n).lam ≤ (root n).xs) →
      (∀ᶠn in atTop,¬(cl*(root n).xs ≤ (root n).alpha.val.val (root n).xs ∧
        (root n).alpha.val.val (root n).xs ≤ cu*(root n).xs)) → False := by
  classical
  obtain ⟨lower,upper,hlower,hupper,Hstep⟩:=exists_actual_wall_history_irregular_child_step hbeta hTemp
  refine ⟨lower,upper,hlower,hupper,?_⟩
  intro m delta cl cu Az C0 Ct D c0 rho hm hdelta hroom hcl hcu hAz hC0 hCt hD
    hc0 hc01 hc0D hbudget hmargin hcapmargin hgapmargin hclMacro hcuMacro hclTemp hcuTemp
    dim hdim root Groot hs hdwall Hbase hrootCap hrootUnit hrootTarget hrootBad
  let T:ℝ:=(beta:ℝ)^2
  let depth:=actualPropagationDepth delta
  have Hchains : ∀k : ℕ,k ≤ depth →
      ∃phi : ℕ→ℕ,StrictMono phi ∧
        ∃M : (n:ℕ)→NativeOverlapMinimum (dim (phi n)+1) m delta cl cu Az C0 Ct D T,
          ∃G : ActualNativeWallHistory M T c0,
          ActualWeakNativeErrorGrowthHistory c0 (fun n=>root (phi n)) k M ∧
          Tendsto (fun n=>(G.wall n).data.s) atTop (𝓝 0) ∧
          Tendsto (fun n=>(G.wall n).data.d) atTop (𝓝 0) ∧
          (∀n,(M n).xs ≤ 1) ∧
          (∀ᶠn in atTop,comparisonConditionalScale (M n).context.N delta
            (M n).context.E (M n).lam ≤ (M n).xs) ∧
          (∀ᶠn in atTop,¬(cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
            (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs)) := by
    intro k
    induction k with
    | zero =>
      intro hk
      exact ⟨id,strictMono_id,root,Groot,.root,hs,hdwall,hrootUnit,hrootTarget,hrootBad⟩
    | succ k ih =>
      intro hk
      obtain ⟨phi,hphi,M,G,Hhistory,Hslow,Hradius,Hunit,Htarget,Hbad⟩:=ih (Nat.le_of_succ_le hk)
      have hbudgetK : ((k:ℝ)+2)*c0^2 ≤ rho := by
        have HK : (k:ℝ) ≤ (depth:ℝ) := by exact_mod_cast Nat.le_of_succ_le hk
        have HB : ((depth:ℝ)+2)*c0^2 ≤ rho := by simpa only [depth] using hbudget
        have H := mul_le_mul_of_nonneg_right (add_le_add_right HK 2) (sq_nonneg c0)
        simpa only [add_comm] using H.trans (by simpa only [add_comm] using HB)
      have Hroom:=Hhistory.covariance_room (T:=rho+1) hc0.le (hphi.tendsto_atTop.eventually hrootCap)
        (by simpa only [add_sub_cancel_right] using hphi.tendsto_atTop.eventually Hbase)
        (Eventually.of_forall Hunit) (by simpa only [add_sub_cancel_right] using hbudgetK)
      obtain ⟨Hweak,Hnext⟩:=Hstep m delta cl cu Az C0 Ct D c0 hm hdelta hroom hcl hcu hAz hC0 hCt hD
        hc0 hc01 hc0D hmargin hcapmargin hgapmargin hclMacro hcuMacro hclTemp hcuTemp
        (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop) M G Hslow Hradius
        Hunit Htarget Hroom Hbad
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
      let Gnew := (G.comp shift hshift).append_child Q
        (fun n=>(M (shift n)).xs) (fun n=>(M (shift n)).hxs)
        (Eventually.of_forall (fun n=>Hunit (shift n)))
        (hshift.tendsto_atTop.eventually Htarget)
        (Eventually.of_forall (fun n=>(M (shift n)).hzxs))
        (Hweak.comp hshift.tendsto_atTop)
        (Eventually.of_forall (fun n=>(HQ n).1))
        (Eventually.of_forall (fun n=>(HQ n).2.1))
        (Eventually.of_forall (fun n=>(HQ n).2.2.2.2.2.2.1))
        (Eventually.of_forall (fun n=>(HQ n).2.2.2.2.2.2.2))
      exact ⟨sigma,hsigma,Q,Gnew,Hnew,Hslow.comp hshift.tendsto_atTop,
        Hradius.comp hshift.tendsto_atTop,fun n=>(HQ n).2.2.2.1.2,
        Eventually.of_forall (fun n=>(HQ n).2.2.2.1.1),
        Eventually.of_forall (fun n=>(HQ n).2.2.2.2.2.1)⟩
  obtain ⟨phi,hphi,M,G,Hhistory,_⟩:=Hchains depth le_rfl
  exact Hhistory.false_at_propagation_depth hm hdelta hC0 (hdim.comp hphi.tendsto_atTop)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
