module

public import ComparisonNativeActualWeakErrorGrowthHistory

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false

namespace NativeOverlapMinimum

theorem theta_zero_finite_native_chain_of_one_step
    {m delta cl cu Az C0 Ct D Bclock c0 rho:ℝ}
    (hm:0 < m) (hdelta:0 < delta) (hC0:0 < C0) (hc0:0 < c0)
    (dim:ℕ → ℕ) (hdim:Tendsto dim atTop atTop)
    (root:(j:ℕ) → NativeOverlapMinimum (dim j+1) m delta cl cu Az C0 Ct D Bclock)
    (hrootCap:∀ᶠj in atTop,(root j).context.d ≤ c0)
    (hbase:∀ᶠj in atTop,rho ≤ (root j).b 0)
    (hbudget:(((actualPropagationDepth delta:ℕ):ℝ)+2)*c0^2 ≤ rho)
    (hunit:∀j,(root j).xs ≤ 1)
    (htarget:∀ᶠj in atTop,comparisonConditionalScale (root j).context.N delta
      (root j).context.E (root j).lam ≤ (root j).xs)
    (hbad:∀ᶠj in atTop,
      ¬(cl*(root j).xs ≤ (root j).alpha.val.val (root j).xs ∧
        (root j).alpha.val.val (root j).xs ≤ cu*(root j).xs))
    (Hstep:∀(phi:ℕ → ℕ)(hphi:StrictMono phi)(k:ℕ)
      (P:(j:ℕ) → NativeOverlapMinimum (dim (phi j)+1) m delta cl cu Az C0 Ct D Bclock),
      ActualWeakNativeErrorGrowthHistory c0 (fun j=>root (phi j)) k P  → 
      (∀j,(P j).xs ≤ 1)  → 
      (∀ᶠj in atTop,comparisonConditionalScale (P j).context.N delta
        (P j).context.E (P j).lam ≤ (P j).xs)  → 
      (∀ᶠj in atTop,(P j).lam+(c0*(P j).xs)^2 ≤ (P j).b 0)  → 
      (∀ᶠj in atTop,
        ¬(cl*(P j).xs ≤ (P j).alpha.val.val (P j).xs ∧
          (P j).alpha.val.val (P j).xs ≤ cu*(P j).xs))  → 
      Tendsto (fun j=>laplaceComparisonStrength (P j).context.d (P j).lam (P j).xs/
        (P j).xs^2) atTop (𝓝 0) ∧
      ∀ᶠj in atTop,∃Q:NativeOverlapMinimum (dim (phi j)+1) m delta cl cu Az C0 Ct D Bclock,
        Q.context.d=c0*(P j).xs ∧
        Q.context.E=actualChildErrorBudget (dim (phi j)+1) delta c0
          (P j).context.d (P j).lam (P j).xs ∧
        (P j).context.N^(delta/4)*(P j).context.E ≤ Q.context.E ∧
        Q.xs∈Icc (comparisonConditionalScale Q.context.N delta Q.context.E Q.lam) 1 ∧
        ¬(cl*Q.xs ≤ Q.alpha.val.val Q.xs ∧ Q.alpha.val.val Q.xs ≤ cu*Q.xs) ∧
        (∀u,Q.b u=(P j).b u-laplaceComparisonStrength (P j).context.d (P j).lam ((P j).R u)) ∧
        (∀u,Q.h u=(P j).h u+laplaceComparisonStrength (P j).context.d (P j).lam ((P j).R u)*(P j).R u)) :
    False := by
  classical
  let depth:=actualPropagationDepth delta
  have Hchains:∀k:ℕ,k ≤ depth → 
      ∃phi:ℕ → ℕ,StrictMono phi ∧
        ∃P:(j:ℕ) → NativeOverlapMinimum (dim (phi j)+1) m delta cl cu Az C0 Ct D Bclock,
          ActualWeakNativeErrorGrowthHistory c0 (fun j=>root (phi j)) k P ∧
          (∀j,(P j).xs ≤ 1) ∧
          (∀ᶠj in atTop,comparisonConditionalScale (P j).context.N delta
            (P j).context.E (P j).lam ≤ (P j).xs) ∧
          (∀ᶠj in atTop,
            ¬(cl*(P j).xs ≤ (P j).alpha.val.val (P j).xs ∧
              (P j).alpha.val.val (P j).xs ≤ cu*(P j).xs)) := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨id,strictMono_id,root,.root,hunit,htarget,hbad⟩
    | succ k ih =>
      intro hk
      obtain ⟨phi,hphi,P,Hhistory,Hunit,Htarget,Hbad⟩:=ih (Nat.le_of_succ_le hk)
      have hbudgetK:((k:ℝ)+2)*c0^2 ≤ rho:=by
        have HK:(k:ℝ) ≤ (depth:ℝ):=by exact_mod_cast Nat.le_of_succ_le hk
        have HB:((depth:ℝ)+2)*c0^2 ≤ rho:=by simpa only [depth] using hbudget
        have H:=mul_le_mul_of_nonneg_right (add_le_add_right HK 2) (sq_nonneg c0)
        simpa only [add_comm] using H.trans (by simpa only [add_comm] using HB)
      have Hroom:=Hhistory.covariance_room (T:=rho+1) hc0.le
        (hphi.tendsto_atTop.eventually hrootCap)
        (by simpa only [add_sub_cancel_right] using hphi.tendsto_atTop.eventually hbase)
        (Eventually.of_forall Hunit)
        (by simpa only [add_sub_cancel_right] using hbudgetK)
      obtain ⟨Hweak,Hnext⟩:=Hstep phi hphi k P Hhistory Hunit Htarget Hroom Hbad
      obtain ⟨j0,Hj0⟩:=eventually_atTop.mp Hnext
      let shift:=fun j:ℕ=>j+j0
      have hshift:StrictMono shift:=fun i j hij=>Nat.add_lt_add_right hij j0
      choose Q hD hE hGrow hXs hBad hMat hField using
        fun j=>Hj0 (shift j) (Nat.le_add_left j0 j)
      let sigma:=phi ∘ shift
      have hsigma:StrictMono sigma:=hphi.comp hshift
      have Hnew:ActualWeakNativeErrorGrowthHistory c0 (fun j=>root (sigma j)) (k+1) Q:=
        .child (Hhistory.comp shift hshift.tendsto_atTop)
          (Eventually.of_forall (fun j=>Hunit (shift j)))
          (hshift.tendsto_atTop.eventually Htarget)
          (Hweak.comp hshift.tendsto_atTop)
          (Eventually.of_forall hD) (Eventually.of_forall hE)
          (Eventually.of_forall hMat) (Eventually.of_forall hField)
          (Eventually.of_forall hGrow)
      exact ⟨sigma,hsigma,Q,Hnew,fun j=>(hXs j).2,
        Eventually.of_forall (fun j=>(hXs j).1),Eventually.of_forall hBad⟩
  obtain ⟨phi,hphi,P,Hhistory,_⟩:=Hchains depth le_rfl
  exact Hhistory.false_at_propagation_depth hm hdelta hC0 (hdim.comp hphi.tendsto_atTop)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
