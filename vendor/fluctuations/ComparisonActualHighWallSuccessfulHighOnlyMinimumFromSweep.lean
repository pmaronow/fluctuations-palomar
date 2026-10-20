module

public import ComparisonActualHighWallAttainedHighOnlyChildAtTest
public import ComparisonActualHighWallSuccessfulChildMinimumAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 1600000
set_option autoImplicit false
set_option linter.unusedVariables false
namespace ActualHighWallOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem eventually_exists_high_only_child_minimum_from_successful_sweep
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) {c0 : ℝ} (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hreserve : ∀n,(M n).data.d^2+(c0*x n)^2 ≤ (M n).data.epsilon)
    (hsweep : ∀ᶠn in atTop,(M n).highOnlyChildSweepCostAtTest hc0
      ((M n).hxs.trans_le (hxs n)) (hreserve n) ≤ ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0 (M n).data.d ((M n).data.d^2) (x n))
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale (M n).data.N delta (M n).data.E
      ((M n).data.d^2) ≤ x n)
    (hT : ∀ᶠn in atTop,(M n).data.T ≤ T)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d ((M n).data.d^2) (x n)/(x n)^2)
      atTop (𝓝 0))
    (hs : Tendsto (fun n=>(M n).data.s/x n) atTop (𝓝 0))
    (hr : Tendsto (fun n=>(M n).data.rmin/x n) atTop (𝓝 0)) :
    ∃C : ℝ,1 ≤ C ∧ Az ≤ 4*C/cl ∧ ∀ᶠn in atTop,
      ∃a : ActualShiftedParentChildCall (dim n+1) delta,
      ∃Q : ActualHighOnlyOverlapMinimum (dim n+1) m delta (cl/4) (4*cu) (4*C/cl) C0 1 1 T,
        a.context=(M n).data.shiftedParentData ∧ a.R=(M n).data.wallRadius (M n).alpha ∧
        a.err=(M n).highOnlyChildSweepCostAtTest hc0 ((M n).hxs.trans_le (hxs n)) (hreserve n) ∧
        Q.data=(M n).actualHighOnlyChild hc0 ((M n).hxs.trans_le (hxs n)) (hreserve n) ∧
        Q.lam=(c0*x n)^2 ∧ HEq Q.optimizer a.childOptimizer ∧
        Q.xs=x n ∧ Q.R=a.Z ∧ Q.z=min ((4*C/cl)*x n) 1 := by
  classical
  have hx n : 0 < x n := (M n).hxs.trans_le (hxs n)
  choose a ha using (fun n=>(M n).exists_attained_high_only_child_at_test hc0 (hx n) (hreserve n))
  have hcontext n : (a n).context=(M n).data.shiftedParentData := (ha n).1
  have hR n : (a n).R=(M n).data.wallRadius (M n).alpha := (ha n).2.2.1
  have hdata n : (a n).childData=(M n).actualHighOnlyChild hc0 (hx n) (hreserve n) :=
    (ha n).2.2.2.1
  have hEchild : ∀ᶠn in atTop,(a n).childData.E=actualChildErrorBudget (dim n+1) delta c0
      (M n).data.d ((M n).data.d^2) (x n) := by
    apply Eventually.of_forall
    intro n
    rcases ha n with ⟨_,_,_,_,_,_,hE,_,_,_,_⟩
    exact hE
  have hchild : ∀ᶠn in atTop,(a n).childRadius=c0*x n ∧ (a n).childLam=(c0*x n)^2 ∧
      (a n).err ≤ ((dim n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim n+1) delta c0 (M n).data.d ((M n).data.d^2) (x n) := by
    filter_upwards [hsweep] with n hn
    rcases ha n with ⟨_,_,_,_,hd,hl,_,_,_,_,he⟩
    refine ⟨hd,hl,?_⟩
    rw [he]
    exact hn
  obtain ⟨C,hC,hAzC,HQ⟩ := eventually_exists_successful_high_only_child_minimum hm hdelta hcl hcu hAz hC0
    hc0 hc01 hmargin dim hdim M a x hxs hxlim hcontext hR hchild hEchild htarget hT hweak hs hr
  refine ⟨C,hC,hAzC,?_⟩
  filter_upwards [HQ] with n hnQ
  obtain ⟨Q,hQdata,hQlam,hQoptimizer,hQxs,hQz,hQR⟩ := hnQ
  rcases ha n with ⟨_,_,_,_,_,hl,_,_,_,_,he⟩
  exact ⟨a n,Q,hcontext n,hR n,he,hQdata.trans (hdata n),hQlam.trans hl,hQoptimizer,hQxs,hQR,hQz⟩

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
