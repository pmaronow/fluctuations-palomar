module

public import ComparisonActualHighWallSuccessfulHighOnlyMinimumFromSweep
public import ComparisonActualHighOnlyWallHistoryContext
public import ComparisonActualHighWallWeakenBookkeepingConstants
public import ComparisonNativeActualChildDirectCalibration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000
set_option autoImplicit false
set_option linter.unusedVariables false
namespace ActualHighWallOverlapMinimum
variable {m cl cu Az C0 T c0 C : ℝ}

theorem successful_high_only_child_physical_context_compatible
    (hm : 0 < m) (hmsmall : m ≤ (1:ℝ)/120)
    (hcl : 0 < cl) (hcu : 0 < cu) (hC0 : 0 < C0)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1) (hTpos : 0 < T)
    (hC : 1 ≤ C) (hAzC : Az ≤ 4*C/cl)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (P : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m (m/10000) cl cu Az C0 1 1 T)
    (x : ℕ→ℝ) (hxs : ∀n,(P n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hreserve : ∀n,(P n).data.d^2+(c0*x n)^2 ≤ (P n).data.epsilon)
    (Q : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m (m/10000)
      (cl/4) (4*cu) (4*C/cl) C0 1 1 T)
    (hdata : ∀n,(Q n).data=(P n).actualHighOnlyChild hc0
      ((P n).hxs.trans_le (hxs n)) (hreserve n))
    (hQlam : ∀n,(Q n).lam=(c0*x n)^2) (hQxs : ∀n,(Q n).xs=x n)
    (hT : ∀ᶠn in atTop,(P n).data.T=T)
    (hE : ∀ᶠn in atTop,(P n).data.E=wallHighError m (dim n+1))
    (hd : ∀ᶠn in atTop,(P n).data.d=wallHighD m (dim n+1))
    (hs : ∀ᶠn in atTop,(P n).data.s=wallHighMass m (dim n+1))
    (hxunit : ∀ᶠn in atTop,x n ≤ 1)
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale (P n).data.N (m/10000)
      (P n).data.E ((P n).data.d^2) ≤ x n)
    (hweak : Tendsto (fun n=>(P n).data.g (x n)/(x n)^2) atTop (𝓝 0)) :
    Nonempty (ActualHighOnlyOverlapMinimum.HighOnlyActualComparableBandContext Q T) ∧
      (∀n,max (Q n).xs (Real.sqrt (laplaceComparisonStrength (Q n).context.d
        (Q n).lam (Q n).xs))=x n) ∧
      (∀n,(Q n).xs^2 ≤ (max 1 (1/c0^3))^2*
        laplaceComparisonStrength (Q n).context.d (Q n).lam (Q n).xs) := by
  have hx n : 0 < x n := (P n).hxs.trans_le (hxs n)
  have hcl4 : cl/4 ≤ cl := by linarith
  have hcu4 : cu ≤ 4*cu := by linarith
  let PW := fun n=>(P n).weakenBookkeepingConstants hcl4 hcu4 hAzC le_rfl le_rfl le_rfl
  have H : ActualHighOnlyOverlapMinimum.ActualWeakHighOnlyHistoryChain c0 Q Q := .root
  have HQd n : (Q n).context.d=c0*x n := by
    change (Q n).data.d=_
    rw [hdata n]
    rfl
  have HQE n : (Q n).context.E=actualChildErrorBudget (dim n+1) (m/10000) c0
      (PW n).data.d ((PW n).data.d^2) (x n) := by
    change (Q n).data.E=_
    rw [hdata n]
    rfl
  have HQs n : (Q n).data.s=(PW n).data.s := by rw [hdata n]; rfl
  have HQb n u : (Q n).b u=(PW n).data.b (PW n).alpha u := by
    change (Q n).data.b u=_
    rw [hdata n]
    rfl
  have HQh n u : (Q n).h u=(PW n).data.h (PW n).alpha u := by
    change (Q n).data.h u=_
    rw [hdata n]
    rfl
  have Hcap : ∀ᶠn in atTop,(PW n).z ≤ (4*C/cl)*x n := by
    apply Eventually.of_forall
    intro n
    exact (PW n).hzxs.trans (mul_le_mul_of_nonneg_left (hxs n) (by positivity))
  have Hxs : Tendsto (fun n=>(Q n).xs) atTop (𝓝 0) := by
    simpa only [hQxs] using hxlim
  have HG := H.exists_concrete_wall_comparable_context hm hmsmall (by positivity) (by positivity)
    hC0 hc0 hc01 hTpos dim hdim PW Q Q hT hE hd hs (Eventually.of_forall HQs)
    x hx hxunit htarget Hcap hweak (Eventually.of_forall HQd) (Eventually.of_forall HQE)
    (Eventually.of_forall HQb) (Eventually.of_forall HQh) Hxs
  refine ⟨HG,?_,?_⟩
  · intro n
    rw [hQxs n,HQd n,hQlam n]
    have Hg := laplaceComparisonStrength_le (c0*x n) (sq_nonneg (c0*x n)) (x n)
    have Hd : c0*x n ≤ x n := by nlinarith [hx n]
    have Hsqrt : Real.sqrt (laplaceComparisonStrength (c0*x n) ((c0*x n)^2) (x n)) ≤ x n := by
      exact (Real.sqrt_le_left (hx n).le).mpr (Hg.trans (sq_le_sq₀ (mul_pos hc0 (hx n)).le (hx n).le |>.mpr Hd))
    exact max_eq_left Hsqrt
  · intro n
    rw [hQxs n,HQd n,hQlam n]
    exact (actual_child_direct_calibration_at_parent_test (delta:=m/10000)
      (d:=(P n).data.d) (lam:=(P n).data.d^2)
      (by omega : 0<dim n+1) hc0 hc01 (sq_pos_of_pos (P n).data.hd) (hx n)).2.2

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
