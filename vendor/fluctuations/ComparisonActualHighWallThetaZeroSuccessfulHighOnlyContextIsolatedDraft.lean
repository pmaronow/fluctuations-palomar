module

public import ComparisonActualHighWallThetaZeroSuccessfulHighOnlyMinimumIsolatedDraft
public import ComparisonActualHighWallThetaZeroHighOnlyHistoryContext
public import ComparisonActualHighWallThetaZeroWeakenConstantsIsolatedDraft
public import ComparisonNativeActualChildDirectCalibration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false

namespace ActualThetaZeroOverlapMinimum

theorem theta_zero_successful_high_only_child_physical_context
    {m delta cl cu Az C0 T c0 C : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl)
    (hcu : 0 < cu) (hC0 : 0 < C0) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hTpos : 0 < T) (hC : 1 ≤ C) (hAzC : Az ≤ 4*C/cl)
    (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (P : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 1 1 T)
    (a : (n:ℕ)→ActualShiftedParentChildCall (dim n+1) delta)
    (Q : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
      m delta (cl/4) (4*cu) (4*C/cl) C0 1 1 T)
    (x : ℕ→ℝ) (hxs : ∀n,(P n).xs ≤ x n)
    (hPx : ∀n,(P n).xs=x n)
    (hxlim : Tendsto x atTop (𝓝 0))
    (hcontext : ∀n,(a n).context=(P n).data.thetaZeroShiftedParentData
      (P n).lam (P n).hlam (P n).hld)
    (hR : ∀n,(a n).R=(P n).data.wallRadius (P n).alpha)
    (hdata : ∀n,(Q n).data=(a n).childData)
    (hchildD : ∀n,(a n).childRadius=c0*x n)
    (hchildE : ∀n,(a n).childData.E=actualChildErrorBudget (dim n+1)
      delta c0 (P n).data.d (P n).lam (x n))
    (hQlam : ∀n,(Q n).lam=(c0*x n)^2)
    (hQxs : ∀n,(Q n).xs=x n)
    (hT : ∀ᶠn in atTop,(P n).data.T=T)
    (hxunit : ∀ᶠn in atTop,x n ≤ 1)
    (htarget : ∀ᶠn in atTop,comparisonConditionalScale
      (P n).data.N delta (P n).data.E (P n).lam ≤ x n)
    (hweak : Tendsto (fun n=>laplaceComparisonStrength (P n).data.d
      (P n).lam (x n)/(x n)^2) atTop (𝓝 0))
    (hs : Tendsto (fun n=>(P n).data.s/
      actualChildCutoff (dim n+1) delta c0 (P n).data.d
        (P n).lam (x n)) atTop (𝓝 0)) :
    Nonempty (ActualHighOnlyOverlapMinimum.HighOnlyActualComparableBandContext Q T) ∧
      (∀n,max (Q n).xs (Real.sqrt (laplaceComparisonStrength
        (Q n).context.d (Q n).lam (Q n).xs))=x n) ∧
      (∀n,(Q n).xs^2 ≤ (max 1 (1/c0^3))^2*
        laplaceComparisonStrength (Q n).context.d (Q n).lam (Q n).xs) := by
  have hcl4 : cl/4 ≤ cl := by linarith
  have hcu4 : cu ≤ 4*cu := by linarith
  let PW := fun n=>(P n).weakenConstants hcl4 hcu4 hAzC le_rfl le_rfl le_rfl
  have H : ActualHighOnlyOverlapMinimum.ActualWeakHighOnlyHistoryChain c0 Q Q := .root
  have hx n : 0 < x n := (P n).hxs.trans_le (hxs n)
  have Hsame : ∀ᶠn in atTop,(Q n).data.s=(PW n).data.s := by
    apply Eventually.of_forall
    intro n
    rw [hdata n]
    change (a n).childData.s=(P n).data.s
    rw [(a n).sameInitialMass,hcontext n]
    rfl
  have Hb : ∀ᶠn in atTop,∀u,(Q n).b u=(PW n).changedBare u := by
    apply Eventually.of_forall
    intro n u
    have Hbare := (a n).bare_clocks_eq_theta_zero_wall (P n)
      (hcontext n) (hR n)
    change (Q n).data.b u=(P n).changedBare u
    rw [hdata n,Hbare.1]
  have Hh : ∀ᶠn in atTop,∀u,(Q n).h u=(PW n).changedField u := by
    apply Eventually.of_forall
    intro n u
    have Hbare := (a n).bare_clocks_eq_theta_zero_wall (P n)
      (hcontext n) (hR n)
    change (Q n).data.h u=(P n).changedField u
    rw [hdata n,Hbare.2]
  have Hcut : ∀ᶠn in atTop,actualChildCutoff (dim n+1) delta c0
      (PW n).data.d (PW n).lam (PW n).xs ≤ comparisonLowerScale
        (Q n).context.N (Q n).context.E (Q n).context.d := by
    apply Eventually.of_forall
    intro n
    change actualChildCutoff (dim n+1) delta c0 (P n).data.d
      (P n).lam (P n).xs ≤ comparisonLowerScale (Q n).data.N
      (Q n).data.E (Q n).data.d
    rw [hPx n]
    rw [hdata n,hchildE n]
    change actualChildCutoff (dim n+1) delta c0 (P n).data.d
      (P n).lam (x n) ≤ comparisonLowerScale ((dim n+1:ℕ):ℝ)
      (actualChildErrorBudget (dim n+1) delta c0 (P n).data.d
        (P n).lam (x n)) (a n).childRadius
    rw [hchildD n]
    rfl
  have Hunit : ∀ᶠn in atTop,(PW n).xs≤1 := by
    filter_upwards [hxunit] with n hn
    exact (hxs n).trans hn
  have Htarget : ∀ᶠn in atTop,comparisonConditionalScale
      (PW n).data.N delta (PW n).data.E (PW n).lam ≤ (PW n).xs := by
    simpa only [PW,ActualThetaZeroOverlapMinimum.weakenConstants,hPx] using htarget
  have Hweak : Tendsto (fun n=>laplaceComparisonStrength (PW n).data.d
      (PW n).lam (PW n).xs/(PW n).xs^2) atTop (𝓝 0) := by
    simpa only [PW,ActualThetaZeroOverlapMinimum.weakenConstants,hPx] using hweak
  have Homit : Tendsto (fun n=>(PW n).data.s/
      actualChildCutoff (dim n+1) delta c0 (PW n).data.d
        (PW n).lam (PW n).xs) atTop (𝓝 0) := by
    simpa only [PW,ActualThetaZeroOverlapMinimum.weakenConstants,hPx] using hs
  have Hxs : Tendsto (fun n=>(Q n).xs) atTop (𝓝 0) := by
    simpa only [hQxs] using hxlim
  have HG := H.exists_theta_zero_wall_comparable_context hm hdelta
    (show 0<cl/4 by positivity) (show 0≤4*C/cl by positivity)
    hC0 hc0 hc01 hTpos hmargin hcapmargin hgapmargin dim hdim
    PW Q Q hT Hsame Hunit Htarget Hweak Homit Hcut Hb Hh Hxs
  refine ⟨HG,?_,?_⟩
  · intro n
    have HQd : (Q n).context.d=c0*x n := by
      change (Q n).data.d=_
      rw [hdata n]
      exact hchildD n
    rw [hQxs n,HQd,hQlam n]
    have Hg := laplaceComparisonStrength_le (c0*x n)
      (sq_nonneg (c0*x n)) (x n)
    have Hd : c0*x n ≤ x n := by nlinarith [hx n]
    have Hsqrt : Real.sqrt (laplaceComparisonStrength (c0*x n)
        ((c0*x n)^2) (x n)) ≤ x n := by
      exact (Real.sqrt_le_left (hx n).le).mpr
        (Hg.trans (sq_le_sq₀ (mul_pos hc0 (hx n)).le
          (hx n).le |>.mpr Hd))
    exact max_eq_left Hsqrt
  · intro n
    have HQd : (Q n).context.d=c0*x n := by
      change (Q n).data.d=_
      rw [hdata n]
      exact hchildD n
    rw [hQxs n,HQd,hQlam n]
    exact (actual_child_direct_calibration_at_parent_test (delta:=delta)
      (d:=(P n).data.d) (lam:=(P n).lam)
      (by omega : 0<dim n+1) hc0 hc01 (P n).hlam (hx n)).2.2

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
