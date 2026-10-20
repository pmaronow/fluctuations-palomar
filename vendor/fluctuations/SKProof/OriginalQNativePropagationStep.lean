module

public import SKProof.OriginalQNativeHistoryChildFailure
public import SKProof.OriginalQNativeChildPullback
public import ComparisonNativeActualSelectedBadChild

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal

namespace NativeOverlapMinimum

theorem exists_irregular_child_step_original_q
    {beta : ℝ≥0} (hbeta : 0 < beta)
    (hTemp : 1 < (beta:ℝ)^2) :
    ∃lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀m delta cl cu Az C0 Ct D c0 : ℝ,
      ∀_hm : 0 < m, ∀_hdelta : 0 < delta,
      delta < 3*m → 0 < cl → 0 < cu → 2 ≤ Az →
      0 < C0 → 1 ≤ Ct → D ≤ 1 →
      ∀_hc0 : 0 < c0, c0 ≤ 1 → c0 ≤ D →
      delta/4 < 3*m-99*delta →
      100*delta < (1:ℝ)/3+m →
      0 < 9*m-298*delta →
      cl ≤ lower → upper ≤ cu →
      cl < (beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
      (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
        (2*Real.exp (-12*(beta:ℝ)^2)) < cu →
      ∀dim : ℕ → ℕ, ∀_hdim : Tendsto dim atTop atTop,
      ∀M : (n : ℕ) → NativeOverlapMinimum (dim n+1)
        m delta cl cu Az C0 Ct D ((beta:ℝ)^2),
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
        ∃Q : NativeOverlapMinimum (dim n+1)
          m delta cl cu Az C0 Ct D ((beta:ℝ)^2),
          Q.context.d = c0*(M n).xs ∧
          Q.context.E = actualChildErrorBudget (dim n+1) delta c0
            (M n).context.d (M n).lam (M n).xs ∧
          (M n).context.N^(delta/4)*(M n).context.E ≤ Q.context.E ∧
          Q.xs ∈ Icc
            (comparisonConditionalScale Q.context.N delta Q.context.E Q.lam) 1 ∧
          Q.z = min (2*Q.xs) 1 ∧
          ¬(cl*Q.xs ≤ Q.alpha.val.val Q.xs ∧
            Q.alpha.val.val Q.xs ≤ cu*Q.xs) ∧
          (∀u, Q.b u = (M n).b u-
            laplaceComparisonStrength (M n).context.d (M n).lam
              ((M n).R u)) ∧
          (∀u, Q.h u = (M n).h u+
            laplaceComparisonStrength (M n).context.d (M n).lam
              ((M n).R u)*(M n).R u) := by
  classical
  obtain ⟨lower,upper,hlower,hupper,Hfailure⟩ :=
    exists_native_child_pressure_failure_original_q hbeta hTemp
  refine ⟨lower,upper,hlower,hupper,?_⟩
  intro m delta cl cu Az C0 Ct D c0 hm hdelta hroom hcl hcu
    hAz hC0 hCt hD hc0 hc01 hc0D hmargin hcapmargin
    hgapmargin hclMacro hcuMacro hclTemp hcuTemp
    dim hdim M G hxsunit htarget hroomChild hbad
  let T : ℝ := (beta:ℝ)^2
  have hAz0 : 0 ≤ Az := (by norm_num : (0:ℝ) ≤ 2).trans hAz
  have hCt0 : 0 ≤ Ct := zero_le_one.trans hCt
  obtain ⟨hweak,hfail⟩ := Hfailure m delta cl cu Az C0 Ct D T c0
    hm hdelta hroom hcl hcu hAz0 hC0 hCt0 hD
    hc0 hc01 hmargin hcapmargin hgapmargin
    hclMacro hcuMacro hclTemp hcuTemp
    dim hdim M G hxsunit htarget hroomChild hbad
  have hcl1 : cl ≤ 1 := by
    simpa only [mul_one,(M 0).alpha.property.2] using
      ((M 0).regular 1 ⟨(M 0).hz.2,le_rfl⟩).1
  have hcu1 : 1 ≤ cu := by
    simpa only [mul_one,(M 0).alpha.property.2] using
      ((M 0).regular 1 ⟨(M 0).hz.2,le_rfl⟩).2
  have htotal := G.total_root_original_q
  have hclock := G.child_pullback_original_q hc0
  have hweak1 := hweak.eventually (eventually_le_nhds zero_lt_one)
  have hselect := hdim.eventually
    (eventually_exists_actual_selected_bad_regular_child_from_target
      (D:=D) (T:=T) hm hdelta hroom hcl hcl1 hcu1
      hAz hCt hC0 hc0 hmargin)
  refine ⟨hweak,?_⟩
  filter_upwards [hfail,htotal,hclock,hweak1,hselect,htarget,hroomChild]
    with n hnFail hnTotal hnClock hnWeak hnSelect hnTarget hnRoom
  have hnD : c0*(M n).xs ≤ D := by
    have h := mul_le_mul_of_nonneg_left (hxsunit n) hc0.le
    simpa only [mul_one] using h.trans
      (by simpa only [mul_one] using hc0D)
  have hn1 : c0*(M n).xs ≤ 1 := hnD.trans hD
  have heweak :
      laplaceComparisonStrength (M n).context.d (M n).lam
        (M n).xs ≤ (M n).xs^2 :=
    (div_le_one₀ (sq_pos_of_pos (M n).hxs)).mp hnWeak
  obtain ⟨lam,hlam,alpha,hattained,Q,hcontext,hQlam,hAlpha,
    hbQ,hhQ,hRQ,hdQ,hEQ,hGrow,hXs,hZ,hBad⟩ :=
    hnSelect (M n) (M n).xs (M n).hxs
      hn1 hnD hnTarget heweak hnRoom hnTotal.1
      (hnClock _ (M n).hxs) hnFail
  refine ⟨Q,hdQ,hEQ,hGrow,?_,hZ,?_,?_,?_⟩
  · rw [hcontext,hQlam]
    exact hXs
  · rcases hBad with hlo|hhi
    · exact fun h => not_lt_of_ge h.1 hlo
    · exact fun h => not_lt_of_ge h.2 hhi
  · exact fun u => congrFun hbQ u
  · exact fun u => congrFun hhQ u

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
