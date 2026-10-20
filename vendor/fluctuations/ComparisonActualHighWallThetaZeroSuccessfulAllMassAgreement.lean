module

public import ComparisonActualHighWallThetaZeroFirstHighOnlyChild
public import ComparisonActualShiftedAllMassMacroscopicChildAgreement

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option linter.unusedVariables false

theorem theta_zero_successful_all_mass_fixed_mass_agreement
    {m delta cl cu Az C0 Ct D Bclock c0 xlo:ℝ}
    (hm:0 < m) (hdelta:0 < delta) (hC0:0 < C0) (hc0:0 < c0) (hxlo:0 < xlo)
    (dim:ℕ→ℕ) (hdim:Tendsto dim atTop atTop)
    (M:(j:ℕ)→ActualThetaZeroOverlapMinimum (dim j+1) m delta cl cu Az C0 Ct D Bclock)
    (a:(j:ℕ)→ActualShiftedAllMassParentChildCall (dim j+1) delta)
    (hx:∀j,(M j).xs∈Icc xlo 1)
    (hcontext:∀j,(a j).context=(M j).data.thetaZeroShiftedParentData
      (M j).lam (M j).hlam (M j).hld)
    (hR:∀j,(a j).R=(M j).data.wallRadius (M j).alpha)
    (hchild:∀ᶠj in atTop,(a j).childRadius=c0*(M j).xs ∧
      (a j).childLam=(c0*(M j).xs)^2 ∧
      (a j).err≤ ((dim j+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim j+1) delta c0 (M j).data.d (M j).lam (M j).xs)
    (hs:Tendsto (fun j=>(M j).data.s) atTop (𝓝 0))
    (hr:Tendsto (fun j=>(M j).data.rmin) atTop (𝓝 0))
    (hweak:Tendsto (fun j=>laplaceComparisonStrength (M j).data.d (M j).lam (M j).xs/
      (M j).xs^2) atTop (𝓝 0)) :
    ∀left right eps width:ℝ,0 < left → left < right → right ≤ 1 → 0 < eps → 0 < width →
      ∀ᶠj in atTop,
        volume (physicalPropagationDisagreementMassSet
          ((M j).data.wallRadius (M j).alpha) (a j).Z left right eps) < ENNReal.ofReal width := by
  have hN:Tendsto (fun j=>dim j+1) atTop atTop:=(tendsto_add_atTop_nat 1).comp hdim
  have hnum:∀j,(a j).context.d≤ D ∧
      Real.sqrt ((dim j+1:ℕ):ℝ)*(a j).context.E≤ (a j).context.d^2 ∧
      ((dim j+1:ℕ):ℝ)^(-(2:ℝ)/3+m)*(a j).context.d≤ C0*(a j).context.E ∧
      comparisonLowerScale ((dim j+1:ℕ):ℝ) (a j).context.E (a j).context.d≤ (M j).xs:=by
    intro j
    rw [hcontext j]
    exact ⟨(M j).hdD,(M j).hupper,(M j).hlower,(M j).hscale⟩
  have hsA:Tendsto (fun j=>(a j).context.s) atTop (𝓝 0):=by
    simpa only [hcontext,ActualHighWallData.thetaZeroShiftedParentData] using hs
  have hrA:Tendsto (fun j=>(a j).context.r0) atTop (𝓝 0):=by
    simpa only [hcontext,ActualHighWallData.thetaZeroShiftedParentData] using hr
  have hweakA:Tendsto (fun j=>(a j).e ((M j).xs)/(M j).xs^2) atTop (𝓝 0):=by
    simpa only [ActualShiftedAllMassParentChildCall.e,hcontext,
      ActualShiftedAllMassParentChildCall.lam,
      ActualHighWallData.thetaZeroShiftedParentData,ActualShiftedParentData.d]
      using hweak
  have hchildA:∀ᶠj in atTop,(a j).childRadius=c0*(M j).xs ∧
      (a j).childLam=(c0*(M j).xs)^2 ∧
      (a j).err≤ ((dim j+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (dim j+1) delta c0 (a j).context.d (a j).lam (M j).xs:=by
    filter_upwards [hchild] with j hj
    have hlamj:(a j).lam=(M j).lam:=by
      change (a j).context.lam=(M j).lam
      rw [hcontext j]
      rfl
    rw [hlamj]
    rw [hcontext j]
    exact hj
  intro left right eps width hleft hlr hright heps hwidth
  have H:=actual_shifted_allmass_successful_child_fixed_mass_agreement hm hdelta hC0 hc0 hxlo
    (fun j=>dim j+1) hN a (fun j=>(M j).xs) hx hnum hchildA hsA hrA hweakA
    left right eps width hleft hlr hright heps hwidth
  simpa only [hR] using H

end OAI.SKFluctuations.LaplaceWindowFormalization
