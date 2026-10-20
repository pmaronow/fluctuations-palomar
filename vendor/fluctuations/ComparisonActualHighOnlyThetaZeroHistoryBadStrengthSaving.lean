module

public import ComparisonActualHighOnlyWeakHistoryEndpointCost
public import ComparisonActualHighOnlyThetaZeroHistoryBranchCalls
public import ComparisonActualHighOnlyThetaZeroHistoryAllScaleFixed

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 28000000
set_option linter.unusedVariables false

namespace ActualHighOnlyOverlapMinimum

theorem exists_theta_zero_high_only_history_bad_test_strength_saving
    {beta : ℝ≥0} (hbeta : 0  <  beta) (hT : 1  <  (beta:ℝ)^2) :
    ∃lower upper : ℝ,0  <  lower ∧ 0  <  upper ∧
      ∀(m delta cl cu Az C0 Ct D Bclock c0 : ℝ),
        0  <  m → 0  <  delta → delta  <  3*m → 0  <  cl → 0  <  cu →
        0≤Az → 0  <  C0 → 0≤Ct → D≤1 → 0  <  c0 → c0≤1 →
        delta/4  <  3*m-99*delta →
        100*delta  <  (1:ℝ)/3+m → 0  <  9*m-298*delta →
        cl≤lower → upper≤cu →
        cl  <  (beta:ℝ)^2*Real.exp (-12*(beta:ℝ)^2) →
        (beta:ℝ)^2*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
          (2*Real.exp (-12*(beta:ℝ)^2))  <  cu →
        ∀dim : ℕ→ℕ,Tendsto dim atTop atTop →
        ∀P : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1)
          m delta cl cu Az C0 Ct D Bclock,
        ∀root M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
          m delta cl cu Az C0 Ct D Bclock,
        ActualWeakHighOnlyHistoryChain c0 root M →
        (∀ᶠn in atTop,(P n).data.T=(beta:ℝ)^2) →
        (∀ᶠn in atTop,(root n).data.s=(P n).data.s) →
        (∀ᶠn in atTop,(P n).xs≤1) →
        (∀ᶠn in atTop,comparisonConditionalScale (P n).data.N delta
          (P n).data.E (P n).lam≤(P n).xs) →
        Tendsto (fun n=>laplaceComparisonStrength (P n).data.d
          (P n).lam (P n).xs/(P n).xs^2) atTop (𝓝 0) →
        Tendsto (fun n=>(P n).data.s/
          actualChildCutoff (dim n+1) delta c0
            (P n).data.d (P n).lam (P n).xs) atTop (𝓝 0) →
        (∀ᶠn in atTop,actualChildCutoff (dim n+1) delta c0
          (P n).data.d (P n).lam (P n).xs≤
            comparisonLowerScale (root n).context.N
              (root n).context.E (root n).context.d) →
        (∀ᶠn in atTop,∀u,(root n).b u=(P n).changedBare u) →
        (∀ᶠn in atTop,∀u,(root n).h u=(P n).changedField u) →
        Tendsto (fun n=>(M n).data.s) atTop (𝓝 0) →
        Tendsto (fun n=>comparisonEndpointL1Cost ((beta:ℝ)^2)
          (root n).b (root n).h) atTop (𝓝 0) →
        (∀n,(M n).xs≤1) →
        (∀ᶠn in atTop,¬(cl*(M n).xs≤(M n).alpha.val.val (M n).xs ∧
          (M n).alpha.val.val (M n).xs≤cu*(M n).xs)) →
        Tendsto (fun n=>laplaceComparisonStrength (M n).context.d
          (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0) := by
  classical
  obtain ⟨lower,upper,hlower,hupper,Hmacro⟩:=
    exists_theta_zero_macro_bad_strength_reindex hbeta hT
  refine ⟨lower,upper,hlower,hupper,?_⟩
  intro m delta cl cu Az C0 Ct D Bclock c0 hm hdelta hroom hcl hcu hAz hC0 hCt
    hD hc0 hc01 hmargin hcapmargin hgapmargin hclMacro hcuMacro hclTemp hcuTemp
    dim hdim P root M H hTemp hsame hunitP htargetP hweakP hsratio hcut hb hh
    hs HrootCost hxsunit Hbad
  let T:ℝ:=(beta:ℝ)^2
  have hTpos : 0  <  T:=zero_lt_one.trans hT
  have Hcost : Tendsto (fun n=>comparisonEndpointL1Cost T
      (M n).b (M n).h) atTop (𝓝 0) :=
    H.endpoint_cost_tendsto_zero HrootCost
  have HmacroInstance (sigma : ℕ→ℕ) (hsigma : StrictMono sigma)
      (xlo : ℝ) (hxlo : 0 < xlo)
      (Hlo : ∀n,xlo≤(M (sigma n)).xs) :
      Tendsto (fun n=>laplaceComparisonStrength (M (sigma n)).context.d
        (M (sigma n)).lam (M (sigma n)).xs/(M (sigma n)).xs^2)
        atTop (𝓝 0) := by
    exact Hmacro m delta cl cu Az C0 Ct D Bclock
      hdelta hclMacro hcuMacro hD dim hdim M hxsunit hs Hcost
      Hbad sigma hsigma xlo hxlo Hlo
  exact theta_zero_high_only_history_bad_strength_of_macro_callback
    (T:=T) hm hdelta hroom hcl hcu hAz hC0 hCt hD hc0 hc01 hTpos
    hmargin hcapmargin hgapmargin hclTemp hcuTemp dim hdim P root M H
    hTemp hsame hunitP htargetP hweakP hsratio hcut hb hh Hbad
    HmacroInstance

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
