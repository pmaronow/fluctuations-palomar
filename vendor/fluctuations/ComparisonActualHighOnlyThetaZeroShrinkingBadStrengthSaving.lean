module

public import ComparisonActualHighWallThetaZeroHighOnlyHistoryContext
public import ComparisonActualHighOnlyCompleteComparableStrictTest

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 16000000

namespace ActualHighOnlyOverlapMinimum

theorem ActualWeakHighOnlyHistoryChain.theta_zero_shrinking_bad_test_strength_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0)
    (hCt : 0≤Ct) (hD : D≤1) (hc0 : 0 < c0) (hc01 : c0≤1)
    (hTpos : 0 < T)
    (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (hclTemp : cl < T*Real.exp (-12*T))
    (hcuTemp : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
      (2*Real.exp (-12*T)) < cu)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (P : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    {root M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock}
    (H : ActualWeakHighOnlyHistoryChain c0 root M)
    (hTemp : ∀ᶠn in atTop,(P n).data.T=T)
    (hsame : ∀ᶠn in atTop,(root n).data.s=(P n).data.s)
    (hunitP : ∀ᶠn in atTop,(P n).xs≤1)
    (htargetP : ∀ᶠn in atTop,comparisonConditionalScale (P n).data.N delta
      (P n).data.E (P n).lam≤(P n).xs)
    (hweakP : Tendsto (fun n=>laplaceComparisonStrength (P n).data.d
      (P n).lam (P n).xs/(P n).xs^2) atTop (𝓝 0))
    (hsratio : Tendsto (fun n=>(P n).data.s/
      actualChildCutoff (dim n+1) delta c0
        (P n).data.d (P n).lam (P n).xs) atTop (𝓝 0))
    (hcut : ∀ᶠn in atTop,actualChildCutoff (dim n+1) delta c0
      (P n).data.d (P n).lam (P n).xs≤
        comparisonLowerScale (root n).context.N
          (root n).context.E (root n).context.d)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=(P n).changedBare u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=(P n).changedField u)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (Hbad : ∀ᶠn in atTop,
      ¬(cl*(M n).xs≤(M n).alpha.val.val (M n).xs ∧
        (M n).alpha.val.val (M n).xs≤cu*(M n).xs)) :
    Tendsto (fun n=>laplaceComparisonStrength (M n).context.d
      (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0) := by
  obtain ⟨Gc⟩ := H.exists_theta_zero_wall_comparable_context
    hm hdelta hcl hAz hC0 hc0 hc01 hTpos hmargin hcapmargin hgapmargin
    dim hdim P root M hTemp hsame hunitP htargetP hweakP hsratio
    hcut hb hh hxs
  have HD : ∀ᶠn in atTop,(M n).context.d≤1 :=
    Eventually.of_forall fun n=>(M n).hdD.trans hD
  have HW := eventually_actual_comparable_context_working_scale_le_one_high_only
    M Gc HD
  exact actual_high_only_comparable_bad_test_strength_tendsto_zero
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim M Gc HW
    hclTemp hcuTemp Hbad

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
