module

public import ComparisonActualHighOnlyThetaZeroShrinkingBadStrengthSaving
public import ComparisonActualHighOnlyHistoryReindex
public import ComparisonActualHighOnlyMacroscopicBadStrengthSaving
public import ComparisonActualHighOnlyWeakHistoryEndpointCost

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 28000000

namespace ActualHighOnlyOverlapMinimum

theorem theta_zero_shrinking_bad_strength_reindex
    {m delta cl cu Az C0 Ct D Bclock c0 T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hCt : 0 ≤ Ct) (hD : D ≤ 1) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hTpos : 0 < T)
    (hmargin : delta/4 < 3*m-99*delta)
    (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (hclTemp : cl < T*Real.exp (-12*T))
    (hcuTemp : T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/
      (2*Real.exp (-12*T)) < cu)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (P : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (root M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (H : ActualWeakHighOnlyHistoryChain c0 root M)
    (hTemp : ∀ᶠn in atTop, (P n).data.T=T)
    (hsame : ∀ᶠn in atTop, (root n).data.s=(P n).data.s)
    (hunitP : ∀ᶠn in atTop, (P n).xs≤1)
    (htargetP : ∀ᶠn in atTop, comparisonConditionalScale (P n).data.N delta
      (P n).data.E (P n).lam≤(P n).xs)
    (hweakP : Tendsto (fun n => laplaceComparisonStrength (P n).data.d
      (P n).lam (P n).xs/(P n).xs^2) atTop (𝓝 0))
    (hsratio : Tendsto (fun n => (P n).data.s/
      actualChildCutoff (dim n+1) delta c0
        (P n).data.d (P n).lam (P n).xs) atTop (𝓝 0))
    (hcut : ∀ᶠn in atTop, actualChildCutoff (dim n+1) delta c0
      (P n).data.d (P n).lam (P n).xs≤
        comparisonLowerScale (root n).context.N
          (root n).context.E (root n).context.d)
    (hb : ∀ᶠn in atTop, ∀u, (root n).b u=(P n).changedBare u)
    (hh : ∀ᶠn in atTop, ∀u, (root n).h u=(P n).changedField u)
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (HX : Tendsto (fun n => (M (phi n)).xs) atTop (𝓝 0))
    (Hbad : ∀ᶠn in atTop,
      ¬(cl*(M n).xs≤(M n).alpha.val.val (M n).xs ∧
        (M n).alpha.val.val (M n).xs≤cu*(M n).xs)) :
    Tendsto (fun n => laplaceComparisonStrength (M (phi n)).context.d
      (M (phi n)).lam (M (phi n)).xs/(M (phi n)).xs^2) atTop (𝓝 0) := by
  let dim' : ℕ → ℕ := fun n => dim (phi n)
  let P' : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim' n+1)
      m delta cl cu Az C0 Ct D Bclock := fun n => P (phi n)
  let root' : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim' n+1)
      m delta cl cu Az C0 Ct D Bclock := fun n => root (phi n)
  let M' : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim' n+1)
      m delta cl cu Az C0 Ct D Bclock := fun n => M (phi n)
  have H' : ActualWeakHighOnlyHistoryChain c0 root' M' :=
    H.comp phi hphi.tendsto_atTop
  have Hresult := H'.theta_zero_shrinking_bad_test_strength_tendsto_zero
    hm hdelta hroom hcl hcu hAz hC0 hCt hD hc0 hc01 hTpos
    hmargin hcapmargin hgapmargin hclTemp hcuTemp
    dim' (hdim.comp hphi.tendsto_atTop) P'
    (hphi.tendsto_atTop.eventually hTemp)
    (hphi.tendsto_atTop.eventually hsame)
    (hphi.tendsto_atTop.eventually hunitP)
    (hphi.tendsto_atTop.eventually htargetP)
    (hweakP.comp hphi.tendsto_atTop)
    (hsratio.comp hphi.tendsto_atTop)
    (hphi.tendsto_atTop.eventually hcut)
    (hphi.tendsto_atTop.eventually hb)
    (hphi.tendsto_atTop.eventually hh) HX
    (hphi.tendsto_atTop.eventually Hbad)
  exact Hresult

theorem exists_theta_zero_macro_bad_strength_reindex
    {beta : ℝ≥0} (hbeta : 0 < beta) (hT : 1 < (beta:ℝ)^2) :
    ∃lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀(m delta cl cu Az C0 Ct D Bclock : ℝ),
        0 < delta → cl ≤ lower → upper ≤ cu → D ≤ 1 →
        ∀dim : ℕ → ℕ, Tendsto dim atTop atTop →
        ∀M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1)
          m delta cl cu Az C0 Ct D Bclock,
        (∀n, (M n).xs ≤ 1) →
        Tendsto (fun n => (M n).data.s) atTop (𝓝 0) →
        Tendsto (fun n => comparisonEndpointL1Cost ((beta:ℝ)^2)
          (M n).b (M n).h) atTop (𝓝 0) →
        (∀ᶠn in atTop,
          ¬(cl*(M n).xs≤(M n).alpha.val.val (M n).xs ∧
            (M n).alpha.val.val (M n).xs≤cu*(M n).xs)) →
        ∀sigma : ℕ → ℕ, StrictMono sigma →
        ∀xlo : ℝ, 0 < xlo → (∀n, xlo ≤ (M (sigma n)).xs) →
        Tendsto (fun n => laplaceComparisonStrength
          (M (sigma n)).context.d (M (sigma n)).lam
          (M (sigma n)).xs/(M (sigma n)).xs^2) atTop (𝓝 0) := by
  classical
  obtain ⟨lower, upper, hlower, hupper, Hmacro⟩ :=
    high_only_macro_bad_test_strength_tendsto_zero hbeta hT
  refine ⟨lower, upper, hlower, hupper, ?_⟩
  intro m delta cl cu Az C0 Ct D Bclock hdelta hclMacro hcuMacro hD
    dim hdim M hxsunit hs Hcost Hbad sigma hsigma xlo hxlo Hlo
  let T : ℝ := (beta:ℝ)^2
  let dim' : ℕ → ℕ := fun n => dim (sigma n)+1
  let M' : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim' n)
    m delta cl cu Az C0 Ct D Bclock := fun n => M (sigma n)
  have Hdim : Tendsto dim' atTop atTop :=
    (tendsto_add_atTop_nat 1).comp (hdim.comp hsigma.tendsto_atTop)
  have Hgap (n : ℕ) : (M' n).context.d^2 ≤ T-(T-1) := by
    have HH := pow_le_pow_left₀ (M' n).context.hd.le
      ((M' n).hdD.trans hD) 2
    norm_num only [one_pow] at HH
    linarith only [HH]
  have Hxs (n : ℕ) : (M' n).xs ∈ Icc xlo 1 :=
    ⟨Hlo n, hxsunit (sigma n)⟩
  have Hs : Tendsto (fun n => (M' n).context.s) atTop (𝓝 0) :=
    hs.comp hsigma.tendsto_atTop
  have Hc : Tendsto (fun n => comparisonEndpointL1Cost T
      (M' n).b (M' n).h) atTop (𝓝 0) :=
    Hcost.comp hsigma.tendsto_atTop
  have Hb : ∀ᶠn in atTop,
      ¬(cl*(M' n).xs≤(M' n).alpha.val.val (M' n).xs ∧
        (M' n).alpha.val.val (M' n).xs≤cu*(M' n).xs) :=
    hsigma.tendsto_atTop.eventually Hbad
  have Hresult := Hmacro m delta cl cu Az C0 Ct D Bclock
    hdelta hclMacro hcuMacro dim' Hdim M' xlo (T-1)
    hxlo (by dsimp only [T]; linarith) Hxs Hgap Hs Hc Hb
  exact Hresult

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
