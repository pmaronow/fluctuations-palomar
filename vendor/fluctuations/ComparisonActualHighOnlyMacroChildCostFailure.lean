module

public import ComparisonActualHighOnlyMacroscopicSuccessfulChildExclusion

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false

namespace ActualHighOnlyOverlapMinimum

theorem exists_macro_bad_parent_child_cost_failure_constants
    {beta : ℝ≥0} (hbeta : 0<beta) (hT : 1<(beta:ℝ)^2) :
    ∃lower upper : ℝ,0<lower ∧ 0<upper ∧
      ∀m delta cl cu Az C0 Ct D Bclock c0 : ℝ,
        0< m → 0<delta → 0<C0 →
        ∀hc0 : 0<c0,c0^2<(beta:ℝ)^2 →
        cl≤lower → upper≤cu →
        ∀dim : ℕ→ℕ, Tendsto dim atTop atTop →
        ∀M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1)
          m delta cl cu Az C0 Ct D Bclock,
        ∀xlo : ℝ,0<xlo →
        (∀n,(M n).xs∈Icc xlo 1) →
        Tendsto (fun n=>(M n).context.s) atTop (𝓝 0) →
        Tendsto (fun n=>laplaceComparisonStrength (M n).context.d
          (M n).lam (M n).xs/(M n).xs^2) atTop (𝓝 0) →
        (∀ᶠn in atTop,(M n).lam+(c0*(M n).xs)^2≤
          (M n).b (M n).context.s) →
        (∀ᶠn in atTop,∀u∈Ico (0:ℝ) (M n).context.s,
          (M n).b u+(M n).lam+(c0*(M n).xs)^2≤
            (M n).b (M n).context.s) →
        Tendsto (fun n=>comparisonEndpointL1Cost ((beta:ℝ)^2)
          (M n).b (M n).h) atTop (𝓝 0) →
        (∀ᶠn in atTop,
          ¬(cl*(M n).xs≤(M n).alpha.val.val (M n).xs ∧
            (M n).alpha.val.val (M n).xs≤cu*(M n).xs)) →
        ∀ᶠn in atTop,
          ((dim n+1:ℕ):ℝ)^(20*delta)*actualChildErrorBudget
            (dim n+1) delta c0 (M n).context.d (M n).lam (M n).xs <
              (M n).macroChildSweepCost hc0 := by
  classical
  obtain ⟨lower,upper,hlower,hupper,Hmacro⟩ :=
    macro_successful_child_literal_bad_witness_excluded_high_only
      hbeta hT
  refine ⟨lower,upper,hlower,hupper,?_⟩
  intro m delta cl cu Az C0 Ct D Bclock c0 hm hdelta hC0
    hc0 hc0T hcl hcu dim hdim M xlo hxlo hxs hs hweak
    hroom hcross hcost Hbad
  by_contra Hfailure
  have Hfreq : ∃ᶠn in atTop,
      (M n).macroChildSweepCost hc0 ≤
        ((dim n+1:ℕ):ℝ)^(20*delta)*actualChildErrorBudget
          (dim n+1) delta c0 (M n).context.d (M n).lam (M n).xs := by
    simpa only [Filter.Frequently,not_le] using Hfailure
  obtain ⟨phi,hphi,Hphi⟩ := extraction_of_frequently_atTop Hfreq
  have Hgood := Hmacro m delta cl cu Az C0 Ct D Bclock c0
    hm hdelta hC0 hc0 hc0T hcl hcu
    (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n=>M (phi n)) xlo hxlo (fun n=>hxs (phi n))
    (hs.comp hphi.tendsto_atTop) (hweak.comp hphi.tendsto_atTop)
    (hphi.tendsto_atTop.eventually hroom)
    (hphi.tendsto_atTop.eventually hcross)
    (hcost.comp hphi.tendsto_atTop)
    (Eventually.of_forall Hphi)
  obtain ⟨n,hn⟩ := (Hgood.and
    (hphi.tendsto_atTop.eventually Hbad)).exists
  exact hn.2 hn.1

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
