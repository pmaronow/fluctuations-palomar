module

public import SKProof.Restore.ComparisonActualHighWallThetaZeroMacroWeakHighGapNumerics
public import SKProof.Restore.ComparisonActualHighWallThetaZeroMacroWeakLowGapFailure

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 18000000

namespace ActualThetaZeroOverlapMinimum

theorem theta_zero_macro_weak_high_gap_bad_forces_sharp_high_only_failure
    {beta:ℝ≥0} (hbeta:0<beta) (hT:1<(beta:ℝ)^2):
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ m delta cl cu Az C0 Ct D Bclock c0 : ℝ,
      0 < m → 0 < delta → 0 < C0 →
      ∀ hc0 : 0 < c0, c0^2 < (beta:ℝ)^2/4 → cl ≤ lower → upper ≤ cu →
      ∀N:ℕ→ℕ,Tendsto N atTop atTop →
      ∀M:(j:ℕ)→ActualThetaZeroOverlapMinimum (N j+1) m delta cl cu Az C0 Ct D Bclock,
      ∀xlo:ℝ,0<xlo → (∀j,(M j).xs∈Icc xlo 1) →
      (∀j,(M j).data.T=(beta:ℝ)^2) →
      Tendsto (fun j=>(M j).data.s) atTop (𝓝 0) →
      Tendsto (fun j=>laplaceComparisonStrength (M j).data.d (M j).lam (M j).xs/(M j).xs^2)
        atTop (𝓝 0) →
      (hgap:∀j,∀u∈Ico (0:ℝ) (M j).data.s,
        (M j).changedBare u+(c0*(M j).xs)^2≤(M j).changedBare (M j).data.s) →
      (∀j,(M j).alpha.val.val (M j).xs<cl*(M j).xs ∨
        cu*(M j).xs<(M j).alpha.val.val (M j).xs) →
      ∀ᶠj in atTop,
        ((N j+1:ℕ):ℝ)^(20*delta)*
          actualChildErrorBudget (N j+1) delta c0 (M j).data.d (M j).lam (M j).xs <
            (M j).highOnlyChildSweepCost hc0 (hgap j):=by
  obtain ⟨lower,upper,hlower,hupper,Hexcl⟩:=
    theta_zero_macro_high_only_successful_child_literal_bad_witness_excluded hbeta hT
  refine ⟨lower,upper,hlower,hupper,?_⟩
  intro m delta cl cu Az C0 Ct D Bclock c0 hm hdelta hC0 hc0 hc0T hclmargin hcumargin
    N hN M xlo hxlo hxs hTfix hs hweak hgap hbad
  have hc0T':c0^2<(beta:ℝ)^2:=by
    nlinarith only [hc0T,hT]
  have Hcost:=theta_zero_changed_endpoint_cost_tendsto_zero_of_weak_bounded_call
    M (Eventually.of_forall fun j=>(hxs j).2) hTfix hs hweak
  have Hr:=theta_zero_rmin_tendsto_zero hdelta N hN M
  by_contra Hfail
  rw [eventually_atTop] at Hfail
  push Not at Hfail
  choose index hindex hsuccess using Hfail
  have hindexlim:Tendsto index atTop atTop:=tendsto_atTop_mono hindex tendsto_id
  have Hreg:=Hexcl m delta cl cu Az C0 Ct D Bclock c0 hm hdelta hC0 hc0 hc0T'
    hclmargin hcumargin (N ∘ index) (hN.comp hindexlim) (fun j=>M (index j))
    xlo hxlo (fun j=>hxs (index j))
    (hs.comp hindexlim) (hweak.comp hindexlim) (Hr.comp hindexlim)
    (fun j=>hgap (index j)) (Hcost.comp hindexlim)
    (Eventually.of_forall fun j=>by simpa only [Function.comp_apply] using hsuccess j)
  obtain ⟨j,hj⟩:=Hreg.exists
  rcases hbad (index j) with hlow|hhigh
  · exact (not_lt_of_ge hj.1) hlow
  · exact (not_lt_of_ge hj.2) hhigh

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
