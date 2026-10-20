module

public import ComparisonActualHighWallThetaZeroMacroscopicEndpoint
public import ComparisonActualHighWallOriginsAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 18000000

namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock:ℝ}

theorem theta_zero_all_mass_room_of_small_epsilon_fixed_beta
    {n:ℕ} {T c0:ℝ}
    (M:ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (hc0:0<c0) (hc0T:c0^2<T/4)
    (hT:M.data.T=T) (hxs:M.xs≤1) (heps:M.data.epsilon≤T/4):
    (c0*M.xs)^2≤M.changedBare 0:=by
  have Hmatrix:=M.data.theta_zero_changed_low_matrix M.lam M.hlam M.hld
    M.alpha M.data.hs.1
  change M.changedBare 0=M.data.T-M.data.epsilon at Hmatrix
  have H0:0≤c0*M.xs:=mul_nonneg hc0.le M.hxs.le
  have Hx:c0*M.xs≤c0:=by simpa using mul_le_mul_of_nonneg_left hxs hc0.le
  have Hsq:=pow_le_pow_left₀ H0 Hx 2
  rw [Hmatrix,hT]
  linarith only [Hsq,hc0T,heps,sq_nonneg c0]

theorem theta_zero_rmin_tendsto_zero
    (hdelta:0<delta) (N:ℕ→ℕ) (hN:Tendsto N atTop atTop)
    (M:(j:ℕ)→ActualThetaZeroOverlapMinimum (N j+1) m delta cl cu Az C0 Ct D Bclock):
    Tendsto (fun j=>(M j).data.rmin) atTop (𝓝 0):=by
  have hNplus:Tendsto (fun j=>N j+1) atTop atTop:=(tendsto_add_atTop_nat 1).comp hN
  have Hlim:=(((tendsto_rpow_neg_atTop hdelta).comp tendsto_natCast_atTop_atTop).comp hNplus).div_const 2
  apply squeeze_zero (fun j=>(M j).data.hrbounds.1.le) _ (by simpa only [zero_div] using Hlim)
  intro j
  have H:=(M j).data.rmin_over_test_le_high_floor (x:=1) (M j).data.hd1
  simpa only [div_one,ActualHighWallData.N,Function.comp_apply] using H

theorem theta_zero_macro_weak_low_gap_bad_forces_sharp_all_mass_failure
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
      (∀ᶠj in atTop,(M j).data.epsilon≤(beta:ℝ)^2/4) →
      (∀j,(M j).alpha.val.val (M j).xs<cl*(M j).xs ∨
        cu*(M j).xs<(M j).alpha.val.val (M j).xs) →
      ∀ᶠj in atTop,
        ((N j+1:ℕ):ℝ)^(20*delta)*
          actualChildErrorBudget (N j+1) delta c0 (M j).data.d (M j).lam (M j).xs <
            (M j).allMassChildSweepCost hc0:=by
  obtain ⟨lower,upper,hlower,hupper,Hexcl⟩:=
    theta_zero_macro_all_mass_successful_child_literal_bad_witness_excluded hbeta hT
  refine ⟨lower,upper,hlower,hupper,?_⟩
  intro m delta cl cu Az C0 Ct D Bclock c0 hm hdelta hC0 hc0 hc0T hclmargin hcumargin
    N hN M xlo hxlo hxs hTfix hs hweak heps hbad
  have hc0T':c0^2<(beta:ℝ)^2:=by
    nlinarith only [hc0T,hT]
  have hroom:∀ᶠj in atTop,(c0*(M j).xs)^2≤(M j).changedBare 0:=by
    filter_upwards [heps] with j he
    exact (M j).theta_zero_all_mass_room_of_small_epsilon_fixed_beta
      hc0 hc0T (hTfix j) (hxs j).2 he
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
    (hindexlim.eventually hroom) (Hcost.comp hindexlim)
    (Eventually.of_forall fun j=>by simpa only [Function.comp_apply] using hsuccess j)
  obtain ⟨j,hj⟩:=Hreg.exists
  rcases hbad (index j) with hlow|hhigh
  · exact (not_lt_of_ge hj.1) hlow
  · exact (not_lt_of_ge hj.2) hhigh

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
