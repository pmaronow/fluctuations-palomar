module

public import ComparisonActualHighWallMacroscopicAllMassChildExclusion
public import ComparisonActualHighWallMacroscopicEndpoint
public import ComparisonActualHighWallFixedCovarianceMargins

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000
namespace ActualHighWallOverlapMinimum

theorem macro_low_gap_successful_child_literal_bad_witness_excluded
    {beta:ℝ≥0} (hbeta:0 < beta) (hT:1 < (beta:ℝ)^2):
    ∃lower upper:ℝ,0 < lower ∧ 0 < upper ∧
      ∀m delta cl cu Az C0 Ct D Bclock c0:ℝ,
      0 < m → 0 < delta → 0 < C0 →
      ∀hc0:0 < c0,c0^2 < (beta:ℝ)^2/4 → cl ≤ lower → upper ≤ cu →
      ∀N:ℕ→ℕ,Tendsto N atTop atTop →
      ∀M:(n:ℕ)→ActualHighWallOverlapMinimum (N n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀xlo:ℝ,0 < xlo → (∀n,(M n).xs∈Icc xlo 1) →
      (∀n,(M n).data.T=(beta:ℝ)^2) →
      Tendsto (fun n=>(M n).data.s) atTop (𝓝 0) →
      Tendsto (fun n=>(M n).data.g ((M n).xs)/(M n).xs^2) atTop (𝓝 0) →
      (∀ᶠn in atTop,(M n).data.epsilon ≤ (beta:ℝ)^2/4) →
      (∀ᶠn in atTop,(M n).macroAllMassChildSweepCost hc0 ≤ ((N n+1:ℕ):ℝ)^(20*delta)*
        actualChildErrorBudget (N n+1) delta c0 (M n).data.d ((M n).data.d^2) ((M n).xs)) →
      ∀ᶠn in atTop,cl*(M n).xs ≤ (M n).alpha.val.val (M n).xs ∧
        (M n).alpha.val.val (M n).xs ≤ cu*(M n).xs:=by
  obtain ⟨lower,upper,hlower,hupper,Hglobal⟩:=macro_all_mass_successful_child_literal_bad_witness_excluded_high_wall hbeta hT
  refine ⟨lower,upper,hlower,hupper,?_⟩
  intro m delta cl cu Az C0 Ct D Bclock c0 hm hdelta hC0 hc0 hc0T hclmargin hcumargin
    N hN M xlo hxlo hxs hTfix hs hweak hepsilon hsuccess
  have hunit:∀ᶠn in atTop,(M n).xs ≤ 1:=Eventually.of_forall fun n=>(hxs n).2
  have Hend:=changed_endpoint_and_radius_origin_zero_of_weak_bounded_test M hunit hTfix hs hweak
  have Hroom:∀ᶠn in atTop,(c0*(M n).xs)^2 ≤ (M n).data.b (M n).alpha 0:=by
    filter_upwards [hepsilon] with n he
    have HC:5*(beta:ℝ)^2/8 ≤ (M n).data.b (M n).alpha 0:=by
      have H:=(M n).data.changed_low_matrix_lower_of_small_epsilon (M n).alpha
        (by simpa only [hTfix n] using he) (M n).data.hs.1
      simpa only [hTfix n] using H
    have Hx:0 ≤ c0*(M n).xs:=mul_nonneg hc0.le (M n).hxs.le
    have Hc:c0*(M n).xs ≤ c0:=by simpa using mul_le_mul_of_nonneg_left (hxs n).2 hc0.le
    have Hsq:=pow_le_pow_left₀ Hx Hc 2
    linarith
  exact Hglobal m delta cl cu Az C0 Ct D Bclock c0 hm hdelta hC0 hc0
    (by linarith) hclmargin hcumargin N hN M xlo hxlo hxs hs hweak Hend.1 Hroom Hend.2 hsuccess

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
