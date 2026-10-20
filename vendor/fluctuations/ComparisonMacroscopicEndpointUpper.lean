module

public import ComparisonPerturbedEndpointBand

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Function
open scoped Topology NNReal

theorem macroEndpointObjective_le_scalar_plus_cost
    {β : ℝ≥0} (hβ : 0 < β) {c : ℝ} {k M : ℝ → ℝ} (hc : 0 < c)
    (hk : ContinuousOn k (Icc (0:ℝ) 1)) (hkc : ∀ r ∈ Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (n : ℕ) (hn : 0 < n) {d lam : ℝ} (hd : d ≠ 0) (hlam : 0 ≤ lam)
    (hlT : lam ≤ (β:ℝ)^2) (b h : ℝ → ℝ)
    (α : inverseIntegralConstraints 0 0 k M)
    (ha : comparisonClockAdmissible b h
      (fun u => laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u))
      (comparisonSweepQuantile hc hk hkc hm hM α)) :
    comparisonVariableEndpointObjective hc hk hkc hm hM n b h d lam α ≤
      scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α.val+
        comparisonEndpointL1Cost ((β:ℝ)^2) b h := by
  let R := comparisonSweepRadiusProfile hc hk hkc hm hM α
  have hp := actualComparison_endpoint_cost n hn hd hlam hlT b h R ha
  have hu := (comparisonSweepObjective_bounds hβ hc hk hkc hm hM n hn hd hlam hlT α).2
  rw [← comparisonVariableEndpointObjective_constant] at hu
  change pathCompensatedPressure n (fun _ => (β:ℝ)^2) (fun _ => 0)
    (fun u => laplaceComparisonStrength d lam (R.val u)) R.val 0 ≤ _ at hu
  have hh := le_abs_self (pathCompensatedPressure n b h
      (fun u => laplaceComparisonStrength d lam (R.val u)) R.val 0-
    pathCompensatedPressure n (fun _ => (β:ℝ)^2) (fun _ => 0)
      (fun u => laplaceComparisonStrength d lam (R.val u)) R.val 0)
  change pathCompensatedPressure n b h
    (fun u => laplaceComparisonStrength d lam (R.val u)) R.val 0 ≤ _
  linarith

theorem eventually_macroEndpoint_minimum_upper_reference
    {β : ℝ≥0} (hβ : 0 < β) {δ epsilon : ℝ} (hδ : 0 < δ) (heps : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop, ∀ (hn : 0 < n) (U L E d lam : ℝ) (hU : 0 < U) (hL : 0 < L)
      (hLU : L ≤ U) (hE : 0 < E) (hd : 0 < d) (hlam : 0 ≤ lam) (hlT : lam ≤ (β:ℝ)^2)
      (b h : ℝ → ℝ),
      let k := comparisonFloor (n:ℝ) δ U
      let M := comparisonCap (n:ℝ) δ U L E d
      let hc := comparisonFloor_pos (by positivity : 0 < (n:ℝ)) hU (by norm_num : (0:ℝ) ≤ 1)
      let hk := comparisonFloor_continuousOn (by positivity : 0 < (n:ℝ)) hU (r₀ := 0) le_rfl
      let hkc := fun r (hr : r ∈ Icc (0:ℝ) 1) =>
        comparisonFloor_lower_on (by positivity : 0 < (n:ℝ)) hU le_rfl hr
      let hm := comparisonCap_monotoneOn (by positivity : 0 < (n:ℝ)) hU.le hL hE hd.le
      let hM := comparisonCap_nonneg (by positivity : 0 < (n:ℝ)) hU.le hL hE hd.le zero_le_one
      (∀ γ : inverseIntegralConstraints 0 0 k M,
        comparisonClockAdmissible b h
          (fun u => laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM γ u))
          (comparisonSweepQuantile hc hk hkc hm hM γ)) →
      ∀ α : inverseIntegralConstraints 0 0 k M,
        (∀ γ : inverseIntegralConstraints 0 0 k M,
          comparisonVariableEndpointObjective hc hk hkc hm hM n b h d lam α ≤
            comparisonVariableEndpointObjective hc hk hkc hm hM n b h d lam γ) →
        comparisonVariableEndpointObjective hc hk hkc hm hM n b h d lam α ≤
          normalizedScalarParisiReference β+epsilon+comparisonEndpointL1Cost ((β:ℝ)^2) b h := by
  filter_upwards [eventually_comparison_scalar_reference_competitor hβ hδ heps] with n htrial
  intro hn U L E d lam hU hL hLU hE hd hlam hlT b h
  dsimp only
  intro hadmissible α hmin
  obtain ⟨γ,hγ⟩ := htrial U L E d hU hL hLU hE hd.le
  have hupper := macroEndpointObjective_le_scalar_plus_cost hβ
    (comparisonFloor_pos (δ := δ) (by positivity : 0 < (n:ℝ)) hU (by norm_num : (0:ℝ) ≤ 1))
    (comparisonFloor_continuousOn (δ := δ) (by positivity : 0 < (n:ℝ)) hU (r₀ := 0) le_rfl)
    (fun r hr => comparisonFloor_lower_on (δ := δ) (by positivity : 0 < (n:ℝ)) hU le_rfl hr)
    (comparisonCap_monotoneOn (δ := δ) (by positivity : 0 < (n:ℝ)) hU.le hL hE hd.le)
    (comparisonCap_nonneg (δ := δ) (by positivity : 0 < (n:ℝ)) hU.le hL hE hd.le zero_le_one)
    n hn hd.ne' hlam hlT b h γ (hadmissible γ)
  have hs : scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) γ.val+
      comparisonEndpointL1Cost ((β:ℝ)^2) b h ≤
        normalizedScalarParisiReference β+epsilon+comparisonEndpointL1Cost ((β:ℝ)^2) b h := by
    linarith
  exact (hmin γ).trans (hupper.trans hs)

end OAI.SKFluctuations.LaplaceWindowFormalization
