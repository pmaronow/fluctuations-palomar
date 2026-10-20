module

public import ComparisonActualHighOnlyMacroscopicTrialUpper

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000

theorem actual_high_only_endpoint_l1_cost_nonneg (T : ℝ) (b h : ℝ→ℝ) :
    0 ≤ comparisonEndpointL1Cost T b h := by
  have HB:=intervalIntegral.integral_nonneg (μ:=volume) zero_le_one (fun u _=>abs_nonneg (b u-T))
  have HH:=intervalIntegral.integral_nonneg (μ:=volume) zero_le_one (fun u _=>abs_nonneg (h u))
  unfold comparisonEndpointL1Cost
  positivity

theorem actual_high_only_objective_tendsto_jointScalar_of_endpoint_cost
    {delta : ℝ} (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (a : (n:ℕ)→ActualHighOnlyComparisonData (dim n) delta)
    (lam : ℕ→ℝ) (hlam : ∀n,lam n∈Icc (0:ℝ) ((a n).d^2))
    (alpha : (n:ℕ)→(a n).Profile) {d l T : ℝ} (hd0 : d≠0)
    (hd : Tendsto (fun n=>(a n).d) atTop (𝓝 d))
    (hl : Tendsto lam atTop (𝓝 l)) (hlT : ∀n,lam n ≤ T) (hlTlim : l∈Ioo (0:ℝ) T)
    {r : boundedMassProfiles}
    (hr : Tendsto (fun n=>(a n).radiusProfile (alpha n)) atTop (𝓝 r))
    (hs : Tendsto (fun n=>(a n).s) atTop (𝓝 0))
    (hcost : Tendsto (fun n=>comparisonEndpointL1Cost T (a n).b (a n).h) atTop (𝓝 0)) :
    Tendsto (fun n=>(a n).objective (lam n) (alpha n)) atTop
      (𝓝 (jointScalarVariationalValue T
        (fun u=>laplaceComparisonStrength d l (r.val u)) r.val)) := by
  have hT:0 ≤ T:=(hlam 0).1.trans (hlT 0)
  have Hbound:Tendsto (fun n=>comparisonEndpointL1Cost T (a n).b (a n).h+(a n).s*T/4)
      atTop (𝓝 0):=by
    simpa only [zero_mul,zero_div,add_zero] using hcost.add ((hs.mul_const T).div_const 4)
  have Hcost:Tendsto (fun n=>comparisonEndpointL1Cost T
      ((a n).fullStrengthBareMatrix (alpha n) (lam n)) (a n).h) atTop (𝓝 0):=by
    apply squeeze_zero (fun n=>actual_high_only_endpoint_l1_cost_nonneg _ _ _) _ Hbound
    intro n
    have H:=(a n).fullStrengthBareMatrix_endpoint_cost_le (T:=T) (alpha n) (hlam n)
    have Hlam:=mul_le_mul_of_nonneg_left (hlT n) (a n).hs.1
    linarith
  have HP:=actualStrengthComparisonPressure_tendsto_jointScalar_of_endpoint_cost
    dim hdim hd0 (fun n=>(a n).hd.ne') hd hl
    (fun n=>⟨(hlam n).1,hlT n⟩) hlTlim hr
    (fun n=>(a n).fullStrengthBareMatrix (alpha n) (lam n)) (fun n=>(a n).h)
    (fun n=>(a n).fullStrength_clockAdmissible (alpha n) (hlam n)) Hcost
  apply HP.congr'
  exact Eventually.of_forall (fun n=>((a n).original_objective_eq_fullStrength (alpha n) (lam n)).symm)

theorem actual_high_only_radius_limit_scalar_minimizer
    {beta : ℝ≥0} (hbeta : 0<beta) {delta : ℝ} (hdelta : 0<delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (a : (n:ℕ)→ActualHighOnlyComparisonData (dim n) delta)
    (lam : ℕ→ℝ) (hlam : ∀n,lam n∈Icc (0:ℝ) ((a n).d^2))
    (M : (n:ℕ)→ActualHighOnlyComparisonMinimum (a n) (lam n))
    {d l : ℝ} (hd0 : d≠0) (hd : Tendsto (fun n=>(a n).d) atTop (𝓝 d))
    (hl : Tendsto lam atTop (𝓝 l)) (hlT : ∀n,lam n ≤ (beta:ℝ)^2)
    (hlTlim : l∈Ioo (0:ℝ) ((beta:ℝ)^2)) {r : boundedMassProfiles}
    (hr : Tendsto (fun n=>(a n).radiusProfile (M n).alpha) atTop (𝓝 r))
    (hs : Tendsto (fun n=>(a n).s) atTop (𝓝 0))
    (hcost : Tendsto (fun n=>comparisonEndpointL1Cost ((beta:ℝ)^2) (a n).b (a n).h)
      atTop (𝓝 0)) :
    quantileMassProfile r.val (fun u _=>r.property.1 u)∈scalarReferenceMinimizers beta hbeta := by
  have HP:=actual_high_only_objective_tendsto_jointScalar_of_endpoint_cost
    dim hdim a lam hlam (fun n=>(M n).alpha) hd0 hd hl hlT hlTlim hr hs hcost
  have Herror:Tendsto (fun n=>comparisonEndpointL1Cost ((beta:ℝ)^2) (a n).b (a n).h+
      (a n).s*(beta:ℝ)^2/4) atTop (𝓝 0):=by
    simpa only [zero_mul,zero_div,add_zero] using hcost.add ((hs.mul_const ((beta:ℝ)^2)).div_const 4)
  have HV:jointScalarVariationalValue ((beta:ℝ)^2)
      (fun u=>laplaceComparisonStrength d l (r.val u)) r.val ≤ normalizedScalarParisiReference beta:=by
    apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    have Hupper:=eventually_actual_high_only_minimum_upper_scalar_reference hbeta hdelta
      (half_pos hepsilon) dim hdim a lam hlam hlT M hs
    have Hsmall:=Herror.eventually (eventually_le_nhds (half_pos hepsilon))
    apply le_of_tendsto HP
    filter_upwards [Hupper,Hsmall] with n hnUpper hnSmall
    have Hlam:=mul_le_mul_of_nonneg_left (hlT n) (a n).hs.1
    linarith
  obtain ⟨c,hc,He,Heb,Her⟩:=actualStrength_profile_geometry hd0 hlTlim r
  exact jointScalarVariationalValue_radius_scalar_minimizer hbeta hc _ _ He Heb Her
    (r.property.2.monotoneOn _) (fun u _=>r.property.1 u) HV

end OAI.SKFluctuations.LaplaceWindowFormalization
