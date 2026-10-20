module

public import ActualComparisonFixedBand
public import ComparisonEndpointStability

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Function
open scoped Topology NNReal

def comparisonClockAdmissible (b h e r : ℝ → ℝ) : Prop :=
  MonotoneOn (fun u => b u-e u) (Icc (0:ℝ) 1) ∧
  MonotoneOn (fun u => h u+e u*r u) (Icc (0:ℝ) 1) ∧
  0 ≤ b 0-e 0 ∧ 0 ≤ h 0+e 0*r 0

def comparisonEndpointL1Cost (T : ℝ) (b h : ℝ → ℝ) : ℝ :=
  (1/4:ℝ)*(∫u in (0:ℝ)..1, |b u-T|)+(1/2:ℝ)*(∫u in (0:ℝ)..1, |h u|)

theorem constantStrength_comparisonClockAdmissible {T d lam : ℝ}
    (hd : d ≠ 0) (hlam : 0 ≤ lam) (hlT : lam ≤ T) (r : boundedMassProfiles) :
    comparisonClockAdmissible (fun _ => T) (fun _ => 0)
      (fun u => laplaceComparisonStrength d lam (r.val u)) r.val := by
  have hh := strengthSweep_clocks_admissible (fun _ => T) r.val hd hlam hlT
    (fun _ _ _ _ _ => le_rfl) (r.property.2.monotoneOn _) (fun u _ => r.property.1 u)
  exact ⟨hh.1,by simpa only [zero_add] using hh.2.1,hh.2.2.1 0 (by norm_num),
    by simpa only [zero_add] using hh.2.2.2 0 (by norm_num)⟩

theorem actualComparison_endpoint_cost (n : ℕ) (hn : 0 < n)
    {T d lam : ℝ} (hd : d ≠ 0) (hlam : 0 ≤ lam) (hlT : lam ≤ T)
    (b h : ℝ → ℝ) (r : boundedMassProfiles)
    (hactual : comparisonClockAdmissible b h
      (fun u => laplaceComparisonStrength d lam (r.val u)) r.val) :
    |pathCompensatedPressure n b h (fun u => laplaceComparisonStrength d lam (r.val u)) r.val 0-
      pathCompensatedPressure n (fun _ => T) (fun _ => 0)
        (fun u => laplaceComparisonStrength d lam (r.val u)) r.val 0| ≤
      comparisonEndpointL1Cost T b h := by
  have hh := constantStrength_comparisonClockAdmissible hd hlam hlT r
  simpa only [comparisonEndpointL1Cost,sub_zero] using
    pathCompensatedPressure_l1_endpoint_comparison n hn b h (fun _ => T) (fun _ => 0)
      (fun u => laplaceComparisonStrength d lam (r.val u)) r.val
      hactual.1 hactual.2.1 hh.1 hh.2.1 hactual.2.2.1 hactual.2.2.2 hh.2.2.1 hh.2.2.2

section
variable {c : ℝ} {k M : ℝ → ℝ} (hc : 0 < c)
variable (hk : ContinuousOn k (Icc (0:ℝ) 1)) (hkc : ∀ r ∈ Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

def comparisonVariableEndpointObjective (n : ℕ) (b h : ℝ → ℝ) (d lam : ℝ)
    (α : inverseIntegralConstraints 0 0 k M) : ℝ :=
  pathCompensatedPressure n b h
    (fun u => laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u))
    (comparisonSweepQuantile hc hk hkc hm hM α) 0

theorem comparisonVariableEndpointObjective_constant (n : ℕ) (T d lam : ℝ)
    (α : inverseIntegralConstraints 0 0 k M) :
    comparisonVariableEndpointObjective hc hk hkc hm hM n (fun _ => T) (fun _ => 0) d lam α=
      comparisonSweepObjective hc hk hkc hm hM n (fun _ => T) d lam α := by
  simp only [comparisonVariableEndpointObjective,comparisonSweepObjective,
    strengthSweepObjective,pathCompensatedPressure,zero_add]

end

theorem eventually_concrete_perturbed_comparison_minimizers_fixed_band
    {β : ℝ≥0} (hβ : 0 < β) (hT : 1 < (β:ℝ)^2) {δ : ℝ} (hδ : 0 < δ)
    {dlo dhi llo lhi x : ℝ} (hdlo : 0 < dlo) (hllo : 0 < llo)
    (hlhi : lhi < (β:ℝ)^2) (hx : x ∈ Ioo (0:ℝ) 1) :
    ∃ ρ cR CR : ℝ, 0 < ρ ∧ 0 < cR ∧ 0 < CR ∧
      ∀ᶠ n : ℕ in atTop, ∀ (hn : 0 < n) (U L E d lam : ℝ)
        (hU : 0 < U) (hL : 0 < L) (hLU : L ≤ U) (hE : 0 < E)
        (hd : d ∈ Icc dlo dhi) (hlam : lam ∈ Icc llo lhi) (b h : ℝ → ℝ),
      let k := comparisonFloor (n:ℝ) δ U
      let M := comparisonCap (n:ℝ) δ U L E d
      let hc := comparisonFloor_pos (by positivity : 0 < (n:ℝ)) hU (by norm_num : (0:ℝ) ≤ 1)
      let hk := comparisonFloor_continuousOn (by positivity : 0 < (n:ℝ)) hU (r₀ := 0) le_rfl
      let hkc := fun r (hr : r ∈ Icc (0:ℝ) 1) =>
        comparisonFloor_lower_on (by positivity : 0 < (n:ℝ)) hU le_rfl hr
      let hm := comparisonCap_monotoneOn (by positivity : 0 < (n:ℝ)) hU.le hL
        hE (hdlo.trans_le hd.1).le
      let hM := comparisonCap_nonneg (by positivity : 0 < (n:ℝ)) hU.le hL
        hE (hdlo.trans_le hd.1).le zero_le_one
      comparisonEndpointL1Cost ((β:ℝ)^2) b h ≤ ρ →
      (∀ γ : inverseIntegralConstraints 0 0 k M,
        comparisonClockAdmissible b h
          (fun u => laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM γ u))
          (comparisonSweepQuantile hc hk hkc hm hM γ)) →
      ∀ α : inverseIntegralConstraints 0 0 k M,
        (∀ γ : inverseIntegralConstraints 0 0 k M,
          comparisonVariableEndpointObjective hc hk hkc hm hM n b h d lam α ≤
            comparisonVariableEndpointObjective hc hk hkc hm hM n b h d lam γ) →
        ∀ u ∈ Ioo (0:ℝ) 1, x ≤ u →
          cR*u ≤ comparisonSweepQuantile hc hk hkc hm hM α u ∧
            comparisonSweepQuantile hc hk hkc hm hM α u ≤ CR*u := by
  obtain ⟨a,ε,ha,hε,he⟩ := uniform_actualStrength_radius_lower_near_reference
    (dhi := dhi) hβ hT hdlo hllo hlhi hx
  refine ⟨ε/8,a,1/x,by positivity,ha,one_div_pos.mpr hx.1,?_⟩
  filter_upwards [he,eventually_comparison_scalar_reference_competitor hβ hδ (half_pos hε)]
    with n hncontrol hntrial
  intro hn U L E d lam hU hL hLU hE hd hlam b h
  dsimp only
  intro hcost hadmissible α hmin u hu hxu
  let hc := comparisonFloor_pos (δ := δ) (by positivity : 0 < (n:ℝ)) hU (by norm_num : (0:ℝ) ≤ 1)
  let hk := comparisonFloor_continuousOn (δ := δ) (by positivity : 0 < (n:ℝ)) hU (r₀ := 0) le_rfl
  let hkc := fun r (hr : r ∈ Icc (0:ℝ) 1) =>
    comparisonFloor_lower_on (δ := δ) (by positivity : 0 < (n:ℝ)) hU le_rfl hr
  let hm := comparisonCap_monotoneOn (δ := δ) (by positivity : 0 < (n:ℝ)) hU.le hL hE (hdlo.trans_le hd.1).le
  let hM := comparisonCap_nonneg (δ := δ) (by positivity : 0 < (n:ℝ)) hU.le hL hE
    (hdlo.trans_le hd.1).le zero_le_one
  let R := comparisonSweepRadiusProfile hc hk hkc hm hM α
  obtain ⟨γ,hγ⟩ := hntrial U L E d hU hL hLU hE (hdlo.trans_le hd.1).le
  let Q := comparisonSweepRadiusProfile hc hk hkc hm hM γ
  have hpα := actualComparison_endpoint_cost n hn (ne_of_gt (hdlo.trans_le hd.1))
    (hllo.le.trans hlam.1) (hlam.2.trans hlhi.le) b h R (hadmissible α)
  have hpγ := actualComparison_endpoint_cost n hn (ne_of_gt (hdlo.trans_le hd.1))
    (hllo.le.trans hlam.1) (hlam.2.trans hlhi.le) b h Q (hadmissible γ)
  have hγconst := (comparisonSweepObjective_bounds hβ hc hk hkc hm hM n hn
    (ne_of_gt (hdlo.trans_le hd.1)) (hllo.le.trans hlam.1) (hlam.2.trans hlhi.le) γ).2.trans hγ
  have hpressure : pathCompensatedPressure n (fun _ => (β:ℝ)^2) (fun _ => 0)
      (fun v => laplaceComparisonStrength d lam (R.val v)) R.val 0 ≤
        normalizedScalarParisiReference β+ε := by
    have hming := hmin γ
    have hγvalue : pathCompensatedPressure n (fun _ => (β:ℝ)^2) (fun _ => 0)
        (fun v => laplaceComparisonStrength d lam (Q.val v)) Q.val 0 ≤
          normalizedScalarParisiReference β+ε/2 := by
      simpa only [Q,comparisonSweepRadiusProfile,comparisonSweepObjective,
        strengthSweepObjective,pathCompensatedPressure,zero_add] using hγconst
    change pathCompensatedPressure n b h
        (fun v => laplaceComparisonStrength d lam (R.val v)) R.val 0 ≤
      pathCompensatedPressure n b h
        (fun v => laplaceComparisonStrength d lam (Q.val v)) Q.val 0 at hming
    have hpa := neg_abs_le (pathCompensatedPressure n b h
      (fun v => laplaceComparisonStrength d lam (R.val v)) R.val 0-
      pathCompensatedPressure n (fun _ => (β:ℝ)^2) (fun _ => 0)
        (fun v => laplaceComparisonStrength d lam (R.val v)) R.val 0)
    have hpg := le_abs_self (pathCompensatedPressure n b h
      (fun v => laplaceComparisonStrength d lam (Q.val v)) Q.val 0-
      pathCompensatedPressure n (fun _ => (β:ℝ)^2) (fun _ => 0)
        (fun v => laplaceComparisonStrength d lam (Q.val v)) Q.val 0)
    linarith
  have hpx := hncontrol d hd lam hlam R hpressure
  have hlo : a*u ≤ R.val u :=
    (mul_le_of_le_one_right ha.le hu.2.le).trans (hpx.trans (R.property.2 hxu))
  have hone : (1:ℝ) ≤ (1/x)*u := by
    rw [div_mul_eq_mul_div,one_mul,le_div_iff₀ hx.1]
    simpa only [one_mul] using hxu
  exact ⟨hlo,(R.property.1 u).2.trans hone⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
