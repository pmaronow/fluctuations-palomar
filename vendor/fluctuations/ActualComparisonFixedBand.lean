module

public import CompactStrengthRadiusControl
public import ActualComparisonScalarUpper

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Function
open scoped Topology NNReal

def comparisonSweepRadiusProfile {c : ℝ} {k M : ℝ → ℝ} (hc : 0 < c)
    (hk : ContinuousOn k (Icc (0:ℝ) 1)) (hkc : ∀ r ∈ Icc (0:ℝ) 1,c ≤ k r)
    (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)
    (α : inverseIntegralConstraints 0 0 k M) : boundedMassProfiles :=
  ⟨comparisonSweepQuantile hc hk hkc hm hM α,
    ⟨comparisonSweepQuantile_bounds hc hk hkc hm hM α,
      comparisonSweepQuantile_monotone hc hk hkc hm hM α⟩⟩

theorem eventually_concrete_comparison_minimizers_fixed_band
    {β : ℝ≥0} (hβ : 0 < β) (hT : 1 < (β:ℝ)^2) {δ : ℝ} (hδ : 0 < δ)
    {dlo dhi llo lhi x : ℝ} (hdlo : 0 < dlo) (hllo : 0 < llo)
    (hlhi : lhi < (β:ℝ)^2) (hx : x ∈ Ioo (0:ℝ) 1) :
    ∃ cR CR : ℝ, 0 < cR ∧ 0 < CR ∧
      ∀ᶠ n : ℕ in atTop, ∀ (hn : 0 < n) (U L E d lam : ℝ)
        (hU : 0 < U) (hL : 0 < L) (hLU : L ≤ U) (hE : 0 < E)
        (hd : d ∈ Icc dlo dhi) (hlam : lam ∈ Icc llo lhi),
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
      ∀ α : inverseIntegralConstraints 0 0 k M,
        (∀ γ : inverseIntegralConstraints 0 0 k M,
          comparisonSweepObjective hc hk hkc hm hM n (fun _ => (β:ℝ)^2) d lam α ≤
            comparisonSweepObjective hc hk hkc hm hM n (fun _ => (β:ℝ)^2) d lam γ) →
        ∀ u ∈ Ioo (0:ℝ) 1, x ≤ u →
          cR*u ≤ comparisonSweepQuantile hc hk hkc hm hM α u ∧
            comparisonSweepQuantile hc hk hkc hm hM α u ≤ CR*u := by
  obtain ⟨a,ε,ha,hε,he⟩ := uniform_actualStrength_radius_lower_near_reference
    (dhi := dhi) hβ hT hdlo hllo hlhi hx
  refine ⟨a,1/x,ha,one_div_pos.mpr hx.1,?_⟩
  filter_upwards [he,eventually_concrete_comparison_minimum_upper_reference hβ hδ hε]
    with n hncontrol hnupper
  intro hn U L E d lam hU hL hLU hE hd hlam
  dsimp only
  intro α hmin u hu hxu
  let hc := comparisonFloor_pos (δ := δ) (by positivity : 0 < (n:ℝ)) hU (by norm_num : (0:ℝ) ≤ 1)
  let hk := comparisonFloor_continuousOn (δ := δ) (by positivity : 0 < (n:ℝ)) hU (r₀ := 0) le_rfl
  let hkc := fun r (hr : r ∈ Icc (0:ℝ) 1) =>
    comparisonFloor_lower_on (δ := δ) (by positivity : 0 < (n:ℝ)) hU le_rfl hr
  let hm := comparisonCap_monotoneOn (δ := δ) (by positivity : 0 < (n:ℝ)) hU.le hL hE (hdlo.trans_le hd.1).le
  let hM := comparisonCap_nonneg (δ := δ) (by positivity : 0 < (n:ℝ)) hU.le hL hE
    (hdlo.trans_le hd.1).le zero_le_one
  let R := comparisonSweepRadiusProfile hc hk hkc hm hM α
  have hpressure := hnupper hn U L E d lam hU hL hLU hE (hdlo.trans_le hd.1)
    (hllo.le.trans hlam.1) (hlam.2.trans hlhi.le) α hmin
  have hpx : a ≤ R.val x := hncontrol d hd lam hlam R (by
    simpa only [R,comparisonSweepRadiusProfile,comparisonSweepObjective,
      strengthSweepObjective,pathCompensatedPressure,zero_add] using hpressure)
  have hlo : a*u ≤ R.val u :=
    (mul_le_of_le_one_right ha.le hu.2.le).trans (hpx.trans (R.property.2 hxu))
  have hone : (1:ℝ) ≤ (1/x)*u := by
    rw [div_mul_eq_mul_div,one_mul,le_div_iff₀ hx.1]
    simpa only [one_mul] using hxu
  exact ⟨hlo,(R.property.1 u).2.trans hone⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
