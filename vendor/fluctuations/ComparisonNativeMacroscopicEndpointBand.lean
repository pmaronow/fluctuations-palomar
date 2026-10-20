module

public import ComparisonNativeOverlapRawAmplitude
public import ComparisonMacroscopicEndpointUpper
public import ComparisonMacroscopicScalarIdentification

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Function
open scoped Topology NNReal
namespace NativeOverlapMinimum

theorem macro_comparisonClockAdmissible
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (gamma : a.context.Profile) :
    comparisonClockAdmissible a.b a.h
      (fun u=>laplaceComparisonStrength a.context.d a.lam (a.context.R gamma u))
      (a.context.R gamma) := by
  have h := strengthSweep_clocks_admissible a.b (a.context.R gamma)
    a.context.hd.ne' a.hlam.le a.hlb a.hb
    ((comparisonSweepQuantile_monotone a.context.hc a.context.hk a.context.hkc
      a.context.hm a.context.hM gamma).monotoneOn (Icc (0:ℝ) 1))
    (fun u _=>comparisonSweepQuantile_bounds a.context.hc a.context.hk a.context.hkc
      a.context.hm a.context.hM gamma u)
  exact ⟨h.1,a.hh.add h.2.1,h.2.2.1 0 (by norm_num),
    add_nonneg a.hh0 (h.2.2.2 0 (by norm_num))⟩

theorem eventually_macro_minimizers_fixed_band
    {β : ℝ≥0} (hβ : 0 < β) (hT : 1 < (β:ℝ)^2) {delta : ℝ} (hdelta : 0 < delta)
    {dlo dhi llo lhi x : ℝ} (hdlo : 0 < dlo) (hllo : 0 < llo)
    (hlhi : lhi < (β:ℝ)^2) (hx : x∈Ioo (0:ℝ) 1)
    (m cl cu Az C0 Ct D Bclock : ℝ) :
    ∃rho cR CR : ℝ,0 < rho ∧ 0 < cR ∧ 0 < CR ∧ ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      a.context.d∈Icc dlo dhi → a.lam∈Icc llo lhi →
      comparisonEndpointL1Cost ((β:ℝ)^2) a.b a.h ≤ rho →
      ∀u∈Ioo (0:ℝ) 1,x ≤ u → cR*u ≤ a.R u ∧ a.R u ≤ CR*u := by
  obtain ⟨rho,cR,CR,hrho,hcR,hCR,hevent⟩ :=
    eventually_concrete_perturbed_comparison_minimizers_fixed_band
      (dhi := dhi) hβ hT hdelta hdlo hllo hlhi hx
  refine ⟨rho,cR,CR,hrho,hcR,hCR,?_⟩
  filter_upwards [hevent] with n hn
  intro a hd hlam hcost
  exact hn a.context.hn a.context.U a.context.L a.context.E a.context.d a.lam
    a.context.hU a.context.hL (min_le_left _ _) a.context.hE hd hlam a.b a.h hcost
    (fun gamma=>a.macro_comparisonClockAdmissible gamma) a.alpha a.minimum

theorem eventually_macro_minimum_upper_reference
    {β : ℝ≥0} (hβ : 0 < β) {delta epsilon : ℝ} (hdelta : 0 < delta)
    (hepsilon : 0 < epsilon) (m cl cu Az C0 Ct D Bclock : ℝ) :
    ∀ᶠn : ℕ in atTop,∀a : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock,
      a.lam ≤ (β:ℝ)^2 →
      pathCompensatedPressure n a.b a.h
        (fun u=>laplaceComparisonStrength a.context.d a.lam (a.R u)) a.R 0 ≤
          normalizedScalarParisiReference β+epsilon+
            comparisonEndpointL1Cost ((β:ℝ)^2) a.b a.h := by
  filter_upwards [eventually_macroEndpoint_minimum_upper_reference hβ hdelta hepsilon]
    with n hn
  intro a hlT
  exact hn a.context.hn a.context.U a.context.L a.context.E a.context.d a.lam
    a.context.hU a.context.hL (min_le_left _ _) a.context.hE a.context.hd a.hlam.le
    hlT a.b a.h (fun gamma=>a.macro_comparisonClockAdmissible gamma) a.alpha a.minimum

theorem macro_radius_limit_scalar_minimizer
    {β : ℝ≥0} (hβ : 0 < β) {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hdelta : 0 < delta) (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (a : (n:ℕ)→NativeOverlapMinimum (dim n) m delta cl cu Az C0 Ct D Bclock)
    {d lam : ℝ} (hd0 : d≠0)
    (hd : Tendsto (fun n=>(a n).context.d) atTop (𝓝 d))
    (hlam : Tendsto (fun n=>(a n).lam) atTop (𝓝 lam))
    (hlamb : ∀n,(a n).lam ≤ (β:ℝ)^2) (hlamT : lam∈Ioo (0:ℝ) ((β:ℝ)^2))
    {r : boundedMassProfiles}
    (hr : Tendsto (fun n=>comparisonSweepRadiusProfile (a n).context.hc (a n).context.hk
      (a n).context.hkc (a n).context.hm (a n).context.hM (a n).alpha) atTop (𝓝 r))
    (hcost : Tendsto (fun n=>comparisonEndpointL1Cost ((β:ℝ)^2) (a n).b (a n).h)
      atTop (𝓝 0)) :
    quantileMassProfile r.val (fun u _=>r.property.1 u) ∈ scalarReferenceMinimizers β hβ := by
  have hp := actualStrengthComparisonPressure_tendsto_jointScalar_of_endpoint_cost
    dim hdim hd0 (fun n=>(a n).context.hd.ne') hd hlam
    (fun n=>⟨(a n).hlam.le,hlamb n⟩) hlamT hr (fun n=>(a n).b) (fun n=>(a n).h)
    (fun n=>(a n).macro_comparisonClockAdmissible (a n).alpha) hcost
  have hv : jointScalarVariationalValue ((β:ℝ)^2)
      (fun u=>laplaceComparisonStrength d lam (r.val u)) r.val≤normalizedScalarParisiReference β := by
    apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    have hu := hdim.eventually (eventually_macro_minimum_upper_reference hβ hdelta
      (half_pos hepsilon) m cl cu Az C0 Ct D Bclock)
    have hc := hcost.eventually (eventually_le_nhds (half_pos hepsilon))
    have hevent : ∀ᶠn in atTop,pathCompensatedPressure (dim n) (a n).b (a n).h
        (fun u=>laplaceComparisonStrength (a n).context.d (a n).lam ((a n).R u))
        (a n).R 0≤normalizedScalarParisiReference β+epsilon := by
      filter_upwards [hu,hc] with n hun hcn
      have hupper := hun (a n) (hlamb n)
      linarith
    exact le_of_tendsto hp hevent
  obtain ⟨c,hc,he,heb,her⟩ := actualStrength_profile_geometry hd0 hlamT r
  exact jointScalarVariationalValue_radius_scalar_minimizer hβ hc _ _ he heb her
    (r.property.2.monotoneOn _) (fun u _=>r.property.1 u) hv

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
