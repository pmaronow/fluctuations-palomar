module

public import ComparisonSignedCavityInnovationClock

@[expose] public section

noncomputable section
set_option maxHeartbeats 3500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
  (hkc : ∀ r∈Icc (0:ℝ) 1,c ≤ k r)
  (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem actual_comparison_quantile_mass_spec
    (α : inverseIntegralConstraints 0 0 k M) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    α.val.val (comparisonSweepQuantile hc hk hkc hm hM α u)=u := by
  rw [comparisonSweepQuantile_eq hc hk hkc hm hM α hu]
  exact constrainedQuantile_spec zero_le_one hc hk hkc hm hM α ⟨u,hu⟩

include hm in
theorem actual_inverse_local_mass_increment
    (α : inverseIntegralConstraints 0 0 k M)
    {r₀ r₁ : ℝ} (hr₀ : r₀∈Icc (0:ℝ) 1) (hr₁ : r₁∈Icc (0:ℝ) 1)
    (hrr : r₀ ≤ r₁) :
    α.val.val r₁-α.val.val r₀ ≤ M (α.val.val r₁)*(r₁-r₀) := by
  apply (α.property.2.2 r₀ hr₀ r₁ hr₁ hrr).2.trans
  calc
    (∫ r in r₀..r₁,M (α.val.val r)) ≤ ∫ r in r₀..r₁,M (α.val.val r₁) := by
      apply intervalIntegral.integral_mono_on hrr
      · exact (show Monotone (fun r=>M (α.val.val r)) from fun r s hrs=>
          hm (α.val.property.1 r) (α.val.property.1 s) (α.val.property.2 hrs)).intervalIntegrable
      · exact intervalIntegrable_const
      · intro r hr
        exact hm (α.val.property.1 r) (α.val.property.1 r₁) (α.val.property.2 hr.2)
    _ = M (α.val.val r₁)*(r₁-r₀) := by simp [mul_comm]

theorem actual_comparison_quantile_local_mass_increment
    (α : inverseIntegralConstraints 0 0 k M)
    {u₀ u₁ : ℝ} (hu₀ : u₀∈Icc (0:ℝ) 1) (hu₁ : u₁∈Icc (0:ℝ) 1)
    (hu : u₀ ≤ u₁) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    u₁-u₀ ≤ M u₁*(R u₁-R u₀) := by
  dsimp only
  have H := actual_inverse_local_mass_increment (hm:=hm) α
    (comparisonSweepQuantile_bounds hc hk hkc hm hM α u₀)
    (comparisonSweepQuantile_bounds hc hk hkc hm hM α u₁)
    (comparisonSweepQuantile_monotone hc hk hkc hm hM α hu)
  rwa [actual_comparison_quantile_mass_spec hc hk hkc hm hM α hu₀,
    actual_comparison_quantile_mass_spec hc hk hkc hm hM α hu₁] at H

theorem actual_comparison_quantile_radius_gap_of_mass
    (α : inverseIntegralConstraints 0 0 k M)
    {u₀ u₁ gap M₀ : ℝ} (hu₀ : u₀∈Icc (0:ℝ) 1) (hu₁ : u₁∈Icc (0:ℝ) 1)
    (hu : u₀ ≤ u₁) (hM₀ : 0<M₀) (hcap : M u₁ ≤ M₀) (hgap : gap ≤ u₁-u₀) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    gap/M₀ ≤ R u₁-R u₀ := by
  dsimp only
  apply (div_le_iff₀ hM₀).mpr
  have hr := sub_nonneg.mpr (comparisonSweepQuantile_monotone hc hk hkc hm hM α hu)
  have H := actual_comparison_quantile_local_mass_increment hc hk hkc hm hM α hu₀ hu₁ hu
  have hb := mul_le_mul_of_nonneg_right hcap hr
  simpa only [mul_comm] using hgap.trans (H.trans hb)

theorem actual_comparison_mass_field_duration_lower
    (α : inverseIntegralConstraints 0 0 k M)
    {N d lam u₀ u₁ gap M₀ g₀ : ℝ}
    (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0<d) (hnd : 1/N ≤ d)
    (hlam : 0<lam) (hld : lam ≤ d^2)
    (hu₀ : u₀∈Icc (0:ℝ) 1) (hu₁ : u₁∈Icc (0:ℝ) 1) (hu : u₀ ≤ u₁)
    (hgap0 : 0 ≤ gap) (hM₀ : 0<M₀) (hg₀ : 0 ≤ g₀)
    (hcap : M u₁ ≤ M₀) (hgap : gap ≤ u₁-u₀)
    (hstrength : g₀ ≤ laplaceComparisonStrength d lam
      (comparisonSweepQuantile hc hk hkc hm hM α u₁)) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    g₀*gap/(3*M₀*Real.log N) ≤
      laplaceComparisonStrength d lam (R u₁)*R u₁-
        laplaceComparisonStrength d lam (R u₀)*R u₀ := by
  dsimp only
  have hrad := actual_comparison_quantile_radius_gap_of_mass hc hk hkc hm hM α
    hu₀ hu₁ hu hM₀ hcap hgap
  have hg := actual_comparison_quantile_field_increment_lower hc hk hkc hm hM α
    hN hlog hd hnd hlam hld hu
  have hmultip := mul_le_mul hstrength hrad (by positivity : 0 ≤ gap/M₀)
    (laplaceComparisonStrength_pos d hlam _).le
  have HH := mul_le_mul_of_nonneg_left hmultip
    (show 0 ≤ ((1:ℝ)/3)/Real.log N by positivity)
  apply le_trans _ hg
  convert HH using 1 <;> ring

end

theorem native_sampled_field_layer_projection_clock
    (n : ℕ) (b h : ℝ→ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as)
    (i₀ : Fin n) {a : ℝ} (ha : 0 ≤ a) {fork pre v w : ℕ}
    (hf : fork ≤ pre) (hpv : pre ≤ v) (hvw : v ≤ w)
    (hv : v ≤ as.length) (hw : w ≤ as.length+1)
    (ham : a ≤ partitionPoint 0 as pre) :
    PhysicalProjectionClock n (nativeSampledPhysicalSteps n b h as) fork v w a
      (physicalFieldDuration (fun st=>st.2 (Sum.inl i₀))
        (cutSlice (nativeSampledPhysicalSteps n b h as) pre v)) := by
  have hs : OrderedSteps 0 (nativeSampledPhysicalSteps n b h as) := sampleClockSteps_ordered _ _ ho
  have hmass : a ≤ physicalCutMass 0 (nativeSampledPhysicalSteps n b h as) pre := by
    simpa only [nativeSampledPhysicalSteps,physicalCutMass_sampleClockSteps _ _ _ pre (hpv.trans hv)] using ham
  apply physicalProjectionClock_of_full_field_layer n _ hs ha
    (fun st=>st.2 (Sum.inl i₀)) (native_sampled_field_homogeneous n b h as i₀)
    hf hpv hvw
  · simpa only [nativeSampledPhysicalSteps,sampleClockSteps_length] using hv
  · simpa only [nativeSampledPhysicalSteps,sampleClockSteps_length] using hw
  · exact hmass

end OAI.SKFluctuations.Cavity
