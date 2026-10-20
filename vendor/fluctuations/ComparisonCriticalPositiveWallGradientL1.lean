module

public import ComparisonCriticalPositiveWallStrengthIdentity
public import ComparisonBoundedPrincipalIntegrability

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 14000000

theorem critical_positive_wall_gradient_L1_of_spin_and_radius_defect
    {m delta cl cu Az C0 Ct D Bclock a b K : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hspinBound : ∀n,∀t∈Icc a b,(M n).actualScaledRadiusSpin t∈Icc (0:ℝ) K)
    (s : NonnegativeMassProfile)
    (hspin : ∀t∈Icc a b,Tendsto (fun n=>(M n).actualScaledRadiusSpin t)
      atTop (𝓝 (s.mass t)))
    (hdefect : Tendsto (fun n=>(∫r in Icc ((M n).xs*a) ((M n).xs*b),
      (M n).wallRadiusPointDefect r)/(M n).xs^3) atTop (𝓝 0)) :
    Tendsto (fun n=>∫t in Icc a b,
      |(M n).actualVirtualScaledGradient t-
        comparisonScaledStationarity (laplaceComparisonShape t)
          (laplaceComparisonSlope t) t (s.mass t)|) atTop (𝓝 0) := by
  let h := fun n t=>(M n).data.g ((M n).xs*t)/(M n).xs^2
  let p := fun n t=>comparisonLogSlope (M n).data.g ((M n).xs*t)
  let spin := fun n=>(M n).actualScaledRadiusSpin
  let F := fun t=>comparisonScaledStationarity (laplaceComparisonShape t)
    (laplaceComparisonSlope t) t (s.mass t)
  have hhidentity n t : h n t=laplaceComparisonShape t :=
    (M n).critical_wall_strength_scaled_identity (hfixed n) t
  have hpidentity n t : p n t=laplaceComparisonSlope t :=
    (M n).critical_wall_slope_scaled_identity (hfixed n) t
  have hstrength n t (_ht:t∈Icc a b) : h n t∈Icc (0:ℝ) (max K 1) := by
    rw [hhidentity n t]
    exact ⟨(laplaceComparisonShape_pos t).le,
      (laplaceComparisonShape_le_one t).trans (le_max_right K 1)⟩
  have hslope n t (_ht:t∈Icc a b) : p n t∈Icc (0:ℝ) 1 := by
    rw [hpidentity n t]
    have H:=laplaceComparisonSlope_mem_Ico t
    exact ⟨H.1,H.2.le⟩
  have hspinb n t (ht:t∈Icc a b) : spin n t∈Icc (0:ℝ) (max K 1) :=
    ⟨(hspinBound n t ht).1,(hspinBound n t ht).2.trans (le_max_left K 1)⟩
  have hprincipal : Tendsto (fun n=>∫t in Icc a b,
      |(M n).actualScaledPrincipalGradient t-F t|) atTop (𝓝 0) := by
    have H:=comparison_principal_density_L1_tendsto h p spin
      laplaceComparisonShape laplaceComparisonSlope s.mass ha hab
      (fun n=>((laplaceComparisonStrength_contDiff _ _).continuous.measurable.comp
        (measurable_const.mul measurable_id)).div_const _)
      (fun n=>by
        change Measurable (fun t=>comparisonLogSlope (M n).data.g ((M n).xs*t))
        simpa only [(M n).critical_wall_slope_scaled_identity (hfixed n)]
          using comparison_shape_slope_continuous.measurable)
      (fun n=>(M n).actual_scaled_radius_spin_monotone.measurable)
      laplaceComparisonShape_contDiff.continuous.measurable
      comparison_shape_slope_continuous.measurable s.monotone.measurable
      hstrength hslope hspinb (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact ⟨(show Tendsto (fun n=>h n t) atTop (𝓝 (laplaceComparisonShape t)) by
          have heq : (fun n=>h n t)=(fun _ : ℕ=>laplaceComparisonShape t) :=
            funext fun n=>hhidentity n t
          rw [heq]
          exact tendsto_const_nhds),
          (show Tendsto (fun n=>p n t) atTop (𝓝 (laplaceComparisonSlope t)) by
          have heq : (fun n=>p n t)=(fun _ : ℕ=>laplaceComparisonSlope t) :=
            funext fun n=>hpidentity n t
          rw [heq]
          exact tendsto_const_nhds),hspin t ht⟩)
    simpa only [h,p,spin,F,ActualHighWallOverlapMinimum.actualScaledPrincipalGradient]
      using H
  have hGm n : AEStronglyMeasurable (M n).actualVirtualScaledGradient
      (volume.restrict (Icc a b)) :=
    (M n).actual_scaled_gradient_aestronglyMeasurable ha
  have hPi n : IntegrableOn (M n).actualScaledPrincipalGradient (Icc a b) :=
    (M n).actual_scaled_principal_gradient_integrable ha
  have hLi : IntegrableOn F (Icc a b) := by
    simpa only [F,one_mul] using
      comparison_bounded_principal_density_integrable s (L:=1) (A:=1)
        (by norm_num) (by norm_num) ha.le
  have hDi n : IntegrableOn (fun t=>(M n).wallRadiusPointDefect ((M n).xs*t)/
      (M n).xs^2) (Icc a b) :=
    (M n).actual_scaled_radius_defect_integrable
  apply comparison_native_gradient_L1_tendsto
    (fun n=>(M n).data.g) (fun n=>(M n).alpha.val.val)
    (fun n=>orderedPathS (dim n+1) (M n).bf (M n).hf)
    (fun n=>orderedPathB (dim n+1) (M n).bf (M n).hf)
    (fun n=>(M n).xs) F ha hab (by norm_num : (0:ℝ)≤1)
    (fun n=>(M n).hxs)
    (fun n t ht=>laplaceComparisonStrength_pos (M n).data.d
      (sq_pos_of_pos (M n).data.hd) _)
    (fun n t ht=>by
      rw [(M n).critical_wall_strength_scaled_identity (hfixed n) t]
      exact laplaceComparisonShape_le_one t)
    (fun n t ht=>hslope n t ht)
    (fun n t _ht=>((M n).full_radius_moments.2.2 _).2.1)
    hGm hPi hLi hDi
  · exact hprincipal
  · exact hdefect

end OAI.SKFluctuations.LaplaceWindowFormalization
