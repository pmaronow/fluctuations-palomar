module

public import ComparisonCriticalPositiveWallSupportSpinSelection
public import ComparisonCriticalPositiveWallSpinProfileCompactness

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 12000000

theorem critical_positive_wall_radius_spin_between_support_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (V : ℝ→ℝ)
    (hCDF : ∀t,Tendsto (fun n=>(M n).actualRadiusMassProfile.val
      ((M n).xs*t)/(M n).xs) atTop (𝓝 (V t)))
    (s : NonnegativeMassProfile)
    (Hspin : ∀t,Tendsto (fun n=>(M n).actualScaledRadiusSpin t)
      atTop (𝓝 (s.mass t)))
    {a b t : ℝ} (ha : 0 ≤ a) (hat : a < t) (htb : t < b)
    (hasupport : a∈comparisonIncrementSupport V)
    (hbsupport : b∈comparisonIncrementSupport V) :
    s.mass t∈Icc a b := by
  obtain ⟨ns,hns,w,Hr,Hs⟩ := exists_critical_positive_wall_support_spin_selections_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hD dim hdim M hfixed hxlim hsRatio
    V hCDF ha hasupport
  have Hlower : a ≤ s.mass t := by
    apply le_of_tendsto_of_tendsto Hs ((Hspin t).comp hns)
    filter_upwards [Hr.eventually (gt_mem_nhds hat)] with j hj
    apply div_le_div_of_nonneg_right _ (M (ns j)).hxs.le
    apply (M (ns j)).mass_mean_le_radius_spin_of_radius_le (w j).property
    have H := (div_lt_iff₀ (M (ns j)).hxs).mp hj
    simpa only [mul_comm] using H.le
  obtain ⟨ms,hms,z,Hr',Hs'⟩ := exists_critical_positive_wall_support_spin_selections_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hD dim hdim M hfixed hxlim hsRatio
    V hCDF (ha.trans (hat.le.trans htb.le)) hbsupport
  have Hrmin := ActualHighWallOverlapMinimum.rmin_over_larger_scale_tendsto_zero
    hdelta dim hdim M (fun n=>(M n).xs) (fun n=>(hfixed n).ge)
  have ht0 : 0 < t := ha.trans_lt hat
  have Hupper : s.mass t ≤ b := by
    apply le_of_tendsto_of_tendsto ((Hspin t).comp hms) Hs'
    filter_upwards [Hr'.eventually (lt_mem_nhds htb),
      (Hrmin.comp hms).eventually (gt_mem_nhds ht0)] with j hj hjmin
    apply div_le_div_of_nonneg_right _ (M (ms j)).hxs.le
    have H := (lt_div_iff₀ (M (ms j)).hxs).mp hj
    have H' : (M (ms j)).xs*t <
        (M (ms j)).data.wallRadius (M (ms j)).alpha (z j) := by
      simpa only [mul_comm] using H
    have Hmin := (div_lt_iff₀ (M (ms j)).hxs).mp hjmin
    have Hmin' : (M (ms j)).data.rmin < (M (ms j)).xs*t := by
      simpa only [mul_comm] using Hmin
    have hhigh : (M (ms j)).data.s < z j :=
      (M (ms j)).data.wallRadius_high_mass (M (ms j)).alpha
        (Hmin'.trans H')
    apply (M (ms j)).radius_spin_le_mass_mean_of_radius_le
      ⟨hhigh.le,(z j).property.2⟩
    exact H'.le
  exact ⟨Hlower,Hupper⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
