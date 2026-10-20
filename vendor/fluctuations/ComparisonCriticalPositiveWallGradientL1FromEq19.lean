module

public import ComparisonCriticalPositiveWallGapPrimitive
public import ComparisonCriticalPositiveWallGradientL1Along
public import ComparisonCriticalPositiveWallRadiusDefectFromEq19
public import ComparisonNativeCavityConcentrationBareRadius

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy ActualHighWallOverlapMinimum
open scoped Topology
set_option maxHeartbeats 14000000

theorem critical_positive_wall_gradient_L1_from_Eq19_on_gap_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (V : ℝ→ℝ) (hV : Monotone V)
    (hCDF : ∀r,Tendsto (fun n=>(M n).alpha.val.val ((M n).xs*r)/(M n).xs)
      atTop (𝓝 (V r)))
    (s : NonnegativeMassProfile)
    (hspin : ∀r,Tendsto (fun n=>(M n).actualScaledRadiusSpin r)
      atTop (𝓝 (s.mass r)))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport V)
    (hmass : 0 < V ((a+b)/2))
    {u v : ℝ} (hu : u∈Ioo a b) (hv : v∈Ioo a b) (huv : u ≤ v) :
    Tendsto (fun n=>∫r in Icc u v,
      |(M n).actualVirtualScaledGradient r-
        comparisonScaledStationarity (laplaceComparisonShape r)
          (laplaceComparisonSlope r) r (s.mass r)|) atTop (𝓝 0) := by
  let c := V ((a+b)/2)/2
  have hc : 0 < c := half_pos hmass
  have hu0 : 0 < u := ha.trans_lt hu.1
  have Hrmin := ActualHighWallOverlapMinimum.rmin_over_larger_scale_tendsto_zero
    hdelta dim hdim M (fun n=>(M n).xs) (fun n=>(hfixed n).ge)
  have Hleft : ∀ᶠn in atTop,(M n).data.rmin < (M n).xs*u := by
    filter_upwards [Hrmin.eventually (gt_mem_nhds hu0)] with n hn
    simpa only [mul_comm] using (div_lt_iff₀ (M n).hxs).mp hn
  have Hright : ∀ᶠn in atTop,(M n).xs*v ≤ 1 := by
    have H : Tendsto (fun n=>(M n).xs*v) atTop (𝓝 0) := by
      simpa only [zero_mul] using hxs.mul_const v
    exact H.eventually (eventually_le_nhds zero_lt_one)
  have Hmass := critical_positive_wall_compact_gap_mass_band_along
    dim M V hV hCDF hab hgap hmass hu hv
  have Hband : ∀ᶠn in atTop,(M n).data.rmin < (M n).xs*u ∧
      (M n).xs*v ≤ 1 ∧ c*(M n).xs ≤
        (M n).alpha.val.val ((M n).xs*u) := by
    filter_upwards [Hleft,Hright,Hmass] with n hnleft hnright hnmass
    exact ⟨hnleft,hnright,(hnmass u ⟨le_rfl,huv⟩).1⟩
  have Hdefect := critical_positive_wall_radius_defect_L1_of_eventual_mass_band
    Bclock hm hdelta hmargin hcl hcu hAz hC0 hCt hc huv dim hdim M
    hfixed Hband
    (fun n=>Fintype.card (FeatureIndex (dim n+1))-1)
    (fun n=>cavityCanonicalFeatureEquiv (dim n))
  exact critical_positive_wall_gradient_L1_of_spin_profile_and_radius_defect
    hu0 huv dim M hfixed s (fun r _=>hspin r) Hdefect

end OAI.SKFluctuations.LaplaceWindowFormalization
