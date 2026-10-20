module

public import ComparisonCriticalPositiveWallGapFromEq19
public import ComparisonCriticalPositiveWallGapSpinRange
public import ComparisonBoundedVirtualGradientBehavior

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 14000000

theorem critical_positive_wall_virtual_gap_from_Eq19_and_scalar_closure_along
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D) (hT : 0 < T)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (V : ℝ→ℝ) (hV : Monotone V)
    (hCDF : ∀r,Tendsto (fun n=>(M n).alpha.val.val ((M n).xs*r)/(M n).xs)
      atTop (𝓝 (V r)))
    (hRadius : ∀r,Tendsto (fun n=>(M n).actualRadiusMassProfile.val
      ((M n).xs*r)/(M n).xs) atTop (𝓝 (V r)))
    (s : NonnegativeMassProfile)
    (hspin : ∀r,Tendsto (fun n=>(M n).actualScaledRadiusSpin r)
      atTop (𝓝 (s.mass r)))
    (g : ℝ→ℝ)
    {a b B : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbB : b < B)
    (hasupport : a∈comparisonIncrementSupport V)
    (hbsupport : b∈comparisonIncrementSupport V)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport V)
    (hmass : 0 < V ((a+b)/2))
    (hclosure : ∀ᵐt∂volume.restrict (Ioo a b),
      g (s.mass t)=laplaceComparisonShape t/T*(s.mass t-t)) :
    Nonempty (ComparisonVirtualGapData g a b) := by
  obtain ⟨K,hK,j,_hjmono,hjrange,⟨P⟩⟩ :=
    critical_positive_wall_gap_primitive_from_Eq19_along
      hm hdelta hmargin hcl hcu hAz hC0 hCt dim hdim M hfixed hxs hsRatio
      V hV hCDF s hspin ha hab hbB hasupport hbsupport hgap hmass
  have hj : ∀ᵐt∂volume.restrict (Ioo a b),0 < j t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hKpos : 0 < K := zero_lt_one.trans_le hK
    have hK2 : 0 < K^2 := pow_pos hKpos 2
    exact (one_div_pos.mpr hK2).trans_le
      (hjrange t ⟨ht.1.le,ht.2.le⟩).1
  have hrange : ∀ᵐt∂volume.restrict (Ioo a b),s.mass t∈Icc a b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact critical_positive_wall_radius_spin_between_support_along
      hm hdelta (by linarith only [hmargin,hdelta]) hcl hcu hAz hC0 hCt hD
      dim hdim M hfixed hxs hsRatio V hRadius s hspin
      ha ht.1 ht.2 hasupport hbsupport
  have P' : ComparisonPinnedGapPrimitive a b (fun t=>j t*
      comparisonScaledStationarity (1*laplaceComparisonShape (1*t))
        (laplaceComparisonSlope (1*t)) t (s.mass t)) := by
    simpa only [one_mul] using P
  have hclosure' : ∀ᵐt∂volume.restrict (Ioo a b),
      g (s.mass t)=(1*laplaceComparisonShape (1*t))/T*(s.mass t-t) := by
    simpa only [one_mul] using hclosure
  exact ⟨comparison_bounded_pinned_primitive_to_gap ha (by norm_num) hT
    P' hj hrange hclosure'⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
