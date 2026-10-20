module

public import ComparisonNativeActualBoundedGradientCore
public import ComparisonVirtualGapLimitExistence

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology

theorem comparison_bounded_scaled_principal_sign
    {L A j t v : ℝ} (hL : 0 < L) (hj : 0 < j) (ht : 0 < t) (hv : 0 ≤ v) :
    (t < v → j*comparisonScaledStationarity (L*laplaceComparisonShape (A*t))
      (laplaceComparisonSlope (A*t)) t v < 0) ∧
    (v < t → 0 < j*comparisonScaledStationarity (L*laplaceComparisonShape (A*t))
      (laplaceComparisonSlope (A*t)) t v) := by
  have hp:=laplaceComparisonSlope_mem_Ico (A*t)
  have H:=stationarity_density_sign ht hv ⟨hp.1,hp.2.le⟩
    (mul_pos hL (laplaceComparisonShape_pos (A*t))) hj
  simpa only [comparisonScaledStationarity,mul_assoc] using H.2

def comparison_bounded_pinned_primitive_to_gap
    {a b L A T : ℝ} {g j : ℝ→ℝ} {s : NonnegativeMassProfile}
    (ha : 0 ≤ a) (hL : 0 < L) (hT : 0 < T)
    (P : ComparisonPinnedGapPrimitive a b (fun t=>j t*
      comparisonScaledStationarity (L*laplaceComparisonShape (A*t))
        (laplaceComparisonSlope (A*t)) t (s.mass t)))
    (hj : ∀ᵐt∂volume.restrict (Ioo a b),0 < j t)
    (hrange : ∀ᵐt∂volume.restrict (Ioo a b),s.mass t∈Icc a b)
    (hclosure : ∀ᵐt∂volume.restrict (Ioo a b),
      g (s.mass t)=(L*laplaceComparisonShape (A*t))/T*(s.mass t-t)) :
    ComparisonVirtualGapData g a b := by
  apply P.toGap
  right
  refine ⟨s.mass,fun t=>(L*laplaceComparisonShape (A*t))/T,?_⟩
  filter_upwards [hj,hrange,hclosure,ae_restrict_mem measurableSet_Ioo] with t hjt hst hct ht
  exact ⟨hst,div_pos (mul_pos hL (laplaceComparisonShape_pos _)) hT,hct,
    comparison_bounded_scaled_principal_sign hL hjt (ha.trans_lt ht.1) (s.nonneg t)⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
