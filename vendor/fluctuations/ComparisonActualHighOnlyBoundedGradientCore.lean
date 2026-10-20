module

public import ComparisonActualHighOnlyRadiusSingleCutIntegral
public import ComparisonActualHighOnlyAnalyticBasics
public import ComparisonActualHighOnlyVirtualControl
public import ComparisonStrengthProfileCompactness

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 8000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def actualScaledRadiusSpin
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (t : ℝ) : ℝ :=
  orderedPathS (n+1) M.bf M.hf (M.alpha.val.val (M.xs*t))/M.xs

def actualScaledPrincipalGradient
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (t : ℝ) : ℝ :=
  comparisonScaledStationarity
    (laplaceComparisonStrength M.context.d M.lam (M.xs*t)/M.xs^2)
    (comparisonLogSlope (laplaceComparisonStrength M.context.d M.lam) (M.xs*t))
    t (M.actualScaledRadiusSpin t)

theorem actual_scaled_radius_spin_monotone
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    Monotone M.actualScaledRadiusSpin := by
  intro s t hst
  exact div_le_div_of_nonneg_right
    (M.mass_mean_monotone (M.alpha.val.property.1 _) (M.alpha.val.property.1 _)
      (M.alpha.val.property.2 (mul_le_mul_of_nonneg_left hst M.hxs.le))) M.hxs.le

theorem actual_scaled_principal_gradient_measurable
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    Measurable M.actualScaledPrincipalGradient := by
  have hh := (laplaceComparisonStrength_contDiff M.context.d M.lam).continuous.measurable
  have hp : Measurable (fun t=>comparisonLogSlope
      (laplaceComparisonStrength M.context.d M.lam) (M.xs*t)) := by
    simp_rw [comparison_slope_scaled_parameter_identity M.context.hd.ne' M.hlam.ne']
    exact comparison_shape_slope_continuous.measurable.comp (measurable_const.mul measurable_id)
  have hs := M.actual_scaled_radius_spin_monotone.measurable
  unfold actualScaledPrincipalGradient comparisonScaledStationarity
  exact (hh.comp (measurable_const.mul measurable_id) |>.div_const _).mul
    ((((measurable_const.sub hp).mul measurable_id).sub
      (((measurable_const.sub hp).const_mul 2).mul hs)).sub
      ((hp.mul (hs.pow_const 2)).div measurable_id))

theorem actual_scaled_radius_defect_integrable
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {a b : ℝ} (ha : 0 ≤ a) (hb : M.xs*b ≤ 1) :
    IntegrableOn (fun t=>M.cavityRadiusPointDefect (M.xs*t)/M.xs^2) (Icc a b) := by
  have H:=M.radius_moments
  have hphys t (ht:t∈Icc a b) : M.xs*t∈Icc (0:ℝ) 1 :=
    ⟨mul_nonneg M.hxs.le (ha.trans ht.1),
      (mul_le_mul_of_nonneg_left ht.2 M.hxs.le).trans hb⟩
  have hB : MonotoneOn (fun t=>orderedPathB (n+1) M.bf M.hf
      (M.alpha.val.val (M.xs*t))) (Icc a b) := by
    intro s hs t ht hst
    exact H.2.1 (hphys s hs) (hphys t ht) (mul_le_mul_of_nonneg_left hst M.hxs.le)
  have hS : MonotoneOn (fun t=>(orderedPathS (n+1) M.bf M.hf
      (M.alpha.val.val (M.xs*t)))^2) (Icc a b) := by
    intro s hs t ht hst
    exact pow_le_pow_left₀ ((H.2.2 _ (hphys s hs)).1.1)
      (H.1 (hphys s hs) (hphys t ht) (mul_le_mul_of_nonneg_left hst M.hxs.le)) 2
  exact ((hB.integrableOn_isCompact (μ:=volume) isCompact_Icc).sub
    (hS.integrableOn_isCompact (μ:=volume) isCompact_Icc)).div_const _

theorem actual_scaled_gradient_error_bound
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {a b K : ℝ} (ha : 0 < a) (hb : M.xs*b ≤ 1) (hK : 0 ≤ K)
    (hwork : laplaceComparisonStrength M.context.d M.lam M.xs/M.xs^2 ≤ K)
    {t : ℝ} (ht : t∈Icc a b) :
    |M.actualVirtualScaledGradient t-M.actualScaledPrincipalGradient t| ≤
      ((K+1)/a)*(M.cavityRadiusPointDefect (M.xs*t)/M.xs^2) := by
  have hstrength : laplaceComparisonStrength M.context.d M.lam (M.xs*t)/M.xs^2 ≤ K+1 :=
    (div_le_div_of_nonneg_right (laplaceComparisonStrength_le M.context.d M.hlam.le _)
      (sq_nonneg _)).trans
      (comparison_zero_strength_bound_of_working M.context.hd M.hlam.le M.hxs M.hld hK hwork)
  have hD := M.cavityRadiusPointDefect_nonneg
    ⟨mul_nonneg M.hxs.le (ha.le.trans ht.1),
      (mul_le_mul_of_nonneg_left ht.2 M.hxs.le).trans hb⟩
  exact laplace_gradient_scaled_error_bound M.alpha.val.val
    (orderedPathS (n+1) M.bf M.hf) (orderedPathB (n+1) M.bf M.hf)
    M.context.hd.ne' M.hlam M.hxs ha ht.1 hstrength (sub_nonneg.mp hD)

theorem actual_scaled_gradient_aestronglyMeasurable
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {a b : ℝ} (ha : 0 < a) (hb : M.xs*b ≤ 1) :
    AEStronglyMeasurable M.actualVirtualScaledGradient (volume.restrict (Icc a b)) := by
  have hDi := M.actual_scaled_radius_defect_integrable ha.le hb
  have hcoef : Measurable (fun t=>
      (laplaceComparisonStrength M.context.d M.lam (M.xs*t)/M.xs^2)*
        comparisonLogSlope (laplaceComparisonStrength M.context.d M.lam) (M.xs*t)/t) := by
    have hh := (laplaceComparisonStrength_contDiff M.context.d M.lam).continuous.measurable
    have hp : Measurable (fun t=>comparisonLogSlope
        (laplaceComparisonStrength M.context.d M.lam) (M.xs*t)) := by
      simp_rw [comparison_slope_scaled_parameter_identity M.context.hd.ne' M.hlam.ne']
      exact comparison_shape_slope_continuous.measurable.comp (measurable_const.mul measurable_id)
    exact (((hh.comp (measurable_const.mul measurable_id)).div_const _).mul hp).div measurable_id
  apply (M.actual_scaled_principal_gradient_measurable.aestronglyMeasurable.sub
    (hcoef.aestronglyMeasurable.mul hDi.aestronglyMeasurable)).congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (comparison_gradient_scaled_exact (laplaceComparisonStrength M.context.d M.lam)
    M.alpha.val.val (orderedPathS (n+1) M.bf M.hf) (orderedPathB (n+1) M.bf M.hf)
    M.hxs.ne' (ha.trans_le ht.1).ne'
    (laplaceComparisonStrength_pos M.context.d M.hlam _).ne').symm

theorem actual_scaled_gradient_integrable_of_principal
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {a b K : ℝ} (ha : 0 < a) (hb : M.xs*b ≤ 1) (hK : 0 ≤ K)
    (hwork : laplaceComparisonStrength M.context.d M.lam M.xs/M.xs^2 ≤ K)
    (hPi : IntegrableOn M.actualScaledPrincipalGradient (Icc a b)) :
    IntegrableOn M.actualVirtualScaledGradient (Icc a b) := by
  apply (hPi.abs.add ((M.actual_scaled_radius_defect_integrable ha.le hb).const_mul
    ((K+1)/a))).mono' (M.actual_scaled_gradient_aestronglyMeasurable ha hb)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have he := M.actual_scaled_gradient_error_bound ha hb hK hwork ht
  have htri := abs_sub_le (M.actualVirtualScaledGradient t) (M.actualScaledPrincipalGradient t) 0
  simp only [sub_zero] at htri
  dsimp only [Pi.add_apply]
  rw [Real.norm_eq_abs]
  linarith only [he,htri]

theorem actual_scaled_principal_gradient_integrable
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {a b : ℝ} (ha : 0 < a) (hb : M.xs*b ≤ 1) :
    IntegrableOn M.actualScaledPrincipalGradient (Icc a b) := by
  let K:=max (M.lam/M.xs^2) (1/M.xs)
  have H:=M.radius_moments
  apply Integrable.of_bound M.actual_scaled_principal_gradient_measurable.aestronglyMeasurable
    (K*(2*b+2*K+K^2/a))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hphys : M.xs*t∈Icc (0:ℝ) 1 :=
    ⟨mul_nonneg M.hxs.le (ha.le.trans ht.1),
      (mul_le_mul_of_nonneg_left ht.2 M.hxs.le).trans hb⟩
  have hs:= (H.2.2 _ hphys).1
  have hp:=laplaceComparisonStrength_logSlope_mem M.context.hd.ne' M.hlam.ne' (M.xs*t)
  apply comparison_scaled_stationarity_bound ha ht
  · exact ⟨div_nonneg (laplaceComparisonStrength_pos _ M.hlam _).le (sq_nonneg _),
      (div_le_div_of_nonneg_right (laplaceComparisonStrength_le _ M.hlam.le _)
        (sq_nonneg _)).trans (le_max_left _ _)⟩
  · exact ⟨hp.1,hp.2.le⟩
  · exact ⟨div_nonneg hs.1 M.hxs.le,
      (div_le_div_of_nonneg_right hs.2 M.hxs.le).trans (le_max_right _ _)⟩

theorem actual_scaled_gradient_integrable
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {a b : ℝ} (ha : 0 < a) (hb : M.xs*b ≤ 1) :
    IntegrableOn M.actualVirtualScaledGradient (Icc a b) := by
  let K:=M.lam/M.xs^2
  have hK : 0 ≤ K := div_nonneg M.hlam.le (sq_nonneg _)
  exact M.actual_scaled_gradient_integrable_of_principal ha hb hK
    (div_le_div_of_nonneg_right (laplaceComparisonStrength_le _ M.hlam.le _)
      (sq_nonneg _)) (M.actual_scaled_principal_gradient_integrable ha hb)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
