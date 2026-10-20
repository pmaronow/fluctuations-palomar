module

public import ComparisonActualHighWallRadiusScalarIntegrability
public import ComparisonActualHighWallStarPreparatory
public import ComparisonActualHighWallVirtualControl
public import ComparisonStrengthProfileCompactness

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology
set_option maxHeartbeats 8000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def actualScaledRadiusSpin
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (t : ℝ) : ℝ :=
  orderedPathS (n+1) M.bf M.hf (M.alpha.val.val (M.xs*t))/M.xs

def actualScaledPrincipalGradient
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (t : ℝ) : ℝ :=
  comparisonScaledStationarity
    (laplaceComparisonStrength M.data.d (M.data.d^2) (M.xs*t)/M.xs^2)
    (comparisonLogSlope (laplaceComparisonStrength M.data.d (M.data.d^2)) (M.xs*t))
    t (M.actualScaledRadiusSpin t)

theorem full_mass_moments
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    MonotoneOn (orderedPathS (n+1) M.bf M.hf) (Icc (0:ℝ) 1) ∧
    MonotoneOn (orderedPathB (n+1) M.bf M.hf) (Icc (0:ℝ) 1) ∧
    ∀u∈Icc (0:ℝ) 1,
      orderedPathS (n+1) M.bf M.hf u∈Icc (0:ℝ) 1 ∧
      (orderedPathS (n+1) M.bf M.hf u)^2≤orderedPathB (n+1) M.bf M.hf u ∧
      orderedPathB (n+1) M.bf M.hf u≤1 := by
  have hb (u : ℝ) (hu:u∈Icc (0:ℝ) 1) :
      orderedPathS (n+1) M.bf M.hf u∈Icc (0:ℝ) 1 ∧
      (orderedPathS (n+1) M.bf M.hf u)^2≤orderedPathB (n+1) M.bf M.hf u ∧
      orderedPathB (n+1) M.bf M.hf u≤1 := by
    by_cases hz:u=0
    · subst u
      simp only [orderedPathS,orderedPathB,orderedPathPair_zero]
      norm_num
    · have H:=orderedPath_SK_bounds (n+1) M.data.hn M.bf M.hf
        (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)
        ⟨lt_of_le_of_ne hu.1 (Ne.symm hz),hu.2⟩
      exact ⟨⟨H.1,H.2.1⟩,H.2.2⟩
  refine ⟨M.mass_mean_monotone,?_,hb⟩
  intro u hu v hv huv
  by_cases hz:u=0
  · subst u
    simpa only [orderedPathB,orderedPathPair_zero] using
      (sq_nonneg (orderedPathS (n+1) M.bf M.hf v)).trans (hb v hv).2.1
  · have hp:0<u:=lt_of_le_of_ne hu.1 (Ne.symm hz)
    exact (orderedPath_SK_monotone (n+1) M.data.hn M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)).2
      ⟨hp,hu.2⟩ ⟨hp.trans_le huv,hv.2⟩ huv

theorem full_radius_moments
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    Monotone M.radiusS ∧ Monotone M.radiusB ∧
    ∀r,M.radiusS r∈Icc (0:ℝ) 1 ∧
      (M.radiusS r)^2≤M.radiusB r ∧ M.radiusB r≤1 := by
  have H:=M.full_mass_moments
  refine ⟨fun r t hrt=>H.1 (M.alpha.val.property.1 _) (M.alpha.val.property.1 _)
      (M.alpha.val.property.2 hrt),
    fun r t hrt=>H.2.1 (M.alpha.val.property.1 _) (M.alpha.val.property.1 _)
      (M.alpha.val.property.2 hrt),
    fun r=>H.2.2 _ (M.alpha.val.property.1 _)⟩

theorem actual_scaled_radius_spin_monotone
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    Monotone M.actualScaledRadiusSpin := by
  intro s t hst
  exact div_le_div_of_nonneg_right
    (M.mass_mean_monotone (M.alpha.val.property.1 _) (M.alpha.val.property.1 _)
      (M.alpha.val.property.2 (mul_le_mul_of_nonneg_left hst M.hxs.le))) M.hxs.le

theorem actual_scaled_principal_gradient_measurable
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    Measurable M.actualScaledPrincipalGradient := by
  have hh := (laplaceComparisonStrength_contDiff M.data.d (M.data.d^2)).continuous.measurable
  have hp : Measurable (fun t=>comparisonLogSlope
      (laplaceComparisonStrength M.data.d (M.data.d^2)) (M.xs*t)) := by
    simp_rw [comparison_slope_scaled_parameter_identity M.data.hd.ne' (sq_pos_of_pos M.data.hd).ne']
    exact comparison_shape_slope_continuous.measurable.comp (measurable_const.mul measurable_id)
  have hs := M.actual_scaled_radius_spin_monotone.measurable
  unfold actualScaledPrincipalGradient comparisonScaledStationarity
  exact (hh.comp (measurable_const.mul measurable_id) |>.div_const _).mul
    ((((measurable_const.sub hp).mul measurable_id).sub
      (((measurable_const.sub hp).const_mul 2).mul hs)).sub
      ((hp.mul (hs.pow_const 2)).div measurable_id))

theorem actual_scaled_radius_defect_integrable
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {a b : ℝ} :
    IntegrableOn (fun t=>M.wallRadiusPointDefect (M.xs*t)/M.xs^2) (Icc a b) := by
  have H:=M.full_radius_moments
  have hB : MonotoneOn (fun t=>orderedPathB (n+1) M.bf M.hf
      (M.alpha.val.val (M.xs*t))) (Icc a b) := by
    intro s hs t ht hst
    exact H.2.1 (mul_le_mul_of_nonneg_left hst M.hxs.le)
  have hS : MonotoneOn (fun t=>(orderedPathS (n+1) M.bf M.hf
      (M.alpha.val.val (M.xs*t)))^2) (Icc a b) := by
    intro s hs t ht hst
    exact pow_le_pow_left₀ ((H.2.2 _).1.1)
      (H.1 (mul_le_mul_of_nonneg_left hst M.hxs.le)) 2
  exact ((hB.integrableOn_isCompact (μ:=volume) isCompact_Icc).sub
    (hS.integrableOn_isCompact (μ:=volume) isCompact_Icc)).div_const _

theorem actual_scaled_gradient_error_bound
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {a b K : ℝ} (ha : 0 < a) (hK : 0 ≤ K)
    (hwork : laplaceComparisonStrength M.data.d (M.data.d^2) M.xs/M.xs^2 ≤ K)
    {t : ℝ} (ht : t∈Icc a b) :
    |M.actualVirtualScaledGradient t-M.actualScaledPrincipalGradient t| ≤
      ((K+1)/a)*(M.wallRadiusPointDefect (M.xs*t)/M.xs^2) := by
  have hstrength : laplaceComparisonStrength M.data.d (M.data.d^2) (M.xs*t)/M.xs^2 ≤ K+1 :=
    (div_le_div_of_nonneg_right (laplaceComparisonStrength_le M.data.d (sq_pos_of_pos M.data.hd).le _)
      (sq_nonneg _)).trans
      (comparison_zero_strength_bound_of_working M.data.hd (sq_pos_of_pos M.data.hd).le M.hxs le_rfl hK hwork)
  have hD := (M.full_radius_moments.2.2 (M.xs*t)).2.1
  exact laplace_gradient_scaled_error_bound M.alpha.val.val
    (orderedPathS (n+1) M.bf M.hf) (orderedPathB (n+1) M.bf M.hf)
    M.data.hd.ne' (sq_pos_of_pos M.data.hd) M.hxs ha ht.1 hstrength
      (by simpa only [radiusS,radiusB] using hD)

theorem actual_scaled_gradient_aestronglyMeasurable
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {a b : ℝ} (ha : 0 < a) :
    AEStronglyMeasurable M.actualVirtualScaledGradient (volume.restrict (Icc a b)) := by
  have hDi := M.actual_scaled_radius_defect_integrable (a:=a) (b:=b)
  have hcoef : Measurable (fun t=>
      (laplaceComparisonStrength M.data.d (M.data.d^2) (M.xs*t)/M.xs^2)*
        comparisonLogSlope (laplaceComparisonStrength M.data.d (M.data.d^2)) (M.xs*t)/t) := by
    have hh := (laplaceComparisonStrength_contDiff M.data.d (M.data.d^2)).continuous.measurable
    have hp : Measurable (fun t=>comparisonLogSlope
        (laplaceComparisonStrength M.data.d (M.data.d^2)) (M.xs*t)) := by
      simp_rw [comparison_slope_scaled_parameter_identity M.data.hd.ne' (sq_pos_of_pos M.data.hd).ne']
      exact comparison_shape_slope_continuous.measurable.comp (measurable_const.mul measurable_id)
    exact (((hh.comp (measurable_const.mul measurable_id)).div_const _).mul hp).div measurable_id
  apply (M.actual_scaled_principal_gradient_measurable.aestronglyMeasurable.sub
    (hcoef.aestronglyMeasurable.mul hDi.aestronglyMeasurable)).congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (comparison_gradient_scaled_exact (laplaceComparisonStrength M.data.d (M.data.d^2))
    M.alpha.val.val (orderedPathS (n+1) M.bf M.hf) (orderedPathB (n+1) M.bf M.hf)
    M.hxs.ne' (ha.trans_le ht.1).ne'
    (laplaceComparisonStrength_pos M.data.d (sq_pos_of_pos M.data.hd) _).ne').symm

theorem actual_scaled_gradient_integrable_of_principal
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {a b K : ℝ} (ha : 0 < a) (hK : 0 ≤ K)
    (hwork : laplaceComparisonStrength M.data.d (M.data.d^2) M.xs/M.xs^2 ≤ K)
    (hPi : IntegrableOn M.actualScaledPrincipalGradient (Icc a b)) :
    IntegrableOn M.actualVirtualScaledGradient (Icc a b) := by
  apply (hPi.abs.add ((M.actual_scaled_radius_defect_integrable (a:=a) (b:=b)).const_mul
    ((K+1)/a))).mono' (M.actual_scaled_gradient_aestronglyMeasurable ha)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have he := M.actual_scaled_gradient_error_bound ha hK hwork ht
  have htri := abs_sub_le (M.actualVirtualScaledGradient t) (M.actualScaledPrincipalGradient t) 0
  simp only [sub_zero] at htri
  dsimp only [Pi.add_apply]
  rw [Real.norm_eq_abs]
  linarith only [he,htri]

theorem actual_scaled_principal_gradient_integrable
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {a b : ℝ} (ha : 0 < a) :
    IntegrableOn M.actualScaledPrincipalGradient (Icc a b) := by
  let K:=max ((M.data.d^2)/M.xs^2) (1/M.xs)
  have H:=M.full_radius_moments
  apply Integrable.of_bound M.actual_scaled_principal_gradient_measurable.aestronglyMeasurable
    (K*(2*b+2*K+K^2/a))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  have hs:= (H.2.2 (M.xs*t)).1
  have hp:=laplaceComparisonStrength_logSlope_mem M.data.hd.ne' (sq_pos_of_pos M.data.hd).ne' (M.xs*t)
  apply comparison_scaled_stationarity_bound ha ht
  · exact ⟨div_nonneg (laplaceComparisonStrength_pos _ (sq_pos_of_pos M.data.hd) _).le (sq_nonneg _),
      (div_le_div_of_nonneg_right (laplaceComparisonStrength_le _ (sq_pos_of_pos M.data.hd).le _)
        (sq_nonneg _)).trans (le_max_left _ _)⟩
  · exact ⟨hp.1,hp.2.le⟩
  · exact ⟨div_nonneg hs.1 M.hxs.le,
      (div_le_div_of_nonneg_right hs.2 M.hxs.le).trans (le_max_right _ _)⟩

theorem actual_scaled_gradient_integrable
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {a b : ℝ} (ha : 0 < a) :
    IntegrableOn M.actualVirtualScaledGradient (Icc a b) := by
  let K:=(M.data.d^2)/M.xs^2
  have hK : 0 ≤ K := div_nonneg (sq_pos_of_pos M.data.hd).le (sq_nonneg _)
  exact M.actual_scaled_gradient_integrable_of_principal ha hK
    (div_le_div_of_nonneg_right (laplaceComparisonStrength_le _ (sq_pos_of_pos M.data.hd).le _)
      (sq_nonneg _)) (M.actual_scaled_principal_gradient_integrable ha)

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
