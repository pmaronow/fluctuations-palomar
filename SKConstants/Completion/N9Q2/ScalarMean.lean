module

public import SKConstants.ParisiActualRestartCoordinate
public import SKConstants.ParisiRestartObservable

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology

namespace SKConstants.Completion.N9Q2
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport
variable {Ω : Type*} [MeasurableSpace Ω]

theorem restart_magnetization_mean_pre (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a v : ℝ≥0) (hav : a+v ≤ parisiEquilibriumPhysicalEndpoint β) (x : ℝ) :
    (∫ w, actualParisiFullMagnetization β (a+v)
      (actualParisiRestartField W β a x v w) ∂W.law) =
      actualParisiFullMagnetization β a x := by
  letI := W.isProbability
  let α := cdf (parisiEquilibriumMeasure β : Measure ℝ)
  have ha : ∀ z, α z ∈ Icc (0 : ℝ) 1 := fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 : α 1 = 1 := supported_probability_cdf_one (parisiEquilibriumMeasure β)
    (parisiEquilibriumMeasure_upstream_spec β).1
  have hb : β ≠ 0 := (zero_lt_one.trans hβ).ne'
  let T := (parisiEquilibriumSupportEndpoint β+1)/2
  have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have hT0 : 0 ≤ T := by dsimp [T]; linarith [hQ.1]
  have hT1 : T < 1 := by dsimp [T]; linarith [hQ.2]
  have hQT : parisiEquilibriumSupportEndpoint β < T := by dsimp [T]; linarith [hQ.2]
  have htime : ((a : ℝ)+(v : ℝ))/β^2 < T := by
    have H : ((a+v : ℝ≥0) : ℝ) ≤ β^2*parisiEquilibriumSupportEndpoint β := by
      simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ] using NNReal.coe_le_coe.mpr hav
    have HD : ((a : ℝ)+(v : ℝ))/β^2 ≤ parisiEquilibriumSupportEndpoint β :=
      (div_le_iff₀ (sq_pos_of_ne_zero hb)).mpr (by simpa only [NNReal.coe_add,mul_comm] using H)
    exact HD.trans_lt hQT
  have H := physicalCDFGradient_restart_integral_eq_zero W β α ha h1 hb hT0 hT1
    a a.coe_nonneg x v htime
  have haV : a ≤ parisiEquilibriumPhysicalEndpoint β := (le_self_add : a ≤ a+v).trans hav
  have hm1 : compactCDFJet β α T 0 (((a : ℝ)+(v : ℝ))/β^2) =
      actualParisiFullMagnetization β (a+v) := by
    funext y
    simpa only [NNReal.coe_add] using
      (actualParisiFullMagnetization_eq_compact_before_support β hβ hQT hT1.le (a+v) hav y).symm
  have hm0 : compactCDFJet β α T 0 ((a : ℝ)/β^2) = actualParisiFullMagnetization β a :=
    (funext (actualParisiFullMagnetization_eq_compact_before_support β hβ hQT hT1.le a haV)).symm
  rw [hm1,hm0] at H
  change (∫ w, actualParisiFullMagnetization β (a+v)
    (actualParisiRestartField W β a x v w)-actualParisiFullMagnetization β a x ∂W.law) = 0 at H
  have hY : Measurable (actualParisiRestartField W β a x v) :=
    measurable_const.add
      ((SKConstants.BoundedLipschitzDrift.translated (actualParisiFullScalarDrift β) a x).solution_measurable W v)
  have hm : Measurable (fun w => actualParisiFullMagnetization β (a+v)
      (actualParisiRestartField W β a x v w)) :=
    (((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable).comp hY
  have hi := Integrable.of_bound (μ := W.law) hm.aestronglyMeasurable 1
    (ae_of_all _ (fun w => (actualParisiFullMagnetization_curvature_bounds β _ _).1))
  rw [integral_sub hi (integrable_const _),integral_const,probReal_univ,one_smul] at H
  exact sub_eq_zero.mp H

theorem restart_magnetization_mean_post (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a v : ℝ≥0) (ha : parisiEquilibriumPhysicalEndpoint β ≤ a) (x : ℝ) :
    (∫ w, actualParisiFullMagnetization β (a+v)
      (actualParisiRestartField W β a x v w) ∂W.law) =
      actualParisiFullMagnetization β a x := by
  have haR : β^2*parisiEquilibriumSupportEndpoint β ≤ (a : ℝ) := by
    simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ] using NNReal.coe_le_coe.mpr ha
  have havR : β^2*parisiEquilibriumSupportEndpoint β ≤ (a : ℝ)+(v : ℝ) := by
    linarith [v.coe_nonneg]
  rw [actualParisiFullMagnetization_eq_tanh_after_support β hβ _ haR,
    actualParisiFullMagnetization_eq_tanh_after_support β hβ _ havR]
  refine (integral_congr_ae ?_).trans (scalarTanhPicard_endpoint_mean W x v)
  filter_upwards [actualParisiRestartField_eq_tanh_picard_after_support W β hβ a v ha x]
    with w hw
  rw [hw]

theorem restart_magnetization_mean_split (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a d e : ℝ≥0) (ha : parisiEquilibriumPhysicalEndpoint β ≤ a+d) (x : ℝ) :
    (∫ w, actualParisiFullMagnetization β (a+(d+e))
      (actualParisiRestartField W β a x (d+e) w) ∂W.law) =
    ∫ w, actualParisiFullMagnetization β (a+d)
      (actualParisiRestartField W β a x d w) ∂W.law := by
  let b := SKConstants.BoundedLipschitzDrift.translated (actualParisiFullScalarDrift β) a x
  let φ : ℝ → ℝ := fun y => actualParisiFullMagnetization β (a+(d+e)) (x+y)
  have hφ : Measurable φ := ((continuous_actualParisiFullMagnetization β).comp
    (continuous_const.prodMk (continuous_const.add continuous_id))).measurable
  have hφB (y : ℝ) : |φ y| ≤ 1 := (actualParisiFullMagnetization_curvature_bounds β _ _).1
  have H := boundedDrift_restart_observable_test W b d e (fun _ => 1) measurable_const 1
    (fun _ => by norm_num) φ hφ 1 hφB
  simp only [one_mul] at H
  have inner (past : ScalarContinuousPath d) :
      (∫ w, φ (past ⟨d,d.coe_nonneg,le_rfl⟩+
        (SKConstants.BoundedLipschitzDrift.translated b d
          (past ⟨d,d.coe_nonneg,le_rfl⟩)).solution W.driver e w) ∂W.law) =
        actualParisiFullMagnetization β (a+d) (x+past ⟨d,d.coe_nonneg,le_rfl⟩) := by
    let y := past ⟨d,d.coe_nonneg,le_rfl⟩
    have hs (w : Ω) :
        (SKConstants.BoundedLipschitzDrift.translated b d y).solution W.driver e w =
        (SKConstants.BoundedLipschitzDrift.translated (actualParisiFullScalarDrift β)
          (a+d) (x+y)).solution W.driver e w := by
      apply SKConstants.BoundedLipschitzDrift.solution_congr_nonneg_drift
      intro r hr z
      change (actualParisiFullScalarDrift β).f ((a : ℝ)+((d : ℝ)+r)) (x+(y+z)) =
        (actualParisiFullScalarDrift β).f (((a+d : ℝ≥0) : ℝ)+r) ((x+y)+z)
      simp only [NNReal.coe_add,add_assoc]
    have heq (w : Ω) : φ (y+
        (SKConstants.BoundedLipschitzDrift.translated b d y).solution W.driver e w) =
        actualParisiFullMagnetization β ((a+d)+e)
          (actualParisiRestartField W β (a+d) (x+y) e w) := by
      dsimp only [φ,actualParisiRestartField]
      rw [hs]
      simp only [NNReal.coe_add,add_assoc]
    change (∫ w, φ (y+(SKConstants.BoundedLipschitzDrift.translated b d y).solution
      W.driver e w) ∂W.law) = _
    simp_rw [heq]
    exact restart_magnetization_mean_post W β hβ (a+d) e ha (x+y)
  change (∫ w, φ (b.solution W.driver (d+e) w) ∂W.law) = _
  rw [H]
  simp_rw [inner]
  let ψ : ℝ → ℝ := fun y => actualParisiFullMagnetization β (a+d) (x+y)
  have hψ : Measurable ψ := ((continuous_actualParisiFullMagnetization β).comp
    (continuous_const.prodMk (continuous_const.add continuous_id))).measurable
  simpa only [one_mul,ψ,b,actualParisiRestartField] using
    (boundedDrift_past_observable_integral W b d (fun _ => 1) measurable_const ψ hψ).symm

theorem restart_magnetization_mean (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a v : ℝ≥0) (x : ℝ) :
    (∫ w, actualParisiFullMagnetization β (a+v)
      (actualParisiRestartField W β a x v w) ∂W.law) =
      actualParisiFullMagnetization β a x := by
  let V := parisiEquilibriumPhysicalEndpoint β
  by_cases hav : a+v ≤ V
  · exact restart_magnetization_mean_pre W β hβ a v hav x
  by_cases ha : V ≤ a
  · exact restart_magnetization_mean_post W β hβ a v ha x
  have haV : a ≤ V := (le_of_not_ge ha)
  have hVa : V ≤ a+v := (le_of_not_ge hav)
  let d := V-a
  let e := a+v-V
  have had : a+d = V := add_tsub_cancel_of_le haV
  have hVe : V+e = a+v := add_tsub_cancel_of_le hVa
  have hde : d+e = v := by
    apply add_left_cancel (a := a)
    rw [← add_assoc,had,hVe]
  rw [← hde]
  simpa only [NNReal.coe_add] using
    (restart_magnetization_mean_split W β hβ a d e (by rw [had]) x).trans
      (restart_magnetization_mean_pre W β hβ a d (by rw [had]) x)

end SKConstants.Completion.N9Q2
