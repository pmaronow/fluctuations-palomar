module

public import SKConstants.ParisiRestartCoordinateExpectation
public import SKConstants.ParisiTanhCoordinateExpectation
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]

def actualParisiRestartField (W : BrownianSystem Ω) (β : ℝ) (a : ℝ≥0) (x0 : ℝ)
    (v : ℝ≥0) (w : Ω) : ℝ :=
  x0+(SKConstants.BoundedLipschitzDrift.translated (actualParisiFullScalarDrift β) a x0).solution W.driver v w

lemma actualParisiFullCurvature_eq_compact_before_support (β : ℝ) (hβ : 1 < β)
    {T : ℝ} (hQT : parisiEquilibriumSupportEndpoint β < T) (hT0 : 0 ≤ T) (hT1 : T < 1)
    (t : ℝ≥0) (ht : t ≤ parisiEquilibriumPhysicalEndpoint β) (x : ℝ) :
    actualParisiFullCurvature β t x=
      compactCDFJet β (cdf (parisiEquilibriumMeasure β : Measure ℝ)) T 1 ((t:ℝ)/β^2) x := by
  let α := cdf (parisiEquilibriumMeasure β:Measure ℝ)
  have ha : ∀ z,α z∈Icc (0:ℝ) 1 := fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 : α 1=1 := supported_probability_cdf_one (parisiEquilibriumMeasure β)
    (parisiEquilibriumMeasure_upstream_spec β).1
  have hm : actualParisiFullMagnetization β t=compactCDFJet β α T 0 ((t:ℝ)/β^2) :=
    funext (actualParisiFullMagnetization_eq_compact_before_support β hβ hQT hT1.le t ht)
  have H := congrArg (fun f : ℝ → ℝ => deriv f x) hm
  rw [(actualParisiFullMagnetization_hasDerivAt β t x).deriv,
    deriv_compactCDFJet β α ha h1 (zero_lt_one.trans hβ).ne' hT0 hT1] at H
  exact H

lemma actualParisiCoordinateRate_eq_before_support (β : ℝ) (hβ : 1 < β)
    {T : ℝ} (hQT : parisiEquilibriumSupportEndpoint β < T) (hT0 : 0 ≤ T) (hT1 : T < 1)
    (t : ℝ≥0) (ht : t ≤ parisiEquilibriumPhysicalEndpoint β) (x : ℝ) :
    physicalCDFCoordinateRate β (cdf (parisiEquilibriumMeasure β:Measure ℝ)) T t x=
      actualParisiFullCurvature β t x+actualParisiFullMagnetization β t x*(actualParisiFullScalarDrift β).f t x := by
  let α := cdf (parisiEquilibriumMeasure β:Measure ℝ)
  have ha : ∀ z,α z∈Icc (0:ℝ) 1 := fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 : α 1=1 := supported_probability_cdf_one (parisiEquilibriumMeasure β)
    (parisiEquilibriumMeasure_upstream_spec β).1
  have hb : 0 < β^2 := sq_pos_of_pos (zero_lt_one.trans hβ)
  have htq : (t:ℝ)/β^2∈Icc (0:ℝ) T := by
    refine ⟨div_nonneg t.coe_nonneg hb.le,?_⟩
    have H : (t:ℝ)/β^2≤parisiEquilibriumSupportEndpoint β := by
      apply (div_le_iff₀ hb).mpr
      simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ,mul_comm] using NNReal.coe_le_coe.mpr ht
    exact H.trans hQT.le
  have hd : (actualParisiFullScalarDrift β).f t x=physicalCDFCompactDrift β α T t x :=
    finiteTemperatureCDFDrift_eq_compact β α ha h1 (zero_lt_one.trans hβ).ne' hT1.le htq x
  rw [actualParisiFullCurvature_eq_compact_before_support β hβ hQT hT0 hT1 t ht x,
    actualParisiFullMagnetization_eq_compact_before_support β hβ hQT hT1.le t ht x,hd]
  unfold physicalCDFCoordinateRate physicalCDFCompactDrift
  ring

theorem actualParisiFullProcess_pre_restartCoordinate_integral
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a v : ℝ≥0)
    (hav : a+v ≤ parisiEquilibriumPhysicalEndpoint β) (x0 : ℝ) :
    (∫ w,actualParisiRestartField W β a x0 v w*
      actualParisiFullMagnetization β (a+v) (actualParisiRestartField W β a x0 v w) ∂W.law)-
      x0*actualParisiFullMagnetization β a x0 =
    ∫ u in 0..(v:ℝ), ∫ w,
      actualParisiFullCurvature β (a+u.toNNReal) (actualParisiRestartField W β a x0 u.toNNReal w)+
      actualParisiFullMagnetization β (a+u.toNNReal) (actualParisiRestartField W β a x0 u.toNNReal w)*
        (actualParisiFullScalarDrift β).f (a+u.toNNReal) (actualParisiRestartField W β a x0 u.toNNReal w) ∂W.law := by
  let α := cdf (parisiEquilibriumMeasure β:Measure ℝ)
  have ha : ∀ z,α z∈Icc (0:ℝ) 1 := fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩
  have h1 : α 1=1 := supported_probability_cdf_one (parisiEquilibriumMeasure β)
    (parisiEquilibriumMeasure_upstream_spec β).1
  have hb : β≠0 := (zero_lt_one.trans hβ).ne'
  let T := (parisiEquilibriumSupportEndpoint β+1)/2
  have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have hT0 : 0 ≤ T := by dsimp [T]; linarith [hQ.1]
  have hT1 : T < 1 := by dsimp [T]; linarith [hQ.2]
  have hQT : parisiEquilibriumSupportEndpoint β<T := by dsimp [T]; linarith [hQ.2]
  have htime : ((a:ℝ)+(v:ℝ))/β^2<T := by
    have H : ((a+v:ℝ≥0):ℝ)≤β^2*parisiEquilibriumSupportEndpoint β := by
      simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ] using NNReal.coe_le_coe.mpr hav
    have HD : ((a:ℝ)+(v:ℝ))/β^2≤parisiEquilibriumSupportEndpoint β :=
      (div_le_iff₀ (sq_pos_of_ne_zero hb)).mpr (by simpa only [NNReal.coe_add,mul_comm] using H)
    exact HD.trans_lt hQT
  have H := physicalCDFRestartCoordinateExpected_integral W β α ha h1 hb hT0 hT1
    a x0 a.coe_nonneg v v.coe_nonneg htime
  have haV : a ≤ parisiEquilibriumPhysicalEndpoint β := (le_add_of_nonneg_right bot_le).trans hav
  have hm1 : compactCDFJet β α T 0 (((a:ℝ)+(v:ℝ))/β^2)=actualParisiFullMagnetization β (a+v) := by
    funext x
    simpa only [NNReal.coe_add] using
      (actualParisiFullMagnetization_eq_compact_before_support β hβ hQT hT1.le (a+v) hav x).symm
  have hm0 : compactCDFJet β α T 0 ((a:ℝ)/β^2)=actualParisiFullMagnetization β a :=
    (funext (actualParisiFullMagnetization_eq_compact_before_support β hβ hQT hT1.le a haV)).symm
  unfold physicalCDFRestartCoordinateExpected at H
  rw [hm1,hm0,Real.toNNReal_coe] at H
  change (∫ w,actualParisiRestartField W β a x0 v w*
    actualParisiFullMagnetization β (a+v) (actualParisiRestartField W β a x0 v w) ∂W.law)-
    x0*actualParisiFullMagnetization β a x0 = _ at H
  rw [H]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le v.coe_nonneg] at hu
  have hu0 : 0 ≤ u := hu.1
  have hut : a+u.toNNReal ≤ parisiEquilibriumPhysicalEndpoint β := by
    apply le_trans _ hav
    apply add_le_add_right
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal u hu0]
    exact hu.2
  apply integral_congr_ae
  apply ae_of_all
  intro w
  have HE := actualParisiCoordinateRate_eq_before_support β hβ hQT hT0 hT1 (a+u.toNNReal) hut
    (actualParisiRestartField W β a x0 u.toNNReal w)
  simpa only [NNReal.coe_add,Real.coe_toNNReal u hu0,actualParisiRestartField,actualParisiFullScalarDrift,α] using HE

lemma actualParisiRestartField_eq_tanh_picard_after_support
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a v : ℝ≥0)
    (ha : parisiEquilibriumPhysicalEndpoint β ≤ a) (x0 : ℝ) :
    actualParisiRestartField W β a x0 v =ᵐ[W.law]
      (fun w => scalarForwardPicardPath scalarTanhDrift v (x0,brownianFinitePath W v w)
        ⟨v,v.coe_nonneg,le_rfl⟩) := by
  let past : ScalarContinuousPath a := ⟨fun _ => x0,continuous_const⟩
  filter_upwards [boundedDriftRestartCallback_fresh_version W (actualParisiFullScalarDrift β) a v past]
    with w hw
  have HE := actualParisiRestartCallback_eq_tanh_after_support β hβ a v ha
    (past,brownianFinitePath W v w)
  have H := (hw ⟨v,v.coe_nonneg,le_rfl⟩).symm
  rw [HE] at H
  exact H

theorem actualParisiFullProcess_post_restartCoordinate_expectation
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (a v : ℝ≥0)
    (ha : parisiEquilibriumPhysicalEndpoint β ≤ a) (x0 : ℝ) :
    (∫ w,actualParisiRestartField W β a x0 v w*
      actualParisiFullMagnetization β (a+v) (actualParisiRestartField W β a x0 v w) ∂W.law)-
      x0*actualParisiFullMagnetization β a x0 = (v:ℝ) := by
  have haR : β^2*parisiEquilibriumSupportEndpoint β ≤ (a:ℝ) := by
    simpa only [parisiEquilibriumPhysicalEndpoint_coe β hβ] using NNReal.coe_le_coe.mpr ha
  have havR : β^2*parisiEquilibriumSupportEndpoint β ≤ (a:ℝ)+(v:ℝ) :=
    haR.trans (le_add_of_nonneg_right v.coe_nonneg)
  simp only [actualParisiFullMagnetization_eq_tanh_after_support β hβ _ haR,
    actualParisiFullMagnetization_eq_tanh_after_support β hβ _ havR]
  have HE : (∫ w,actualParisiRestartField W β a x0 v w*Real.tanh (actualParisiRestartField W β a x0 v w) ∂W.law)=
      x0*Real.tanh x0+(v:ℝ) := by
    have H := scalarTanhPicard_coordinate_magnetization_expectation W x0 v
    refine (integral_congr_ae ?_).trans H
    filter_upwards [actualParisiRestartField_eq_tanh_picard_after_support W β hβ a v ha x0] with w hw
    rw [hw]
  rw [HE]
  ring

end SKConstants
