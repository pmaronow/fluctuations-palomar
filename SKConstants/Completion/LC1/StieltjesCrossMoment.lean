module

public import SKConstants.Completion.LC1.TerminalCrossMoment
public import SKConstants.Completion.LC1.BrownianStieltjesFubini
public import SKConstants.ParisiScalarEnergyProfiles

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants.Completion.LC1
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_actualFullCurvature_process_real (W : BrownianSystem Ω) (β : ℝ) :
    Measurable (fun q : ℝ × Ω => actualParisiFullCurvature β q.1.toNNReal
      (actualParisiFullScalarProcess W β q.1.toNNReal q.2)) := by
  have hy : Measurable (fun q : ℝ × Ω => actualParisiFullScalarProcess W β q.1.toNNReal q.2) := by
    simpa only [zero_add] using measurable_fullScalar_real_shift W β 0
  have hp : Measurable (fun q : ℝ × Ω => ((q.1.toNNReal:ℝ),
      actualParisiFullScalarProcess W β q.1.toNNReal q.2)) :=
    (measurable_subtype_coe.comp (measurable_real_toNNReal.comp measurable_fst)).prodMk hy
  convert (continuous_actualParisiFullCurvature β).measurable.comp hp using 1
  funext q
  rfl

theorem actualFullProcess_stieltjes_cross_moment_test
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (wgt : StieltjesFunction ℝ) (hwgt : Continuous wgt)
    (S T H : ℝ≥0) (hST : S ≤ T) (hTH : T ≤ H)
    (F : ScalarContinuousPath S → ℝ) (hF : Measurable F)
    (C : ℝ≥0) (hFC : ∀ p, |F p| ≤ C) :
    (∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) S w) *
      actualParisiMagnetizationObservable W β H w *
        (scalarGlobalStieltjesWeightedProcess wgt W.driver T w -
          scalarGlobalStieltjesWeightedProcess wgt W.driver S w) ∂W.law) =
    ∫ r in (S:ℝ)..(T:ℝ), wgt r * (∫ w,
      F (boundedDriftPastPath W (actualParisiFullScalarDrift β) S w) *
        actualParisiFullCurvature β r.toNNReal (actualParisiFullScalarProcess W β r.toNNReal w) ∂W.law) := by
  let := W.isProbability
  let f := F ∘ boundedDriftPastPath W (actualParisiFullScalarDrift β) S
  let M := actualParisiMagnetizationObservable W β H
  let G : Ω → ℝ := fun w => f w * M w
  let p : ℝ → ℝ := fun r => ∫ w, f w * actualParisiFullCurvature β r.toNNReal
    (actualParisiFullScalarProcess W β r.toNNReal w) ∂W.law
  have hf : Measurable f := hF.comp (measurable_boundedDriftPastPath W (actualParisiFullScalarDrift β) S)
  have hG : Measurable G := hf.mul (measurable_actualParisiMagnetizationObservable W β H)
  have hGC (w : Ω) : |G w| ≤ C := by
    exact (abs_mul _ _).trans_le ((mul_le_mul (hFC _)
      (actualParisiMagnetizationObservable_abs_le W β H w) (abs_nonneg _) C.coe_nonneg).trans_eq (mul_one _))
  have hRate : Measurable (fun q : ℝ × Ω => f q.2 * actualParisiFullCurvature β q.1.toNNReal
      (actualParisiFullScalarProcess W β q.1.toNNReal q.2)) :=
    (hf.comp measurable_snd).mul (measurable_actualFullCurvature_process_real W β)
  have hp : Measurable p := hRate.stronglyMeasurable.integral_prod_right'.measurable
  have hBound (r : ℝ) (w : Ω) : |f w * actualParisiFullCurvature β r.toNNReal
      (actualParisiFullScalarProcess W β r.toNNReal w)| ≤ C := by
    rw [abs_mul]
    exact (mul_le_mul (hFC _)
      (actualParisiFullCurvature_abs_le_one β r.toNNReal (actualParisiFullScalarProcess W β r.toNNReal w))
      (abs_nonneg _) C.coe_nonneg).trans_eq (mul_one _)
  have hpC (r : ℝ) : |p r| ≤ C := by
    rw [← Real.norm_eq_abs]
    have hh := norm_integral_le_of_norm_le_const (μ:=W.law) (C:=(C:ℝ))
      (f:=fun w => f w * actualParisiFullCurvature β r.toNNReal
        (actualParisiFullScalarProcess W β r.toNNReal w))
      (ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs] using hBound r w))
    simpa only [probReal_univ,mul_one] using hh
  have hMoment (r : ℝ) (hr : r ∈ Icc (S:ℝ) (T:ℝ)) :
      (∫ w, G w * (W.driver r.toNNReal w-W.driver S w) ∂W.law) =
        ∫ u in (S:ℝ)..r, p u := by
    have hr0 : 0 ≤ r := S.coe_nonneg.trans hr.1
    have hSr : S ≤ r.toNNReal := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ hr0]
      exact hr.1
    have hrH : r.toNNReal ≤ H := by
      apply NNReal.coe_le_coe.mp
      rw [Real.coe_toNNReal _ hr0]
      exact hr.2.trans (NNReal.coe_le_coe.mpr hTH)
    have hh := actualFullProcess_terminal_brownian_cross_moment_test W β hβ S r.toNNReal H hSr hrH F hF C hFC
    change (∫ w, f w * M w * (W.B r.toNNReal w-W.B S w) ∂W.law) =
      ∫ u in (S:ℝ)..(r.toNNReal:ℝ), p u at hh
    rw [Real.coe_toNNReal _ hr0] at hh
    refine (integral_congr_ae ?_).trans hh
    filter_upwards [W.driver_indistinguishable] with w hw
    change f w * M w * (W.driver r.toNNReal w-W.driver S w) = _
    rw [hw,hw]
  have hend := hMoment (T:ℝ) ⟨NNReal.coe_le_coe.mpr hST,le_rfl⟩
  simp only [Real.toNNReal_coe] at hend
  have hTime : (∫ r in (S:ℝ)..(T:ℝ),
      (∫ w, G w * (W.driver r.toNNReal w-W.driver S w) ∂W.law) ∂wgt.measure) =
      ∫ r in (S:ℝ)..(T:ℝ), (∫ u in (S:ℝ)..r, p u) ∂wgt.measure := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le (NNReal.coe_le_coe.mpr hST)] at hr
    exact hMoment r hr
  have hh := bounded_brownian_stieltjes_increment_integral W wgt S T hST G hG C hGC
  rw [hend,hTime] at hh
  exact hh.trans (stieltjes_weighted_primitive wgt hwgt p hp C hpC S T (NNReal.coe_le_coe.mpr hST))

theorem actualFullProcess_stieltjes_cross_moment
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (wgt : StieltjesFunction ℝ) (hwgt : Continuous wgt)
    (S T H : ℝ≥0) (hST : S ≤ T) (hTH : T ≤ H) :
    (∫ w, actualParisiMagnetizationObservable W β H w *
      (scalarGlobalStieltjesWeightedProcess wgt W.driver T w -
        scalarGlobalStieltjesWeightedProcess wgt W.driver S w) ∂W.law) =
    ∫ r in (S:ℝ)..(T:ℝ), wgt r * actualParisiFullSusceptibilityExpected W β r := by
  have hh := actualFullProcess_stieltjes_cross_moment_test W β hβ wgt hwgt S T H hST hTH
    (fun _ => (1:ℝ)) measurable_const 1 (fun _ => by norm_num)
  simp only [one_mul] at hh
  refine hh.trans ?_
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (NNReal.coe_le_coe.mpr hST)] at hr
  have hr0 : 0 ≤ r := S.coe_nonneg.trans hr.1
  change wgt r * (∫ w, actualParisiFullCurvature β r.toNNReal
    (actualParisiFullScalarProcess W β r.toNNReal w) ∂W.law) = _
  rw [Real.coe_toNNReal _ hr0]
  rfl

end SKConstants.Completion.LC1
