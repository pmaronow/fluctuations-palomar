module

public import SKConstants.ParisiCDFRestartMGF
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option maxHeartbeats 800000

namespace SKConstants

theorem subgaussian_integral_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) : (∫ w, X w ∂μ) = 0 := by
  have hs : integrableExpSet X μ = univ := by
    ext t
    simp only [mem_univ, iff_true]
    exact h.integrable_exp_mul t
  have hd : HasDerivAt (mgf X μ) (∫ w, X w ∂μ) 0 := by
    simpa only [zero_mul, Real.exp_zero, mul_one] using
      hasDerivAt_mgf (X := X) (μ := μ) (t := 0) (by simp [hs])
  have he : HasDerivAt (fun t : ℝ => Real.exp ((c : ℝ)*t^2/2)) 0 0 := by
    convert ((((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (c : ℝ)).div_const 2).exp using 1 <;>
      norm_num
  have hm : IsLocalMax (fun t => mgf X μ t - Real.exp ((c : ℝ)*t^2/2)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa only [mgf_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      zero_div, Real.exp_zero, sub_self] using sub_nonpos.mpr (h.mgf_le t)
  simpa only [sub_zero] using hm.hasDerivAt_eq_zero (hd.sub he)

end SKConstants

namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

lemma compactCDFJet_zero_abs_le_one (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) {T : ℝ}
    (hT0 : 0 ≤ T) (_hT1 : T ≤ 1) (t x : ℝ) :
    |compactCDFJet β α T 0 t x| ≤ 1 := by
  have hr := cdfStripTime_mem hT0 t
  have ht : Real.toNNReal (1-cdfStripTime T t) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith [hr.1]
  simpa only [compactCDFJet, iteratedDeriv_zero, compactCDFGradient] using
    (scalarCDF_derivative_bounds β ha α.mono (cdfStripTime T t) _ ht x).1

theorem physicalCDFGradient_initial_hasSubgaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (hβ : β ≠ 0) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)
    (v : ℝ≥0) (hv : (v : ℝ)/β^2 < T) :
    HasSubgaussianMGF (fun w => compactCDFJet β α T 0 ((v : ℝ)/β^2)
      (finiteTemperatureCDFProcess W β α ha h1 v w)) v W.law := by
  let := W.isProbability
  have hm : Measurable (fun w => compactCDFJet β α T 0 ((v : ℝ)/β^2)
      (finiteTemperatureCDFProcess W β α ha h1 v w)) :=
    ((compactCDFJetField β α ha h1 hβ hT0 hT1 0).smooth.regular _).smooth.continuous.measurable.comp
      (finiteTemperatureCDFProcess_measurable W β α ha h1 v)
  refine ⟨fun θ => integrable_exp_mul_of_mem_Icc (a := -1) (b := 1) hm.aemeasurable ?_, fun θ => ?_⟩
  · exact ae_of_all _ (fun w => abs_le.mp
      (compactCDFJet_zero_abs_le_one β α ha hT0 hT1.le _ _))
  · simpa only [mgf, mul_comm (v : ℝ) (θ^2)] using
      physicalCDFGradient_initial_mgf W β α ha h1 hβ hT0 hT1 v hv θ

theorem physicalCDFGradient_restart_hasSubgaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (hβ : β ≠ 0) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)
    (a : ℝ) (ha0 : 0 ≤ a) (x0 : ℝ) (v : ℝ≥0)
    (hv : (a+(v : ℝ))/β^2 < T) :
    HasSubgaussianMGF (fun w =>
      compactCDFJet β α T 0 ((a+(v : ℝ))/β^2)
        (x0+(SKConstants.BoundedLipschitzDrift.translated
          (finiteTemperatureCDFDrift β α ha h1) a x0).solution W.driver v w) -
        compactCDFJet β α T 0 (a/β^2) x0) v W.law := by
  let := W.isProbability
  let b := SKConstants.BoundedLipschitzDrift.translated
    (finiteTemperatureCDFDrift β α ha h1) a x0
  have hm : Measurable (fun w => compactCDFJet β α T 0 ((a+(v : ℝ))/β^2)
      (x0+b.solution W.driver v w) - compactCDFJet β α T 0 (a/β^2) x0) :=
    (((compactCDFJetField β α ha h1 hβ hT0 hT1 0).smooth.regular _).smooth.continuous.measurable.comp
      (measurable_const.add (b.solution_measurable W v))).sub_const _
  refine ⟨fun θ => integrable_exp_mul_of_mem_Icc (a := -2) (b := 2) hm.aemeasurable ?_, fun θ => ?_⟩
  · apply ae_of_all
    intro w
    have hA := abs_le.mp (compactCDFJet_zero_abs_le_one β α ha hT0 hT1.le
      ((a+(v : ℝ))/β^2) (x0+b.solution W.driver v w))
    have hB := abs_le.mp (compactCDFJet_zero_abs_le_one β α ha hT0 hT1.le (a/β^2) x0)
    exact (show _ ∈ Icc (-2 : ℝ) 2 from ⟨by linarith, by linarith⟩)
  · simpa only [mgf, mul_comm (v : ℝ) (θ^2)] using
      physicalCDFGradient_restart_mgf W β α ha h1 hβ hT0 hT1 a ha0 x0 v hv θ

theorem physicalCDFGradient_restart_integral_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] (W : BrownianSystem Ω)
    (β : ℝ) (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1)
    (h1 : α 1 = 1) (hβ : β ≠ 0) {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1)
    (a : ℝ) (ha0 : 0 ≤ a) (x0 : ℝ) (v : ℝ≥0)
    (hv : (a+(v : ℝ))/β^2 < T) :
    (∫ w, compactCDFJet β α T 0 ((a+(v : ℝ))/β^2)
        (x0+(SKConstants.BoundedLipschitzDrift.translated
          (finiteTemperatureCDFDrift β α ha h1) a x0).solution W.driver v w) -
        compactCDFJet β α T 0 (a/β^2) x0 ∂W.law) = 0 := by
  let := W.isProbability
  exact SKConstants.subgaussian_integral_eq_zero
    (physicalCDFGradient_restart_hasSubgaussianMGF W β α ha h1 hβ hT0 hT1 a ha0 x0 v hv)

end SKConstants.ParisiFullSupport
