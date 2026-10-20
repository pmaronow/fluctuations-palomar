module

public import SKConstants.ScalarProcessParisiSeed
public import SKConstants.ScalarProcessLagWeightBudget
public import SKConstants.ParisiSeedTail
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace SKConstants
open SKConstantsOAI.SK.Analytic SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

def scalarContinuationP (ν : Measure ℝ) (v : ℝ) : ℝ :=
  ∫ z, if v.toNNReal = 0 then scalarDefect z else scalarP z v.toNNReal ∂ν

def scalarContinuationR (ν : Measure ℝ) (v : ℝ) : ℝ :=
  ∫ z, if v.toNNReal = 0 then (scalarDefect z)^2 else scalarR z v.toNNReal ∂ν

theorem scalarHiddenExpectedDefectReal_eq_corrected
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (v : ℝ) (hv : 0 ≤ v) :
    scalarHiddenExpectedDefectReal P z B v =
      if v.toNNReal = 0 then scalarDefect z else scalarP z v.toNNReal := by
  simpa only [scalarHiddenExpectedDefectReal, scalarHiddenFieldReal,
    scalarHiddenContinuousField, Real.coe_toNNReal v hv] using
    integral_scalarHiddenContinuousField_defect hB z v.toNNReal

theorem scalarHiddenExpectedDefectSqReal_eq_corrected
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (v : ℝ) (hv : 0 ≤ v) :
    scalarHiddenExpectedDefectSqReal P z B v =
      if v.toNNReal = 0 then (scalarDefect z)^2 else scalarR z v.toNNReal := by
  simpa only [scalarHiddenExpectedDefectSqReal, scalarHiddenFieldReal,
    scalarHiddenContinuousField, Real.coe_toNNReal v hv] using
    integral_scalarHiddenContinuousField_defect_sq hB z v.toNNReal

theorem measurable_scalarHiddenExpectedDefectReal_seed
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (v : ℝ) (hv : 0 ≤ v) :
    Measurable (fun z => scalarHiddenExpectedDefectReal P z B v) := by
  simp_rw [scalarHiddenExpectedDefectReal_eq_corrected P _ B hB v hv]
  by_cases h : v.toNNReal = 0
  · simpa only [h, ite_true] using measurable_scalarDefect
  · simpa only [h, ite_false] using measurable_scalarP v.toNNReal

theorem measurable_scalarHiddenExpectedDefectSqReal_seed
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (v : ℝ) (hv : 0 ≤ v) :
    Measurable (fun z => scalarHiddenExpectedDefectSqReal P z B v) := by
  simp_rw [scalarHiddenExpectedDefectSqReal_eq_corrected P _ B hB v hv]
  by_cases h : v.toNNReal = 0
  · simpa only [h, ite_true] using measurable_scalarDefect.pow_const 2
  · simpa only [h, ite_false] using measurable_scalarR v.toNNReal

theorem scalarContinuationP_eq_actualAverage
    (ν : Measure ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (v : ℝ) :
    scalarContinuationP ν v = ∫ z, scalarHiddenExpectedDefectReal P z B (v.toNNReal : ℝ) ∂ν := by
  simp_rw [scalarHiddenExpectedDefectReal_eq_corrected P _ B hB _ v.toNNReal.coe_nonneg, Real.toNNReal_coe]
  rfl

theorem scalarContinuationR_eq_actualAverage
    (ν : Measure ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (v : ℝ) :
    scalarContinuationR ν v = ∫ z, scalarHiddenExpectedDefectSqReal P z B (v.toNNReal : ℝ) ∂ν := by
  simp_rw [scalarHiddenExpectedDefectSqReal_eq_corrected P _ B hB _ v.toNNReal.coe_nonneg, Real.toNNReal_coe]
  rfl

theorem continuous_scalarContinuationP
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) : Continuous (scalarContinuationP ν) := by
  have he : scalarContinuationP ν = fun v => ∫ z, scalarHiddenExpectedDefectReal P z B (v.toNNReal : ℝ) ∂ν :=
    funext (scalarContinuationP_eq_actualAverage ν P B hB.toIsPreBrownianReal)
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro v
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    (Eventually.of_forall (fun s =>
      (measurable_scalarHiddenExpectedDefectReal_seed P B hB.toIsPreBrownianReal (s.toNNReal : ℝ) s.toNNReal.coe_nonneg).aestronglyMeasurable))
    (Eventually.of_forall (fun s => ae_of_all _ (fun z =>
      scalarHiddenExpectedDefectReal_norm_le_one P z B (s.toNNReal : ℝ))))
    (integrable_const 1)
    (ae_of_all _ (fun z => ((continuous_scalarHiddenExpectedDefectReal P z B hB).comp
      (NNReal.continuous_coe.comp continuous_real_toNNReal)).tendsto v))

theorem continuous_scalarContinuationR
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) : Continuous (scalarContinuationR ν) := by
  have he : scalarContinuationR ν = fun v => ∫ z, scalarHiddenExpectedDefectSqReal P z B (v.toNNReal : ℝ) ∂ν :=
    funext (scalarContinuationR_eq_actualAverage ν P B hB.toIsPreBrownianReal)
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro v
  exact tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    (Eventually.of_forall (fun s =>
      (measurable_scalarHiddenExpectedDefectSqReal_seed P B hB.toIsPreBrownianReal (s.toNNReal : ℝ) s.toNNReal.coe_nonneg).aestronglyMeasurable))
    (Eventually.of_forall (fun s => ae_of_all _ (fun z =>
      scalarHiddenExpectedDefectSqReal_norm_le_one P z B (s.toNNReal : ℝ))))
    (integrable_const 1)
    (ae_of_all _ (fun z => ((continuous_scalarHiddenExpectedDefectSqReal P z B hB).comp
      (NNReal.continuous_coe.comp continuous_real_toNNReal)).tendsto v))

theorem scalarHiddenExpectedDefectSqReal_pos
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (v : ℝ) :
    0 < scalarHiddenExpectedDefectSqReal P z B v := by
  have hm : AEStronglyMeasurable (fun u => scalarDefect (scalarHiddenFieldReal z B v u)^2)
      (scalarHiddenBrownianLaw z P) :=
    ((measurable_scalarDefect.comp_aemeasurable
      (aemeasurable_scalarHiddenFieldReal P z B hB v)).pow_const 2).aestronglyMeasurable
  have hi : Integrable (fun u => scalarDefect (scalarHiddenFieldReal z B v u)^2)
      (scalarHiddenBrownianLaw z P) := Integrable.of_bound hm 1
        (ae_of_all _ (fun u => norm_scalarDefect_sq_le_one _))
  apply (integral_pos_iff_support_of_nonneg (fun u => sq_nonneg _) hi).mpr
  have hs : Function.support (fun u => scalarDefect (scalarHiddenFieldReal z B v u)^2) = univ := by
    ext u
    simp only [Function.mem_support, mem_univ, iff_true]
    exact ne_of_gt (sq_pos_of_pos (scalarDefect_pos _))
  rw [hs, measure_univ]
  exact zero_lt_one

theorem scalarContinuationR_pos
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (v : ℝ) :
    0 < scalarContinuationR ν v := by
  rw [scalarContinuationR_eq_actualAverage ν P B hB v]
  have hi : Integrable (fun z => scalarHiddenExpectedDefectSqReal P z B (v.toNNReal : ℝ)) ν :=
    Integrable.of_bound (measurable_scalarHiddenExpectedDefectSqReal_seed P B hB (v.toNNReal : ℝ) v.toNNReal.coe_nonneg).aestronglyMeasurable
      1 (ae_of_all _ (fun z => scalarHiddenExpectedDefectSqReal_norm_le_one P z B (v.toNNReal : ℝ)))
  apply (integral_pos_iff_support_of_nonneg
    (fun z => (scalarHiddenExpectedDefectSqReal_pos P z B hB (v.toNNReal : ℝ)).le) hi).mpr
  have hs : Function.support (fun z => scalarHiddenExpectedDefectSqReal P z B (v.toNNReal : ℝ)) = univ := by
    ext z
    simp only [Function.mem_support, mem_univ, iff_true]
    exact ne_of_gt (scalarHiddenExpectedDefectSqReal_pos P z B hB (v.toNNReal : ℝ))
  rw [hs, measure_univ]
  exact zero_lt_one

theorem scalarContinuationR_le_exp
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (v : ℝ) (hv : 0 ≤ v) :
    scalarContinuationR ν v ≤ Real.exp (-v/2) := by
  rw [scalarContinuationR_eq_actualAverage ν P B hB v]
  have hi : Integrable (fun z => scalarHiddenExpectedDefectSqReal P z B (v.toNNReal : ℝ)) ν :=
    Integrable.of_bound (measurable_scalarHiddenExpectedDefectSqReal_seed P B hB (v.toNNReal : ℝ) v.toNNReal.coe_nonneg).aestronglyMeasurable
      1 (ae_of_all _ (fun z => scalarHiddenExpectedDefectSqReal_norm_le_one P z B (v.toNNReal : ℝ)))
  simpa using integral_mono hi (integrable_const (Real.exp (-v/2)))
    (fun z => by simpa only [Real.coe_toNNReal v hv] using
      scalarHiddenExpectedDefectSqReal_le_exp P z B hB (v.toNNReal : ℝ) v.toNNReal.coe_nonneg)

theorem scalarContinuationR_eq_scalarSeedR
    (ν : Measure ℝ) (v : ℝ) (hv : 0 < v) :
    scalarContinuationR ν v = scalarSeedR ν v.toNNReal := by
  simp only [scalarContinuationR, scalarSeedR, ne_of_gt (Real.toNNReal_pos.mpr hv), ite_false]

theorem scalarContinuationP_eq_scalarSeedP
    (ν : Measure ℝ) (v : ℝ) (hv : 0 < v) :
    scalarContinuationP ν v = scalarSeedP ν v.toNNReal := by
  simp only [scalarContinuationP, scalarSeedP, ne_of_gt (Real.toNNReal_pos.mpr hv), ite_false]

theorem scalarContinuationR_ge_compact_tail
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (R : ℝ) (hR : 0 ≤ R)
    (v : ℝ) (hv : 1 ≤ v) :
    ν.real (Icc (-R) R) * scalarCompactTailConstant R * scalarTailScale v.toNNReal ≤
      scalarContinuationR ν v := by
  rw [scalarContinuationR_eq_scalarSeedR ν v (by linarith)]
  exact scalarSeedR_ge_sharp_tail ν R hR v.toNNReal
    (by simpa only [Real.coe_toNNReal v (by linarith)] using hv)

theorem scalarContinuationP_eq_seedMixture_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (T : ℝ≥0) :
    scalarContinuationP ν T =
      ∫ u, scalarDefect (scalarSeedHiddenContinuousField B T u)
        ∂scalarSeedHiddenBrownianLaw ν P := by
  have hm := measurable_scalarDefect.comp (measurable_scalarSeedHiddenContinuousField B hBm T)
  have hi : Integrable (fun u => scalarDefect (scalarSeedHiddenContinuousField B T u))
      (scalarSeedHiddenBrownianLaw ν P) := Integrable.of_bound hm.aestronglyMeasurable 1
        (ae_of_all _ (fun u => norm_scalarDefect_le_one _))
  rw [scalarSeedHiddenBrownianLaw, Measure.integral_compProd hi,
    scalarContinuationP_eq_actualAverage ν P B hB]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    change scalarHiddenExpectedDefectReal P z B ((T : ℝ).toNNReal : ℝ) =
      ∫ u, scalarDefect (scalarHiddenContinuousField z B T u) ∂scalarHiddenBrownianLaw z P
    simp only [scalarHiddenExpectedDefectReal, scalarHiddenFieldReal,
      scalarHiddenContinuousField, Real.toNNReal_coe])

theorem scalarContinuationR_eq_seedMixture_moment
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (hBm : Measurable (Function.uncurry B)) (T : ℝ≥0) :
    scalarContinuationR ν T =
      ∫ u, scalarDefect (scalarSeedHiddenContinuousField B T u)^2
        ∂scalarSeedHiddenBrownianLaw ν P := by
  have hm := (measurable_scalarDefect.comp
    (measurable_scalarSeedHiddenContinuousField B hBm T)).pow_const 2
  have hi : Integrable (fun u => scalarDefect (scalarSeedHiddenContinuousField B T u)^2)
      (scalarSeedHiddenBrownianLaw ν P) := Integrable.of_bound hm.aestronglyMeasurable 1
        (ae_of_all _ (fun u => norm_scalarDefect_sq_le_one _))
  rw [scalarSeedHiddenBrownianLaw, Measure.integral_compProd hi,
    scalarContinuationR_eq_actualAverage ν P B hB]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    change scalarHiddenExpectedDefectSqReal P z B ((T : ℝ).toNNReal : ℝ) =
      ∫ u, scalarDefect (scalarHiddenContinuousField z B T u)^2 ∂scalarHiddenBrownianLaw z P
    simp only [scalarHiddenExpectedDefectSqReal, scalarHiddenFieldReal,
      scalarHiddenContinuousField, Real.toNNReal_coe])

def actualParisiSeedCompactRadius (β : ℝ) : ℝ := β^2+4*|β|+1

theorem actualParisiSeedCompactRadius_nonneg (β : ℝ) :
    0 ≤ actualParisiSeedCompactRadius β := by
  unfold actualParisiSeedCompactRadius
  positivity

theorem actualParisiEndpointSeedLaw_compact_mass
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    1/2 ≤ (actualParisiEndpointSeedLaw W β).real
      (Icc (-actualParisiSeedCompactRadius β) (actualParisiSeedCompactRadius β)) := by
  let := W.isProbability
  let v := parisiEquilibriumPhysicalEndpoint β
  let R := actualParisiSeedCompactRadius β
  have hQ := (parisiEquilibriumSupportEndpoint_spec β hβ).1
  have hv : (v : ℝ) = β^2*parisiEquilibriumSupportEndpoint β :=
    parisiEquilibriumPhysicalEndpoint_coe β hβ
  have hβ0 : 0 < β := by linarith
  have hvpos : 0 < (v : ℝ) := by rw [hv]; exact mul_pos (sq_pos_of_pos hβ0) hQ.1
  have hvle : (v : ℝ) ≤ β^2 := by
    rw [hv]
    exact mul_le_of_le_one_right (sq_nonneg _) hQ.2.le
  have hR : (v : ℝ) ≤ R := by
    dsimp [R, actualParisiSeedCompactRadius]
    linarith [abs_nonneg β]
  have hdiff : 4*β ≤ R-(v : ℝ) := by
    dsimp [R, actualParisiSeedCompactRadius]
    rw [abs_of_pos hβ0]
    linarith
  have hratio : 8 ≤ (R-(v : ℝ))^2/(2*(v : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (R-(v : ℝ)-4*β)]
  have ht := finiteTemperatureCDFProcess_abs_tail W β
    (cdf (parisiEquilibriumMeasure β : Measure ℝ))
    (fun z => ⟨cdf_nonneg _ z, cdf_le_one _ z⟩)
    (supported_probability_cdf_one (parisiEquilibriumMeasure β)
      (parisiEquilibriumMeasure_upstream_spec β).1) v R hR
  have hexp : 2*Real.exp (-8) ≤ (1/2 : ℝ) := by
    rw [Real.exp_neg]
    have hp := Real.exp_pos (8 : ℝ)
    have he := Real.add_one_le_exp (8 : ℝ)
    rw [← div_eq_mul_inv, div_le_iff₀ hp]
    linarith
  have htail : (actualParisiEndpointSeedLaw W β).real {z | R < |z|} ≤ 1/2 := by
    change (W.law.map (actualParisiPreContinuationField W β v)).real {z | R < |z|} ≤ 1/2
    rw [map_measureReal_apply
      (measurable_actualParisiPreContinuationField W β v)
      (show MeasurableSet {z : ℝ | R < |z|} from measurableSet_lt measurable_const measurable_id.abs)]
    change W.law.real {w | R < |actualParisiPreContinuationField W β v w|} ≤ _
    exact ht.trans ((mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (show -(R-(v : ℝ))^2/(2*(v : ℝ)) ≤ -8 from by
        rw [neg_div]
        exact neg_le_neg hratio)) (by norm_num)).trans hexp)
  have hs : {z : ℝ | R < |z|} = (Icc (-R) R)ᶜ := by
    ext z
    simp only [mem_ofPred_eq, mem_compl_iff, mem_Icc, ← abs_le, not_le]
  rw [hs, probReal_compl_eq_one_sub measurableSet_Icc] at htail
  dsimp [R] at htail
  linarith

def actualParisiContinuationP (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (β : ℝ) : ℝ → ℝ :=
  scalarContinuationP (actualParisiEndpointSeedLaw W β)

def actualParisiContinuationR (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (β : ℝ) : ℝ → ℝ :=
  scalarContinuationR (actualParisiEndpointSeedLaw W β)

theorem continuous_actualParisiContinuationP
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (β : ℝ) :
    Continuous (actualParisiContinuationP W β) := by
  let := W.isProbability
  exact continuous_scalarContinuationP _ W.law W.B W.brownian

theorem continuous_actualParisiContinuationR
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (β : ℝ) :
    Continuous (actualParisiContinuationR W β) := by
  let := W.isProbability
  exact continuous_scalarContinuationR _ W.law W.B W.brownian

theorem actualParisiContinuationR_pos
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (β v : ℝ) :
    0 < actualParisiContinuationR W β v := by
  let := W.isProbability
  exact scalarContinuationR_pos _ W.law W.B W.brownian.toIsPreBrownianReal v

theorem actualParisiContinuationR_le_exp
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (β v : ℝ) (hv : 0 ≤ v) :
    actualParisiContinuationR W β v ≤ Real.exp (-v/2) := by
  let := W.isProbability
  exact scalarContinuationR_le_exp _ W.law W.B W.brownian.toIsPreBrownianReal v hv

theorem scalarContinuationR_global_lower
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (R : ℝ) (hR : 0 ≤ R) (hmass : 0 < ν.real (Icc (-R) R)) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ, 0 ≤ v →
      C * (Real.exp (-v/2) / Real.sqrt (1+v)) ≤ scalarContinuationR ν v := by
  obtain ⟨c, hc, hsmall⟩ := isCompact_Icc.exists_forall_le'
    (continuous_scalarContinuationR ν P B hB).continuousOn
    (fun v (_ : v ∈ Icc (0 : ℝ) 1) => scalarContinuationR_pos ν P B hB.toIsPreBrownianReal v)
  let L := ν.real (Icc (-R) R)*scalarCompactTailConstant R/Real.sqrt (2*Real.pi)
  have hL : 0 < L := div_pos (mul_pos hmass (scalarCompactTailConstant_pos R))
    (Real.sqrt_pos.mpr (by positivity))
  refine ⟨min c L, lt_min hc hL, ?_⟩
  intro v hv
  have henv0 : 0 ≤ Real.exp (-v/2)/Real.sqrt (1+v) := by positivity
  by_cases hv1 : v ≤ 1
  · have hsqrt : 1 ≤ Real.sqrt (1+v) := by
      simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1+v by linarith)
    have henv : Real.exp (-v/2)/Real.sqrt (1+v) ≤ 1 := by
      exact (div_le_self (Real.exp_pos _).le hsqrt).trans
        (Real.exp_le_one_iff.mpr (by linarith))
    exact (mul_le_of_le_one_right (lt_min hc hL).le henv).trans
      ((min_le_left c L).trans (hsmall v ⟨hv,hv1⟩))
  · have hvge : 1 ≤ v := le_of_not_ge hv1
    have hvpos : 0 < v := by linarith
    have hden : 0 < Real.sqrt (2*Real.pi)*Real.sqrt v := by positivity
    have hdenle : Real.sqrt (2*Real.pi)*Real.sqrt v ≤
        Real.sqrt (2*Real.pi)*Real.sqrt (1+v) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (Real.sqrt_nonneg _)
    have htail : L*(Real.exp (-v/2)/Real.sqrt (1+v)) ≤
        ν.real (Icc (-R) R)*scalarCompactTailConstant R*scalarTailScale v.toNNReal := by
      calc
        _ = (ν.real (Icc (-R) R)*scalarCompactTailConstant R*Real.exp (-v/2)) /
            (Real.sqrt (2*Real.pi)*Real.sqrt (1+v)) := by dsimp [L]; ring
        _ ≤ (ν.real (Icc (-R) R)*scalarCompactTailConstant R*Real.exp (-v/2)) /
            (Real.sqrt (2*Real.pi)*Real.sqrt v) :=
          div_le_div_of_nonneg_left
            (mul_nonneg (mul_nonneg hmass.le (scalarCompactTailConstant_pos R).le)
              (Real.exp_pos _).le) hden hdenle
        _ = _ := by
          unfold scalarTailScale
          norm_num only [Nat.cast_ofNat]
          rw [Real.coe_toNNReal v hv, Real.sqrt_mul (show 0 ≤ 2*Real.pi by positivity)]
          ring
    exact ((mul_le_mul_of_nonneg_right (min_le_right c L) henv0).trans htail).trans
      (scalarContinuationR_ge_compact_tail ν R hR v hvge)

theorem actualParisiContinuationR_global_lower
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ, 0 ≤ v →
      C * (Real.exp (-v/2) / Real.sqrt (1+v)) ≤ actualParisiContinuationR W β v := by
  let := W.isProbability
  exact scalarContinuationR_global_lower _ W.law W.B W.brownian
    (actualParisiSeedCompactRadius β) (actualParisiSeedCompactRadius_nonneg β)
    (lt_of_lt_of_le (by norm_num) (actualParisiEndpointSeedLaw_compact_mass W β hβ))

theorem actualParisiContinuationP_le_tail
    (W : BrownianSystem Ω) (β v : ℝ) (hv : 0 < v) :
    actualParisiContinuationP W β v ≤ 4*scalarTailScale v.toNNReal := by
  rw [actualParisiContinuationP, scalarContinuationP_eq_scalarSeedP _ v hv]
  exact scalarSeedP_le_sharp_tail _ v.toNNReal (ne_of_gt (Real.toNNReal_pos.mpr hv))

end SKConstants
