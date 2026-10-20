module

public import SKConstants.ScalarProcessMixedRowCovariances
public import SKConstants.ScalarProcessSeedReconstruction
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SKConstants
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

def scalarHiddenBrownianKernel (P : Measure Ω) [SFinite P] : Kernel ℝ (Bool × Ω) where
  toFun z := scalarHiddenBrownianLaw z P
  measurable' := by
    apply Measure.measurable_measure.mpr
    intro A hA
    simp only [scalarHiddenBrownianLaw, scalarHiddenPriorBool, Measure.add_prod,
      Measure.prod_smul_left, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact ((measurable_scalarPlusWeight.ennreal_ofReal).mul_const _).add
      ((measurable_scalarMinusWeight.ennreal_ofReal).mul_const _)

instance scalarHiddenBrownianKernel_isMarkov (P : Measure Ω) [IsProbabilityMeasure P] :
    IsMarkovKernel (scalarHiddenBrownianKernel P) := by
  constructor
  intro z
  exact scalarHiddenBrownianLaw_isProbability z P

def scalarSeedHiddenBrownianLaw (ν : Measure ℝ) (P : Measure Ω) [SFinite P] :
    Measure (ℝ × (Bool × Ω)) := ν ⊗ₘ scalarHiddenBrownianKernel P

instance scalarSeedHiddenBrownianLaw_isProbability
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (scalarSeedHiddenBrownianLaw ν P) := by
  unfold scalarSeedHiddenBrownianLaw
  infer_instance

theorem scalarSeedHiddenBrownianLaw_seed_hasLaw
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P] :
    HasLaw Prod.fst ν (scalarSeedHiddenBrownianLaw ν P) := by
  refine ⟨measurable_fst.aemeasurable, ?_⟩
  exact Measure.fst_compProd ν (scalarHiddenBrownianKernel P)

def scalarSeedHiddenContinuousField (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (u : ℝ × (Bool × Ω)) : ℝ := scalarHiddenContinuousField u.1 B T u.2

theorem measurable_scalarSeedHiddenContinuousField
    (B : ℝ≥0 → Ω → ℝ) (hBm : Measurable (Function.uncurry B)) (T : ℝ≥0) :
    Measurable (scalarSeedHiddenContinuousField B T) := by
  exact (measurable_fst.add
    (((measurable_of_finite scalarHiddenSign).comp measurable_snd.fst).mul_const _)).add
      ((hBm.comp (measurable_const.prodMk measurable_id)).comp measurable_snd.snd)

theorem scalarSeedHiddenBrownianLaw_hiddenSign_mean
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P] :
    (∫ u, scalarHiddenSign u.2.1 ∂scalarSeedHiddenBrownianLaw ν P) = ∫ z, Real.tanh z ∂ν := by
  have hm : Measurable (fun u : ℝ × (Bool × Ω) => scalarHiddenSign u.2.1) :=
    (measurable_of_finite scalarHiddenSign).comp measurable_snd.fst
  have hi : Integrable (fun u : ℝ × (Bool × Ω) => scalarHiddenSign u.2.1)
      (scalarSeedHiddenBrownianLaw ν P) := Integrable.of_bound hm.aestronglyMeasurable 1
        (ae_of_all _ (fun u => (scalarHiddenSign_norm_one u.2.1).le))
  rw [scalarSeedHiddenBrownianLaw, Measure.integral_compProd hi]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    change (∫ u, scalarHiddenSign u.1 ∂scalarHiddenBrownianLaw z P) = Real.tanh z
    rw [(scalarHiddenSign_hasLaw P z).integral_eq, integral_id_scalarSpinLaw])

theorem scalarSeedHiddenBrownianLaw_hiddenSign_secondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P] :
    (∫ u, (scalarHiddenSign u.2.1)^2 ∂scalarSeedHiddenBrownianLaw ν P) = 1 := by
  have he : (fun u : ℝ × (Bool × Ω) => (scalarHiddenSign u.2.1)^2) = fun _ => 1 := by
    ext u
    cases u.2.1 <;> norm_num [scalarHiddenSign]
  rw [he, integral_const]
  simp

theorem scalarSeed_tanh_mean_eq_zero_of_symmetric
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hsym : ν.map (fun z => -z) = ν) :
    (∫ z, Real.tanh z ∂ν) = 0 := by
  have hMap : AEStronglyMeasurable Real.tanh (ν.map (fun z => -z)) :=
    measurable_scalarTanh.aestronglyMeasurable
  have he := integral_map measurable_neg.aemeasurable hMap
  rw [hsym] at he
  simp only [Real.tanh_neg, integral_neg] at he
  linarith

theorem scalarSeedHiddenSign_hasSubgaussianMGF_of_symmetric
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (P : Measure Ω) [IsProbabilityMeasure P]
    (hsym : ν.map (fun z => -z) = ν) :
    HasSubgaussianMGF (fun u : ℝ × (Bool × Ω) => scalarHiddenSign u.2.1) 1
      (scalarSeedHiddenBrownianLaw ν P) := by
  have hm : Measurable (fun u : ℝ × (Bool × Ω) => scalarHiddenSign u.2.1) :=
    (measurable_of_finite scalarHiddenSign).comp measurable_snd.fst
  have hb : ∀ᵐ u ∂scalarSeedHiddenBrownianLaw ν P, scalarHiddenSign u.2.1 ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ae_of_all _ (fun u => by cases u.2.1 <;> norm_num [scalarHiddenSign])
  have hmean : (∫ u, scalarHiddenSign u.2.1 ∂scalarSeedHiddenBrownianLaw ν P) = 0 := by
    rw [scalarSeedHiddenBrownianLaw_hiddenSign_mean,
      scalarSeed_tanh_mean_eq_zero_of_symmetric ν hsym]
  convert hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hm.aemeasurable hb hmean using 1
  apply NNReal.eq
  simp only [NNReal.coe_one, NNReal.coe_pow, NNReal.coe_div, coe_nnnorm]
  norm_num

end SKConstants
