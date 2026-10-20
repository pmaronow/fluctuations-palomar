module

public import SKConstants.ParisiFullMartingale
public import SKConstants.ScalarProcessGaussianMoments
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

lemma integrable_gaussianPDFReal_mul_coordinate (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    Integrable (fun y => gaussianPDFReal μ v y*y) := by
  have hi : Integrable (fun y : ℝ => y) (gaussianReal μ v) :=
    (memLp_id_gaussianReal 1).integrable (by simp)
  rw [gaussianReal_of_var_ne_zero μ hv] at hi
  have H := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF μ v) (ae_of_all _ (fun y => gaussianPDF_lt_top (μ:=μ) (v:=v) (x:=y)))).mp hi
  simpa only [toReal_gaussianPDF,smul_eq_mul] using H

lemma integral_gaussianPDFReal_mul_coordinate (μ : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (∫ y,gaussianPDFReal μ v y*y)=μ := by
  have H := integral_id_gaussianReal (μ:=μ) (v:=v)
  rw [integral_gaussianReal_eq_integral_smul hv] at H
  simpa only [smul_eq_mul] using H

theorem integral_coordinate_tanh_scalarTransitionKernel (z : ℝ) (t : ℝ≥0) :
    (∫ y,y*Real.tanh y ∂scalarTransitionKernel t z)=z*Real.tanh z+(t:ℝ) := by
  change (∫ y,y*Real.tanh y ∂if t=0 then Measure.dirac z else scalarKernelLaw z t)=_
  by_cases ht : t=0
  · simp [ht]
  · simp only [ht,↓reduceIte]
    rw [integral_scalarKernelLaw]
    have he (y : ℝ) : scalarKernel z t y*(y*Real.tanh y)=
        scalarPlusWeight z*(gaussianPDFReal (z+t) t y*y)-
          scalarMinusWeight z*(gaussianPDFReal (z-t) t y*y) := by
      calc
        _ = y*(scalarKernel z t y*Real.tanh y) := by ring
        _ = _ := by rw [scalarKernel_mul_tanh z y t ht]; ring
    simp_rw [he]
    rw [integral_sub ((integrable_gaussianPDFReal_mul_coordinate (z+t) t ht).const_mul _)
      ((integrable_gaussianPDFReal_mul_coordinate (z-t) t ht).const_mul _),
      integral_const_mul,integral_const_mul,
      integral_gaussianPDFReal_mul_coordinate (z+t) t ht,
      integral_gaussianPDFReal_mul_coordinate (z-t) t ht]
    calc
      _ = z*(scalarPlusWeight z-scalarMinusWeight z)+(t:ℝ)*(scalarPlusWeight z+scalarMinusWeight z) := by ring
      _ = _ := by rw [scalarWeight_difference,scalarWeight_sum]; ring

theorem scalarTanhPicard_endpoint_integral {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (z : ℝ) (v : ℝ≥0) (φ : ℝ → ℝ) (hφ : Measurable φ) :
    (∫ w,φ (scalarForwardPicardPath scalarTanhDrift v
      (z,brownianFinitePath W v w) ⟨v,v.coe_nonneg,le_rfl⟩) ∂W.law)=
    ∫ y,φ y ∂scalarTransitionKernel v z := by
  let := W.isProbability
  let F := brownianFinitePath W v
  let J : ScalarContinuousPath v → ScalarContinuousPath v :=
    fun p => scalarForwardPicardPath scalarTanhDrift v (z,p)
  let H : ScalarContinuousPath v → ℝ := fun p => φ (p ⟨v,v.coe_nonneg,le_rfl⟩)
  have hJ : Measurable J := (measurable_scalarForwardPicardPath scalarTanhDrift v).comp
    (measurable_const.prodMk measurable_id)
  have hH : Measurable H := hφ.comp (ContinuousMap.measurable_eval _)
  have hl := scalarForwardPicardPath_actual_hidden_field_law_joint_version W.law W.B W.brownian
    v z F (measurable_brownianFinitePath W v) (brownianFinitePath_version W v)
  have hl' : W.law.map (J ∘ F) = (scalarHiddenBrownianLaw z W.law).map
      (fun u => scalarSeedHiddenFieldPath v F (z,u)) := by
    rw [←Measure.map_map hJ (measurable_brownianFinitePath W v)]
    exact hl
  have hm : Measurable (fun u : Bool × Ω => scalarSeedHiddenFieldPath v F (z,u)) :=
    (measurable_scalarSeedHiddenFieldPath v F (measurable_brownianFinitePath W v)).comp
      (measurable_const.prodMk measurable_id)
  change (∫ w,H (J (F w)) ∂W.law)=_
  rw [show (∫ w,H (J (F w)) ∂W.law)=∫ p,H p ∂W.law.map (J ∘ F) from
    (integral_map (hJ.comp (measurable_brownianFinitePath W v)).aemeasurable hH.aestronglyMeasurable).symm,
    hl',integral_map hm.aemeasurable hH.aestronglyMeasurable]
  have hv : (fun u : Bool × Ω => H (scalarSeedHiddenFieldPath v F (z,u))) =ᵐ[
      scalarHiddenBrownianLaw z W.law] (fun u => φ (scalarHiddenContinuousField z W.B v u)) := by
    have hf := (measurePreserving_snd (μ:=scalarHiddenPriorBool z) (ν:=W.law)).quasiMeasurePreserving.ae
      (brownianFinitePath_version W v)
    filter_upwards [hf] with u hu
    dsimp only [H,scalarSeedHiddenFieldPath,ContinuousMap.coe_mk]
    rw [hu ⟨v,v.coe_nonneg,le_rfl⟩]
    rfl
  rw [integral_congr_ae hv]
  exact integral_scalarHiddenContinuousField_comp W.brownian.toIsPreBrownianReal z v φ hφ

theorem scalarTanhPicard_coordinate_magnetization_expectation {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (z : ℝ) (v : ℝ≥0) :
    (∫ w, (scalarForwardPicardPath scalarTanhDrift v
      (z,brownianFinitePath W v w) ⟨v,v.coe_nonneg,le_rfl⟩)*
        Real.tanh (scalarForwardPicardPath scalarTanhDrift v
          (z,brownianFinitePath W v w) ⟨v,v.coe_nonneg,le_rfl⟩) ∂W.law)=z*Real.tanh z+(v:ℝ) :=
  (scalarTanhPicard_endpoint_integral W z v _ (measurable_id.mul measurable_scalarTanh)).trans
    (integral_coordinate_tanh_scalarTransitionKernel z v)

end SKConstants
