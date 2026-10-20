module

public import SKConstants.GaussianEntropy
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.CompMap

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped ENNReal NNReal
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def gaussianPiSmoothingKernel {ι : Type*} [Fintype ι] (v : ι → ℝ≥0) :
    Kernel (ι → ℝ) (ι → ℝ) :=
  (Kernel.id ×ₖ Kernel.const (ι → ℝ) (Measure.pi fun i => gaussianReal 0 (v i))).map
    (fun p : (ι → ℝ) × (ι → ℝ) => fun i => p.1 i + p.2 i)

instance gaussianPiSmoothingKernel_isMarkov {ι : Type*} [Fintype ι]
    (v : ι → ℝ≥0) : IsMarkovKernel (gaussianPiSmoothingKernel v) := by
  unfold gaussianPiSmoothingKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

theorem gaussianPiSmoothingKernel_apply {ι : Type*} [Fintype ι]
    (v : ι → ℝ≥0) (a : ι → ℝ) :
    gaussianPiSmoothingKernel v a = Measure.pi (fun i => gaussianReal (a i) (v i)) := by
  rw [gaussianPiSmoothingKernel, Kernel.map_apply _ (by fun_prop), Kernel.prod_apply]
  simp only [Kernel.id_apply, Kernel.const_apply]
  rw [Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop)]
  change (Measure.pi fun i => gaussianReal 0 (v i)).map
    (fun z i => a i + z i) = _
  rw [Measure.pi_map_pi (fun i => (show Measurable (fun y : ℝ => a i + y) by fun_prop).aemeasurable)]
  simp only [gaussianReal_map_const_add, zero_add]

theorem klDiv_pi_gaussianReal_same_variances_fintype {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    klDiv (Measure.pi fun i => gaussianReal (a i) (v i))
      (Measure.pi fun i => gaussianReal (b i) (v i)) =
      ENNReal.ofReal (∑ i, (a i - b i) ^ 2 / (2 * (v i : ℝ))) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft (fun i => gaussianReal (a i) (v i)) e).map_eq,
    ← (measurePreserving_piCongrLeft (fun i => gaussianReal (b i) (v i)) e).map_eq,
    klDiv_map_measurableEquiv,
    klDiv_pi_gaussianReal_same_variances (Fintype.card ι) (fun i => a (e i)) (fun i => b (e i))
      (fun i => v (e i)) (fun i => hv _)]
  congr 1
  exact e.sum_comp (fun i => (a i - b i) ^ 2 / (2 * (v i : ℝ)))

theorem klDiv_gaussianPiSmoothingKernel {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    klDiv (gaussianPiSmoothingKernel v a) (gaussianPiSmoothingKernel v b) =
      ENNReal.ofReal (∑ i, (a i - b i) ^ 2 / (2 * (v i : ℝ))) := by
  rw [gaussianPiSmoothingKernel_apply, gaussianPiSmoothingKernel_apply]
  exact klDiv_pi_gaussianReal_same_variances_fintype a b v hv

theorem klDiv_gaussianPiSmoothing_mixture_le {A ι : Type*} [MeasurableSpace A]
    [Fintype ι] (μ : Measure A) [IsProbabilityMeasure μ]
    (a b : A → ι → ℝ) (ha : Measurable a) (hb : Measurable b)
    (v : ι → ℝ≥0) (hv : ∀ i, v i ≠ 0) :
    klDiv ((gaussianPiSmoothingKernel v).comap a ha ∘ₘ μ)
      ((gaussianPiSmoothingKernel v).comap b hb ∘ₘ μ) ≤
      ∫⁻ i, ENNReal.ofReal (∑ j, (a i j - b i j) ^ 2 / (2 * (v j : ℝ))) ∂μ := by
  let ka := (gaussianPiSmoothingKernel v).comap a ha
  let kb := (gaussianPiSmoothingKernel v).comap b hb
  have hac (i : A) : ka i ≪ kb i := by
    apply (klDiv_ne_top_iff.mp ?_).1
    change klDiv (gaussianPiSmoothingKernel v (a i))
      (gaussianPiSmoothingKernel v (b i)) ≠ ⊤
    rw [klDiv_gaussianPiSmoothingKernel _ _ v hv]
    exact ENNReal.ofReal_ne_top
  have h := klDiv_map_le (μ ⊗ₘ ka) (μ ⊗ₘ kb) measurable_snd
  change klDiv (μ ⊗ₘ ka).snd (μ ⊗ₘ kb).snd ≤ _ at h
  rw [Measure.snd_compProd, Measure.snd_compProd,
    klDiv_compProd_same_left_eq_lintegral μ ka kb hac] at h
  refine h.trans_eq ?_
  apply lintegral_congr_ae
  exact ae_of_all _ (fun i => klDiv_gaussianPiSmoothingKernel (a i) (b i) v hv)

end SKConstants
