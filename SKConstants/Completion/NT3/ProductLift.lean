module

public import SKConstants.Completion.T0.All
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.NT3

variable {X Y D : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace D]

theorem withDensity_map_fst (μ : Measure X) (κ : Measure D) [SFinite κ]
    (g : X × D → ℝ≥0∞) (hg : Measurable g) :
    ((μ.prod κ).withDensity g).map Prod.fst =
      μ.withDensity (fun x => ∫⁻ d, g (x, d) ∂κ) := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  have hφ' : Measurable (fun u : X × D => φ u.1) := hφ.comp measurable_fst
  rw [lintegral_map hφ measurable_fst,
    lintegral_withDensity_eq_lintegral_mul _ hg hφ',
    lintegral_prod _ ((hg.mul hφ').aemeasurable),
    lintegral_withDensity_eq_lintegral_mul _ hg.lintegral_prod_right' hφ]
  apply lintegral_congr
  intro x
  change (∫⁻ d, g (x, d) * φ x ∂κ) = (∫⁻ d, g (x, d) ∂κ) * φ x
  exact lintegral_mul_const (φ x) (show Measurable (fun d => g (x, d)) from
    hg.comp (measurable_const.prodMk measurable_id))

theorem conditional_normalization (ν : Measure Y) (κ : Measure D)
    [SigmaFinite ν] [SFinite κ] (g : Y × D → ℝ≥0∞) (hg : Measurable g)
    (h : ((ν.prod κ).withDensity g).map Prod.fst = ν) :
    ∀ᵐ y ∂ν, (∫⁻ d, g (y, d) ∂κ) = 1 := by
  apply (withDensity_eq_iff_of_sigmaFinite hg.lintegral_prod_right'.aemeasurable
    measurable_const.aemeasurable).mp
  rw [← withDensity_map_fst ν κ g hg, h]
  simp

theorem withDensity_static_pullback (μ : Measure X) (ν : Measure Y) (κ : Measure D)
    [SigmaFinite ν] [SFinite κ] (f : X → Y) (hf : Measurable f)
    (hlaw : μ.map f = ν) (g : Y × D → ℝ≥0∞) (hg : Measurable g)
    (h : ((ν.prod κ).withDensity g).map Prod.fst = ν) :
    ((μ.prod κ).withDensity (fun u => g (f u.1, u.2))).map Prod.fst = μ := by
  have hgm : Measurable (fun u : X × D => g (f u.1, u.2)) :=
    hg.comp (hf.prodMap measurable_id)
  rw [withDensity_map_fst μ κ _ hgm]
  have hmp : MeasurePreserving f μ ν := ⟨hf, hlaw⟩
  have he : ∀ᵐ x ∂μ, (∫⁻ d, g (f x, d) ∂κ) = 1 :=
    hmp.quasiMeasurePreserving.ae (conditional_normalization ν κ g hg h)
  rw [withDensity_congr_ae he]
  simp

end SKConstants.Completion.NT3
