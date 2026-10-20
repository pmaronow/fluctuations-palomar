module

public import SKConstants.ScalarProcessInnovation
public import Mathlib.Probability.Kernel.Composition.MeasureComp
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Tactic

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SKConstants

lemma measurable_scalarPlusWeight : Measurable scalarPlusWeight := by
  unfold scalarPlusWeight
  fun_prop

lemma measurable_scalarMinusWeight : Measurable scalarMinusWeight := by
  unfold scalarMinusWeight
  fun_prop

theorem scalarKernelLaw_withDensity_plusWeight (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    (scalarKernelLaw z t).withDensity (fun y => ENNReal.ofReal (scalarPlusWeight y)) =
      ENNReal.ofReal (scalarPlusWeight z) • gaussianReal (z + t) t := by
  unfold scalarKernelLaw
  rw [← withDensity_mul volume (measurable_scalarKernel z t).ennreal_ofReal
    measurable_scalarPlusWeight.ennreal_ofReal]
  have he : (fun y => ENNReal.ofReal (scalarKernel z t y)) *
      (fun y => ENNReal.ofReal (scalarPlusWeight y)) =
        ENNReal.ofReal (scalarPlusWeight z) • gaussianPDF (z + t) t := by
    funext y
    change ENNReal.ofReal (scalarKernel z t y) * ENNReal.ofReal (scalarPlusWeight y) =
      ENNReal.ofReal (scalarPlusWeight z) * ENNReal.ofReal (gaussianPDFReal (z + t) t y)
    rw [← ENNReal.ofReal_mul (scalarKernel_nonneg z y t),
      scalarKernel_mul_plusWeight z y t ht,
      ENNReal.ofReal_mul (scalarPlusWeight_pos z).le]
  rw [he, withDensity_smul _ (measurable_gaussianPDF _ _),
    ← gaussianReal_of_var_ne_zero _ ht]

theorem scalarKernelLaw_withDensity_minusWeight (z : ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    (scalarKernelLaw z t).withDensity (fun y => ENNReal.ofReal (scalarMinusWeight y)) =
      ENNReal.ofReal (scalarMinusWeight z) • gaussianReal (z - t) t := by
  unfold scalarKernelLaw
  rw [← withDensity_mul volume (measurable_scalarKernel z t).ennreal_ofReal
    measurable_scalarMinusWeight.ennreal_ofReal]
  have he : (fun y => ENNReal.ofReal (scalarKernel z t y)) *
      (fun y => ENNReal.ofReal (scalarMinusWeight y)) =
        ENNReal.ofReal (scalarMinusWeight z) • gaussianPDF (z - t) t := by
    funext y
    change ENNReal.ofReal (scalarKernel z t y) * ENNReal.ofReal (scalarMinusWeight y) =
      ENNReal.ofReal (scalarMinusWeight z) * ENNReal.ofReal (gaussianPDFReal (z - t) t y)
    rw [← ENNReal.ofReal_mul (scalarKernel_nonneg z y t),
      scalarKernel_mul_minusWeight z y t ht,
      ENNReal.ofReal_mul (scalarMinusWeight_pos z).le]
  rw [he, withDensity_smul _ (measurable_gaussianPDF _ _),
    ← gaussianReal_of_var_ne_zero _ ht]

@[expose] def gaussianShiftKernel (s : ℝ≥0) (c : ℝ) : Kernel ℝ ℝ where
  toFun y := gaussianReal (y + c) s
  measurable' := by
    exact measurable_gaussianReal.comp ((measurable_id.add_const c).prodMk measurable_const)

instance gaussianShiftKernel_isMarkov (s : ℝ≥0) (c : ℝ) :
    IsMarkovKernel (gaussianShiftKernel s c) where
  isProbabilityMeasure y := by change IsProbabilityMeasure (gaussianReal (y + c) s); infer_instance

theorem gaussianShiftKernel_comp_gaussianReal (mu c : ℝ) (t s : ℝ≥0) :
    gaussianShiftKernel s c ∘ₘ gaussianReal mu t = gaussianReal (mu + c) (t + s) := by
  rw [← gaussianReal_conv_gaussianReal (m₁ := mu) (m₂ := c) (v₁ := t) (v₂ := s)]
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  rw [Measure.lintegral_bind (gaussianShiftKernel s c).aemeasurable hf.aemeasurable,
    Measure.lintegral_conv hf]
  apply lintegral_congr
  intro y
  change (∫⁻ x, f x ∂gaussianReal (y + c) s) = _
  have hg : gaussianReal (y + c) s = (gaussianReal c s).map (fun x => y + x) := by
    rw [gaussianReal_map_const_add]
    congr 1
    ring
  rw [hg, lintegral_map hf (by fun_prop)]

theorem lintegral_gaussianReal_shift (mu c : ℝ) (t s : ℝ≥0)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (∫⁻ y, gaussianReal (y + c) s A ∂gaussianReal mu t) =
      gaussianReal (mu + c) (t + s) A := by
  have h := congrArg (fun m : Measure ℝ => m A)
    (gaussianShiftKernel_comp_gaussianReal mu c t s)
  rw [Measure.bind_apply hA (gaussianShiftKernel s c).aemeasurable] at h
  exact h

theorem scalarTransitionKernel_comp_positive (z : ℝ) (t s : ℝ≥0)
    (ht : t ≠ 0) (hs : s ≠ 0) :
    scalarTransitionKernel s ∘ₘ scalarKernelLaw z t = scalarKernelLaw z (t + s) := by
  have hts : t + s ≠ 0 := by positivity
  have htrans : ∀ y, scalarTransitionKernel s y = scalarKernelLaw y s := by
    intro y
    change (if s = 0 then Measure.dirac y else scalarKernelLaw y s) = _
    simp [hs]
  ext A hA
  rw [Measure.bind_apply hA (scalarTransitionKernel s).aemeasurable]
  simp_rw [htrans, scalarKernelLaw_eq_mixture _ s hs, Measure.add_apply,
    Measure.smul_apply, smul_eq_mul]
  have hp : Measurable (fun y : ℝ => gaussianReal (y + (s : ℝ)) s A) :=
    (gaussianShiftKernel s (s : ℝ)).measurable_coe hA
  have hm : Measurable (fun y : ℝ => gaussianReal (y - (s : ℝ)) s A) := by
    change Measurable (fun y : ℝ => gaussianReal (y + -(s : ℝ)) s A)
    exact (gaussianShiftKernel s (-(s : ℝ))).measurable_coe hA
  have hpw : Measurable (fun y : ℝ =>
      ENNReal.ofReal (scalarPlusWeight y) * gaussianReal (y + s) s A) :=
    measurable_scalarPlusWeight.ennreal_ofReal.mul hp
  rw [lintegral_add_left hpw]
  have hplus : (∫⁻ y, ENNReal.ofReal (scalarPlusWeight y) * gaussianReal (y + s) s A
      ∂scalarKernelLaw z t) =
      ENNReal.ofReal (scalarPlusWeight z) * gaussianReal (z + (t : ℝ) + s) (t + s) A := by
    have hi : (∫⁻ y, gaussianReal (y + s) s A
        ∂(scalarKernelLaw z t).withDensity (fun y => ENNReal.ofReal (scalarPlusWeight y))) =
        ∫⁻ y, ENNReal.ofReal (scalarPlusWeight y) * gaussianReal (y + s) s A
          ∂scalarKernelLaw z t := by
      simpa only [Pi.mul_apply] using lintegral_withDensity_eq_lintegral_mul
        (scalarKernelLaw z t) measurable_scalarPlusWeight.ennreal_ofReal hp
    rw [← hi, scalarKernelLaw_withDensity_plusWeight z t ht, lintegral_smul_measure,
      lintegral_gaussianReal_shift _ _ _ _ A hA]
    rfl
  have hminus : (∫⁻ y, ENNReal.ofReal (scalarMinusWeight y) * gaussianReal (y - s) s A
      ∂scalarKernelLaw z t) =
      ENNReal.ofReal (scalarMinusWeight z) * gaussianReal (z - (t : ℝ) - s) (t + s) A := by
    have hi : (∫⁻ y, gaussianReal (y - s) s A
        ∂(scalarKernelLaw z t).withDensity (fun y => ENNReal.ofReal (scalarMinusWeight y))) =
        ∫⁻ y, ENNReal.ofReal (scalarMinusWeight y) * gaussianReal (y - s) s A
          ∂scalarKernelLaw z t := by
      simpa only [Pi.mul_apply] using lintegral_withDensity_eq_lintegral_mul
        (scalarKernelLaw z t) measurable_scalarMinusWeight.ennreal_ofReal hm
    rw [← hi, scalarKernelLaw_withDensity_minusWeight z t ht, lintegral_smul_measure]
    simp only [sub_eq_add_neg]
    rw [lintegral_gaussianReal_shift _ _ _ _ A hA]
    rfl
  rw [hplus, hminus, scalarKernelLaw_eq_mixture z (t + s) hts,
    Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [NNReal.coe_add, smul_eq_mul]
  congr 2 <;> congr 2 <;> ring

theorem scalarTransitionKernel_zero : scalarTransitionKernel 0 = Kernel.id := by
  apply Kernel.ext
  intro z
  change (if (0 : ℝ≥0) = 0 then Measure.dirac z else scalarKernelLaw z 0) = Measure.dirac z
  simp

theorem scalarTransitionKernel_semigroup_apply (z : ℝ) (t s : ℝ≥0) :
    scalarTransitionKernel (t + s) z =
      scalarTransitionKernel s ∘ₘ scalarTransitionKernel t z := by
  by_cases ht : t = 0
  · subst t
    rw [zero_add, scalarTransitionKernel_zero]
    change _ = scalarTransitionKernel s ∘ₘ Measure.dirac z
    rw [Measure.dirac_bind (scalarTransitionKernel s).measurable]
  · by_cases hs : s = 0
    · subst s
      rw [add_zero, scalarTransitionKernel_zero, Measure.id_comp]
    · have hts : t + s ≠ 0 := by positivity
      have htrans : scalarTransitionKernel t z = scalarKernelLaw z t := by
        change (if t = 0 then Measure.dirac z else scalarKernelLaw z t) = _
        simp [ht]
      have htrans' : scalarTransitionKernel (t + s) z = scalarKernelLaw z (t + s) := by
        change (if t + s = 0 then Measure.dirac z else scalarKernelLaw z (t + s)) = _
        simp [hts]
      rw [htrans, htrans']
      exact (scalarTransitionKernel_comp_positive z t s ht hs).symm

theorem scalarTransitionKernel_semigroup (t s : ℝ≥0) :
    scalarTransitionKernel (t + s) = scalarTransitionKernel s ∘ₖ scalarTransitionKernel t := by
  apply Kernel.ext
  intro z
  rw [Kernel.comp_apply]
  exact scalarTransitionKernel_semigroup_apply z t s

end SKConstants
