module

public import SKConstants.JointGibbs
public import Mathlib.MeasureTheory.Integral.Bochner.Set

public section
noncomputable section
open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory

namespace SKConstants

theorem jointGibbs_typical_start_bound {n : ℕ} (beta : ℝ)
    (μ : Measure (Matrix (Fin n) (Fin n) ℝ)) [IsProbabilityMeasure μ]
    (good : Set (Matrix (Fin n) (Fin n) ℝ)) (hgood : MeasurableSet good)
    (err : Matrix (Fin n) (Fin n) ℝ × Spin n → ℝ) (herr : Measurable err)
    (herr_nonneg : ∀ z, 0 ≤ err z) (herr_le_one : ∀ z, err z ≤ 1)
    (B delta : ℝ) (hB : 0 ≤ B) (hdelta : 0 < delta)
    (haverage : ∀ W ∈ good, ∑ x, gibbsProbability beta W x * err (W, x) ≤ B) :
    (jointGibbsMeasure beta μ).real {z | delta < err z} ≤
      μ.real goodᶜ + B / delta := by
  let ν := jointGibbsMeasure beta μ
  have : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  let f : Matrix (Fin n) (Fin n) ℝ × Spin n → ℝ :=
    (Prod.fst ⁻¹' good).indicator err
  have hfmeas : Measurable f := herr.indicator (hgood.preimage measurable_fst)
  have hfnonneg : ∀ z, 0 ≤ f z := by
    intro z
    exact Set.indicator_nonneg (fun z _ ↦ herr_nonneg z) z
  have hfle : ∀ z, f z ≤ 1 := by
    intro z
    by_cases hz : z.1 ∈ good <;> simp [f, hz, herr_le_one z]
  have hfint : Integrable f ν :=
    (integrable_const (1 : ℝ)).mono' hfmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z ↦ by simpa [Real.norm_eq_abs, abs_of_nonneg (hfnonneg z)] using hfle z)
  have hint : ∫ z, f z ∂ν ≤ B := by
    rw [show ν = μ ⊗ₘ gibbsKernel n beta from rfl, Measure.integral_compProd hfint]
    calc
      (∫ W, ∫ x, f (W, x) ∂gibbsKernel n beta W ∂μ) ≤ ∫ _, B ∂μ := by
        apply integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun W ↦ integral_nonneg (fun x ↦ hfnonneg (W, x)))
          (integrable_const B)
        apply Filter.Eventually.of_forall
        intro W
        by_cases hW : W ∈ good
        · simpa [f, hW, integral_gibbsKernel] using haverage W hW
        · simp [f, hW, hB]
      _ = B := by simp
  have hmarkov : ν {z | z.1 ∈ good ∧ delta < err z} ≤ ENNReal.ofReal (B / delta) := by
    refine ((hfint.div_const delta).measure_le_integral
      (Filter.Eventually.of_forall fun z ↦ div_nonneg (hfnonneg z) hdelta.le) ?_).trans ?_
    · intro z hz
      exact (le_div_iff₀ hdelta).mpr (by simpa [f, hz.1] using hz.2.le)
    · rw [integral_div]
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hint hdelta.le)
  have hmarkovreal : ν.real {z | z.1 ∈ good ∧ delta < err z} ≤ B / delta := by
    exact ENNReal.toReal_le_of_le_ofReal (div_nonneg hB hdelta.le) hmarkov
  have hbad : ν.real (Prod.fst ⁻¹' goodᶜ) = μ.real goodᶜ := by
    change ((μ ⊗ₘ gibbsKernel n beta) (Prod.fst ⁻¹' goodᶜ)).toReal = _
    rw [← Measure.fst_apply hgood.compl, Measure.fst_compProd]
    rfl
  calc
    ν.real {z | delta < err z} ≤
        ν.real ((Prod.fst ⁻¹' goodᶜ) ∪ {z | z.1 ∈ good ∧ delta < err z}) := by
      apply measureReal_mono ?_ (measure_ne_top ν _)
      intro z hz
      by_cases hg : z.1 ∈ good
      · exact Or.inr ⟨hg, hz⟩
      · exact Or.inl hg
    _ ≤ ν.real (Prod.fst ⁻¹' goodᶜ) + ν.real {z | z.1 ∈ good ∧ delta < err z} :=
      measureReal_union_le _ _
    _ ≤ μ.real goodᶜ + B / delta := by rw [hbad]; exact add_le_add le_rfl hmarkovreal

end SKConstants
