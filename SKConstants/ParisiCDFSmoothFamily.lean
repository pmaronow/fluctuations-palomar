module

public import SKConstants.ParisiCDFDiffusion
public import SKConstants.Upstream.OAI.Probability.SKSupport.Regularity.BoundedSmoothFamily

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

def cdfStripTime (T t : ℝ) : ℝ := max 0 (min t T)

lemma cdfStripTime_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    cdfStripTime T t ∈ Icc (0 : ℝ) T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

lemma continuous_cdfStripTime (T : ℝ) : Continuous (cdfStripTime T) := by
  unfold cdfStripTime
  fun_prop

lemma scalarCDF_gradient_eq_deriv {α : ℝ → ℝ}
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hm : Monotone α)
    (β s : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    scalarCDFGradient β α s t = deriv (scalarCDFValue β α s t) := by
  funext x
  exact (scalarCDFValue_hasDerivAt β ha hm s t ht x).deriv.symm

lemma scalarCDF_strip_gradient_bounds (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT : T < 1) (m : ℕ) :
    ∃ C : ℝ≥0, ∀ r ∈ Icc (0 : ℝ) T, ∀ x,
      |iteratedDeriv m (scalarCDFGradient β α r (Real.toNNReal (1-r))) x| ≤ C := by
  have ht1 {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) : Real.toNNReal (1-r) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith [hr.1]
  cases m with
  | zero =>
    refine ⟨1, ?_⟩
    intro r hr x
    simpa only [iteratedDeriv_zero, NNReal.coe_one] using
      (scalarCDF_derivative_bounds β ha α.mono r _ (ht1 hr) x).1
  | succ m =>
    obtain ⟨C, hC, hb⟩ := scalarCDFValue_uniform_strip_derivative_bounds ha α.mono hβ hT m
    refine ⟨Real.toNNReal C, ?_⟩
    intro r hr x
    rw [scalarCDF_gradient_eq_deriv ha α.mono β r _ (ht1 hr)]
    simpa only [iteratedDeriv_succ', Real.coe_toNNReal C hC] using hb r hr x

lemma scalarCDF_strip_gradient_smooth (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hβ : β ≠ 0)
    {T : ℝ} (hT : T < 1) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) :
    ContDiff ℝ ∞ (scalarCDFGradient β α r (Real.toNNReal (1-r))) := by
  have ht1 : Real.toNNReal (1-r) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith [hr.1]
  rw [scalarCDF_gradient_eq_deriv ha α.mono β r _ ht1]
  exact (contDiff_infty_iff_deriv.mp
    (scalarCDFValue_contDiff_and_higher_derivative_limit ha α.mono hβ r _
      (by rw [Real.coe_toNNReal _ (by linarith [hr.2])]; linarith [hr.2]) ht1).1).2

lemma scalarCDF_strip_gradient_family (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T : ℝ} (hT0 : 0 ≤ T) (hT : T < 1) :
    BoundedSmoothFamily (fun t => scalarCDFGradient β α (cdfStripTime T t)
      (Real.toNNReal (1-cdfStripTime T t))) := by
  have hr (t : ℝ) : cdfStripTime T t ∈ Icc (0 : ℝ) T := cdfStripTime_mem hT0 t
  have hr1 (t : ℝ) : cdfTimeClamp (cdfStripTime T t) = cdfStripTime T t :=
    cdfTimeClamp_eq ⟨(hr t).1, (hr t).2.trans hT.le⟩
  have hmeas : Measurable (fun p : ℝ × ℝ =>
      scalarCDFGradient β α (cdfStripTime T p.1)
        (Real.toNNReal (1-cdfStripTime T p.1)) p.2) := by
    have H := (continuous_clamped_CDFGradient β α ha h1).measurable.comp
      (((continuous_cdfStripTime T).measurable.comp measurable_fst).prodMk measurable_snd)
    simpa only [Function.comp_def, hr1] using H
  have hb (m : ℕ) : ∃ C : ℝ≥0, ∀ t x,
      |iteratedDeriv m (scalarCDFGradient β α (cdfStripTime T t)
        (Real.toNNReal (1-cdfStripTime T t))) x| ≤ C := by
    obtain ⟨C, hC⟩ := scalarCDF_strip_gradient_bounds β α ha hβ hT0 hT m
    exact ⟨C, fun t x => hC _ (hr t) x⟩
  refine ⟨hmeas, ?_, hb⟩
  intro t
  refine ⟨scalarCDF_strip_gradient_smooth β α ha hβ hT (hr t), ?_⟩
  intro m
  obtain ⟨C, hC⟩ := hb m
  exact ⟨C, hC t⟩

lemma scalarCDFValue_regularDatum (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (hβ : β ≠ 0)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    RegularDatum (scalarCDFValue β α r (Real.toNNReal (1-r))) := by
  have ht1 : Real.toNNReal (1-r) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith
  refine ⟨(scalarCDFValue_contDiff_and_higher_derivative_limit ha α.mono hβ r _
    (by rw [Real.coe_toNNReal _ (by linarith)]; linarith) ht1).1, ?_⟩
  rw [← scalarCDF_gradient_eq_deriv ha α.mono β r _ ht1]
  refine ⟨scalarCDF_strip_gradient_smooth β α ha hβ hr1 ⟨hr0, le_rfl⟩, ?_⟩
  intro m
  obtain ⟨C, hC⟩ := scalarCDF_strip_gradient_bounds β α ha hβ hr0 hr1 m
  exact ⟨C, hC r ⟨hr0, le_rfl⟩⟩

end SKConstants.ParisiFullSupport
