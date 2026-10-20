module
public import SKConstants.ParisiSpinLinkCoefficient
public import SKConstants.ParisiBrownianMarkov

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK ParisiFullSupport

lemma lintegral_scalarHiddenPriorBool_zero (f : Bool → ℝ≥0∞) :
    (∫⁻ b, f b ∂scalarHiddenPriorBool 0) = ENNReal.ofReal (1/(2 : ℝ))*f true+
      ENNReal.ofReal (1/(2 : ℝ))*f false := by
  simp [scalarHiddenPriorBool,scalarPlusWeight,scalarMinusWeight,lintegral_add_measure,
    lintegral_smul_measure,smul_eq_mul]

lemma lintegral_actualParisiSpinLinkDensity_bool (β v y : ℝ) :
    (∫⁻ b, ENNReal.ofReal (actualParisiSpinLinkDensity β b v y) ∂scalarHiddenPriorBool 0) = 1 := by
  rw [lintegral_scalarHiddenPriorBool_zero,
    ← ENNReal.ofReal_mul (by norm_num : 0 ≤ 1/(2 : ℝ)),
    ← ENNReal.ofReal_mul (by norm_num : 0 ≤ 1/(2 : ℝ)),
    ← ENNReal.ofReal_add (mul_nonneg (by norm_num) (actualParisiSpinLinkDensity_pos β true v y).le)
      (mul_nonneg (by norm_num) (actualParisiSpinLinkDensity_pos β false v y).le)]
  convert ENNReal.ofReal_one using 1
  simp only [actualParisiSpinLinkDensity,scalarHiddenSign,Bool.false_eq_true,↓reduceIte]
  ring

def actualParisiFullTerminalField {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ) (W : BrownianSystem Ω) (T : ℝ≥0) : Ω → ℝ :=
  (actualParisiFullScalarDrift β).solution W.driver T

def actualParisiFullTerminalSpinDensity {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ) (W : BrownianSystem Ω) (T : ℝ≥0) (u : Bool × Ω) : ℝ :=
  actualParisiSpinLinkDensity β u.1 T (actualParisiFullTerminalField β W T u.2)

def actualParisiFullTerminalSpinLaw {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ) (W : BrownianSystem Ω) (T : ℝ≥0) : Measure (Bool × Ω) :=
  ((scalarHiddenPriorBool 0).prod W.law).withDensity
    (fun u => ENNReal.ofReal (actualParisiFullTerminalSpinDensity β W T u))

lemma measurable_actualParisiFullTerminalSpinDensity {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ) (W : BrownianSystem Ω) (T : ℝ≥0) :
    Measurable (actualParisiFullTerminalSpinDensity β W T) := by
  change Measurable (fun u : Bool × Ω => 1+scalarHiddenSign u.1 *
    actualParisiFullMagnetization β T (actualParisiFullTerminalField β W T u.2))
  have hY : Measurable (actualParisiFullTerminalField β W T) := by
    change Measurable ((actualParisiFullScalarDrift β).solution W.driver T)
    exact (actualParisiFullScalarDrift β).solution_measurable W T
  have hm : Measurable (fun u : Bool × Ω => actualParisiFullMagnetization β T
      (actualParisiFullTerminalField β W T u.2)) :=
    ((continuous_actualParisiFullMagnetization β).comp
      ((continuous_const : Continuous (fun _ : ℝ => (T : ℝ))).prodMk continuous_id)).measurable.comp
        (hY.comp measurable_snd)
  exact measurable_const.add (((measurable_of_finite scalarHiddenSign).comp measurable_fst).mul hm)

lemma actualParisiFullTerminalSpinDensity_pos {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ) (W : BrownianSystem Ω) (T : ℝ≥0) (u : Bool × Ω) :
    0 < actualParisiFullTerminalSpinDensity β W T u := actualParisiSpinLinkDensity_pos _ _ _ _

theorem actualParisiFullTerminalSpinLaw_path_marginal {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ) (W : BrownianSystem Ω) (T : ℝ≥0) :
    (actualParisiFullTerminalSpinLaw β W T).map Prod.snd = W.law := by
  letI := W.isProbability
  let f : Bool × Ω → ℝ≥0∞ := fun u => ENNReal.ofReal (actualParisiFullTerminalSpinDensity β W T u)
  have hf : Measurable f := (measurable_actualParisiFullTerminalSpinDensity β W T).ennreal_ofReal
  ext s hs
  rw [Measure.map_apply measurable_snd hs]
  change (((scalarHiddenPriorBool 0).prod W.law).withDensity f) (Prod.snd ⁻¹' s) = _
  rw [withDensity_apply _ (measurable_snd hs),← lintegral_indicator (measurable_snd hs),
    lintegral_prod_symm _ (hf.indicator (measurable_snd hs)).aemeasurable]
  have hinner (ω : Ω) : (∫⁻ b, ((Prod.snd ⁻¹' s).indicator f) (b,ω) ∂scalarHiddenPriorBool 0) =
      s.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    by_cases hω : ω ∈ s
    · rw [Set.indicator_of_mem hω]
      have hh (b : Bool) : (Prod.snd ⁻¹' s).indicator f (b,ω) = f (b,ω) :=
        Set.indicator_of_mem (show (b,ω) ∈ Prod.snd ⁻¹' s from hω) f
      simp_rw [hh]
      exact lintegral_actualParisiSpinLinkDensity_bool β T (actualParisiFullTerminalField β W T ω)
    · simp [hω]
  simp_rw [hinner]
  rw [lintegral_indicator hs]
  simp

instance actualParisiFullTerminalSpinLaw_isProbability {Ω : Type*} [MeasurableSpace Ω]
    (β : ℝ) (W : BrownianSystem Ω) (T : ℝ≥0) :
    IsProbabilityMeasure (actualParisiFullTerminalSpinLaw β W T) := by
  have hm := actualParisiFullTerminalSpinLaw_path_marginal β W T
  have he : (actualParisiFullTerminalSpinLaw β W T) univ = W.law univ := by
    rw [← hm,Measure.map_apply measurable_snd MeasurableSet.univ]
    simp
  exact ⟨he.trans W.isProbability.measure_univ⟩

end SKConstants
