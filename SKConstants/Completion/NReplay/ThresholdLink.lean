module

public import SKConstants.Completion.Blueprint.NodesLower

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators unitInterval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.NReplay
open SKConstantsOAI.ZeroTemperatureSK Blueprint

theorem scalar_threshold_probability (m : ℝ) (hm : m ∈ Icc (-1 : ℝ) 1) (b : Bool) :
    (volume : Measure I) {u | decide ((u : ℝ) < (1 + m) / 2) = b} =
      ENNReal.ofReal ((1 + scalarHiddenSign b * m) / 2) := by
  let p : I := ⟨(1 + m) / 2, by constructor <;> linarith [hm.1, hm.2]⟩
  cases b with
  | false =>
    have he : {u : I | decide ((u : ℝ) < (1 + m) / 2) = false} = Ici p := by
      ext u
      change (decide ((u : ℝ) < (1 + m) / 2) = false) ↔ (1 + m) / 2 ≤ (u : ℝ)
      simp
    rw [he, unitInterval.volume_Ici]
    congr 1
    simp only [scalarHiddenSign, Bool.false_eq_true, ↓reduceIte, p]
    ring
  | true =>
    have he : {u : I | decide ((u : ℝ) < (1 + m) / 2) = true} = Iio p := by
      ext u
      change (decide ((u : ℝ) < (1 + m) / 2) = true) ↔ (u : ℝ) < (1 + m) / 2
      simp
    rw [he, unitInterval.volume_Iio]
    simp [p, scalarHiddenSign]

theorem thresholdSpin_law {N : ℕ} (β : ℝ) (H : ℝ≥0) (y : Fin N → ℝ) :
    (thresholdLaw N).map
      (thresholdSpin (fun i => actualParisiFullMagnetization β H (y i))) =
      (M1.spinPrior N).withDensity
        (fun x => ENNReal.ofReal (M1.TerminalDensity β H (fun _ : Unit => y) (x, ()))) := by
  have ht : Measurable (thresholdSpin (fun i => actualParisiFullMagnetization β H (y i))) :=
    (measurable_thresholdSpin N).comp (measurable_const.prodMk measurable_id)
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply ht (measurableSet_singleton x),
    withDensity_apply _ (measurableSet_singleton x), lintegral_singleton]
  have hp : thresholdSpin (fun i => actualParisiFullMagnetization β H (y i)) ⁻¹' {x} =
      Set.univ.pi (fun i => {u : I |
        decide ((u : ℝ) < (1 + actualParisiFullMagnetization β H (y i)) / 2) = x i}) := by
    ext u
    simp [thresholdSpin, funext_iff]
  rw [hp, Measure.pi_pi]
  have hprior (b : Bool) : (scalarHiddenPriorBool 0) {b} = ENNReal.ofReal (1 / 2 : ℝ) := by
    cases b <;> simp [scalarHiddenPriorBool, scalarPlusWeight, scalarMinusWeight]
  rw [M1.spinPrior, Measure.pi_singleton]
  simp only [M1.TerminalDensity]
  rw [ENNReal.ofReal_prod_of_nonneg
    (fun i _ => (actualParisiSpinLinkDensity_pos β (x i) H (y i)).le),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [scalar_threshold_probability _
      (let h := actualParisiFullMagnetization_strict_bounds β H (y i); ⟨h.1.le, h.2.le⟩),
    hprior, ← ENNReal.ofReal_mul (actualParisiSpinLinkDensity_pos β (x i) H (y i)).le]
  congr 1
  unfold actualParisiSpinLinkDensity
  ring

theorem threshold_terminalLinkedLaw {S : Type*} [MeasurableSpace S] {N : ℕ}
    (β : ℝ) (H : ℝ≥0) (μ : Measure S) [IsProbabilityMeasure μ]
    (Y : S → Fin N → ℝ) (hY : Measurable Y) :
    (μ.prod (thresholdLaw N)).map (fun z =>
      (thresholdSpin (fun i => actualParisiFullMagnetization β H (Y z.1 i)) z.2, z.1)) =
      M1.TerminalLinkedLaw β H μ Y := by
  let M : S → Fin N → ℝ := fun s i => actualParisiFullMagnetization β H (Y s i)
  have hM : Measurable M := Measurable.of_eval (fun i =>
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable.comp
        ((measurable_pi_apply i).comp hY))
  let G : S × (Fin N → I) → (Fin N → Bool) × S :=
    fun z => (thresholdSpin (M z.1) z.2, z.1)
  have hG : Measurable G :=
    ((measurable_thresholdSpin N).comp
      ((hM.comp measurable_fst).prodMk measurable_snd)).prodMk measurable_fst
  let D : (Fin N → Bool) × S → ℝ≥0∞ :=
    fun z => ENNReal.ofReal (M1.TerminalDensity β H Y z)
  have hD : Measurable D := (M1.measurable_terminalDensity β H Y hY).ennreal_ofReal
  change (μ.prod (thresholdLaw N)).map G = _
  ext E hE
  rw [Measure.map_apply hG hE]
  change (μ.prod (thresholdLaw N)) (G ⁻¹' E) =
    (((M1.spinPrior N).prod μ).withDensity D) E
  rw [← lintegral_indicator_fun_one (hG hE)]
  rw [lintegral_prod _ ((measurable_const (a := (1 : ℝ≥0∞))).indicator (hG hE)).aemeasurable,
    withDensity_apply _ hE, ← lintegral_indicator hE,
    lintegral_prod_symm _ (hD.indicator hE).aemeasurable]
  apply lintegral_congr
  intro s
  have ht : Measurable (thresholdSpin (M s)) :=
    (measurable_thresholdSpin N).comp (measurable_const.prodMk measurable_id)
  have hsection : Measurable (fun x : Fin N → Bool => E.indicator (fun _ => (1 : ℝ≥0∞)) (x,s)) :=
    (measurable_const.indicator hE).comp (measurable_id.prodMk measurable_const)
  have he : (fun u => (G ⁻¹' E).indicator (fun _ => (1 : ℝ≥0∞)) (s,u)) =
      (fun x : Fin N → Bool => E.indicator (fun _ => (1 : ℝ≥0∞)) (x,s)) ∘
        thresholdSpin (M s) := by
    funext u
    rfl
  rw [he]
  simp only [Function.comp_def]
  rw [← lintegral_map hsection ht, thresholdSpin_law β H (Y s)]
  rw [lintegral_withDensity_eq_lintegral_mul₀ (measurable_of_finite _).aemeasurable
    hsection.aemeasurable]
  apply lintegral_congr
  intro x
  by_cases hx : (x,s) ∈ E <;> simp [hx, D, M1.TerminalDensity]

end SKConstants.NReplay
