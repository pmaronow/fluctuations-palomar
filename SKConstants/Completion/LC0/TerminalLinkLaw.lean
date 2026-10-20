module
public import SKConstants.Completion.LC0.TerminalLink
public import Mathlib.Probability.Independence.Integration

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
namespace SKConstants.M1

theorem terminalDensity_spin_lintegral {S : Type*} {N : ℕ}
    (β : ℝ) (H : ℝ≥0) (Y : S → Fin N → ℝ) (s : S) :
    (∫⁻ x, ENNReal.ofReal (TerminalDensity β H Y (x,s)) ∂spinPrior N) = 1 := by
  let F : Fin N → Bool → ℝ≥0∞ :=
    fun i b => ENNReal.ofReal (actualParisiSpinLinkDensity β b H (Y s i))
  have hF (i : Fin N) : Measurable (F i) := measurable_of_finite _
  have hind := iIndepFun_pi (μ := fun _ : Fin N => scalarHiddenPriorBool 0)
    (X := F) (fun i => (hF i).aemeasurable)
  change iIndepFun (fun i x => F i (x i)) (spinPrior N) at hind
  have hp (x : Fin N → Bool) :
      ENNReal.ofReal (TerminalDensity β H Y (x,s)) = ∏ i, F i (x i) :=
    ENNReal.ofReal_prod_of_nonneg fun i _ =>
      (actualParisiSpinLinkDensity_pos β (x i) H (Y s i)).le
  simp_rw [hp]
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => (hF i).comp (measurable_pi_apply i))]
  have he (i : Fin N) : (∫⁻ x, F i (x i) ∂spinPrior N) = 1 := by
    change (∫⁻ x, F i (x i) ∂Measure.pi (fun _ : Fin N => scalarHiddenPriorBool 0)) = 1
    rw [(measurePreserving_eval (fun _ : Fin N => scalarHiddenPriorBool 0) i).lintegral_comp
      (hF i)]
    exact lintegral_actualParisiSpinLinkDensity_bool β H (Y s i)
  simp only [he, Finset.prod_const_one]

theorem terminalLinkedLaw_base_marginal {S : Type*} [MeasurableSpace S] {N : ℕ}
    (β : ℝ) (H : ℝ≥0) (μ : Measure S) [SFinite μ]
    (Y : S → Fin N → ℝ) (hY : Measurable Y) :
    (TerminalLinkedLaw β H μ Y).map Prod.snd = μ := by
  let f : (Fin N → Bool) × S → ℝ≥0∞ :=
    fun u => ENNReal.ofReal (TerminalDensity β H Y u)
  have hf : Measurable f := (measurable_terminalDensity β H Y hY).ennreal_ofReal
  ext s hs
  rw [Measure.map_apply measurable_snd hs]
  change (((spinPrior N).prod μ).withDensity f) (Prod.snd ⁻¹' s) = _
  rw [withDensity_apply _ (measurable_snd hs), ← lintegral_indicator (measurable_snd hs),
    lintegral_prod_symm _ (hf.indicator (measurable_snd hs)).aemeasurable]
  have hinner (y : S) : (∫⁻ x, ((Prod.snd ⁻¹' s).indicator f) (x,y) ∂spinPrior N) =
      s.indicator (fun _ => (1 : ℝ≥0∞)) y := by
    by_cases hy : y ∈ s
    · rw [Set.indicator_of_mem hy]
      have hh (x : Fin N → Bool) : (Prod.snd ⁻¹' s).indicator f (x,y) = f (x,y) :=
        Set.indicator_of_mem (show (x,y) ∈ Prod.snd ⁻¹' s from hy) f
      simp_rw [hh]
      exact terminalDensity_spin_lintegral β H Y y
    · simp [hy]
  simp_rw [hinner]
  rw [lintegral_indicator hs]
  simp

theorem terminalLinkedLaw_probability {S : Type*} [MeasurableSpace S] {N : ℕ}
    (β : ℝ) (H : ℝ≥0) (μ : Measure S) [IsProbabilityMeasure μ]
    (Y : S → Fin N → ℝ) (hY : Measurable Y) :
    IsProbabilityMeasure (TerminalLinkedLaw β H μ Y) := by
  have hm := terminalLinkedLaw_base_marginal β H μ Y hY
  refine ⟨?_⟩
  have he := congrArg (fun ν : Measure S => ν univ) hm
  rw [Measure.map_apply measurable_snd MeasurableSet.univ] at he
  simpa using he

theorem terminalLinkedLaw_map {S T : Type*} [MeasurableSpace S] [MeasurableSpace T]
    {N : ℕ} (β : ℝ) (H : ℝ≥0) (μ : Measure S) [SFinite μ]
    (F : S → T) (hF : Measurable F)
    (Y : T → Fin N → ℝ) (hY : Measurable Y) :
    (TerminalLinkedLaw β H μ (Y ∘ F)).map (Prod.map id F) =
      TerminalLinkedLaw β H (μ.map F) Y := by
  let G : ((Fin N → Bool) × S) → ((Fin N → Bool) × T) := Prod.map id F
  have hG : Measurable G := measurable_id.prodMap hF
  let g : (Fin N → Bool) × T → ℝ≥0∞ :=
    fun u => ENNReal.ofReal (TerminalDensity β H Y u)
  have hg : Measurable g := (measurable_terminalDensity β H Y hY).ennreal_ofReal
  have hbase : ((spinPrior N).prod μ).map G = (spinPrior N).prod (μ.map F) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map (spinPrior N) μ measurable_id hF).symm
  change (((spinPrior N).prod μ).withDensity (g ∘ G)).map G = _
  have htransport : (((spinPrior N).prod μ).withDensity (g ∘ G)).map G =
      (((spinPrior N).prod μ).map G).withDensity g := by
    ext s hs
    rw [Measure.map_apply hG hs, withDensity_apply _ (hG hs), withDensity_apply _ hs,
      setLIntegral_map hs hg hG]
    rfl
  rw [htransport, hbase]
  rfl

end SKConstants.M1
