module

public import SKConstants.ScalarProcessCausalReconstruction
public import SKConstants.ScalarProcessInnovationBrownian

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

theorem exists_aemeasurable_scalarPathVersion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ≥0) (Y : ℝ → Ω → ℝ)
    (hY : ∀ s, AEMeasurable (Y s) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun s => Y s ω)) :
    ∃ paths : Ω → ScalarContinuousPath T, Measurable paths ∧
      ∀ᵐ ω ∂P, ∀ t : Icc (0 : ℝ) (T : ℝ), paths ω t = Y t ω := by
  let samples : Ω → ℕ → ℝ := fun ω k =>
    (hY (scalarPathDenseTimes T k)).mk (Y (scalarPathDenseTimes T k)) ω
  have hs : Measurable samples := Measurable.of_eval (fun k =>
    (hY (scalarPathDenseTimes T k)).measurable_mk)
  have he : ∀ᵐ ω ∂P, ∀ k, samples ω k = Y (scalarPathDenseTimes T k) ω := by
    apply ae_all_iff.2
    intro k
    exact (hY (scalarPathDenseTimes T k)).ae_eq_mk.symm
  let paths := scalarPathFromDenseSamples T ∘ samples
  refine ⟨paths, (measurable_scalarPathFromDenseSamples T).comp hs, ?_⟩
  filter_upwards [he, hcont] with ω hw hc
  let f := scalarContinuousPathRestriction T (fun s => Y s ω) hc
  have hsf : samples ω = scalarPathDenseSamples T f := by
    funext k
    exact hw k
  have hpf : paths ω = f := by
    change scalarPathFromDenseSamples T (samples ω) = f
    rw [hsf]
    exact scalarPathFromDenseSamples_leftInverse T f
  intro t
  rw [hpf]
  rfl

theorem scalarHiddenBrownian_actual_pathVersions {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ≥0) (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∃ Ypaths Mpaths : Bool × Ω → ScalarContinuousPath T,
      Measurable Ypaths ∧ Measurable Mpaths ∧
      (∀ u, Mpaths u = scalarInnovationPath T z (Ypaths u)) ∧
      (∀ᵐ u ∂scalarHiddenBrownianLaw z P,
        ∀ t : Icc (0 : ℝ) (T : ℝ),
          Ypaths u t = scalarHiddenContinuousField z B ⟨t, t.property.1⟩ u ∧
          Mpaths u t = scalarContinuousInnovation z B ⟨t, t.property.1⟩ u) ∧
      MeasurableSpace.comap Ypaths inferInstance =
        MeasurableSpace.comap Mpaths inferInstance := by
  have hcontB : ∀ᵐ u : Bool × Ω ∂scalarHiddenBrownianLaw z P,
      Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hB.cont
  have hcontY : ∀ᵐ u : Bool × Ω ∂scalarHiddenBrownianLaw z P,
      Continuous (fun s => scalarHiddenFieldReal z B s u) :=
    hcontB.mono (fun u hu => continuous_scalarHiddenFieldReal z B u hu)
  obtain ⟨Ypaths, hYm, hYe⟩ := exists_aemeasurable_scalarPathVersion
    (scalarHiddenBrownianLaw z P) T (scalarHiddenFieldReal z B)
    (aemeasurable_scalarHiddenFieldReal P z B hB.toIsPreBrownianReal) hcontY
  let Mpaths := fun u => scalarInnovationPath T z (Ypaths u)
  refine ⟨Ypaths, Mpaths, hYm, (measurable_scalarInnovationPath T z).comp hYm,
    fun _ => rfl, ?_, ?_⟩
  · filter_upwards [hYe, hcontB] with u hu hc
    have hpath : Ypaths u = scalarContinuousPathRestriction T
        (fun s => scalarHiddenFieldReal z B s u)
        (continuous_scalarHiddenFieldReal z B u hc) := by
      ext t
      exact hu t
    intro t
    constructor
    · rw [hu t]
      unfold scalarHiddenFieldReal scalarHiddenContinuousField
      simp only [Real.toNNReal_of_nonneg t.property.1]
      rfl
    · change scalarInnovationPath T z (Ypaths u) t = _
      rw [hpath]
      exact scalarInnovationPath_hiddenField_eq T z B u hc t
  · exact (scalarInnovationPath_comap_eq T z Ypaths).symm

theorem scalarContinuousInnovation_future_indep_observationPaths {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ≥0)
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∃ Ypaths : Bool × Ω → ScalarContinuousPath T,
      Measurable Ypaths ∧
      (∀ᵐ u ∂scalarHiddenBrownianLaw z P, ∀ t : Icc (0 : ℝ) (T : ℝ),
        Ypaths u t = scalarHiddenContinuousField z B ⟨t, t.property.1⟩ u) ∧
      IndepFun
        (fun u t => scalarContinuousInnovation z B (T + t) u -
          scalarContinuousInnovation z B T u)
        Ypaths (scalarHiddenBrownianLaw z P) := by
  obtain ⟨Ypaths, Mpaths, hYm, hMm, hdef, he, hsig⟩ :=
    scalarHiddenBrownian_actual_pathVersions P T z B hB
  have hM := (scalarContinuousInnovation_isBrownianReal P z B hB).toIsPreBrownianReal
  have hMe : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, ∀ t : Icc (0 : ℝ) (T : ℝ),
      Mpaths u t = scalarContinuousInnovation z B ⟨t, t.property.1⟩ u :=
    he.mono (fun u hu t => (hu t).2)
  have hi := brownian_indepFun_shift_scalarPathVersion (scalarHiddenBrownianLaw z P)
    T (scalarContinuousInnovation z B) hM Mpaths hMe
  have hd : Mpaths = fun u => scalarInnovationPath T z (Ypaths u) := funext hdef
  rw [hd] at hi
  refine ⟨Ypaths, hYm, he.mono (fun u hu t => (hu t).1), ?_⟩
  exact indepFun_scalarObservationPath_of_innovation (scalarHiddenBrownianLaw z P)
    T z Ypaths _ hi

theorem scalarContinuousInnovation_indepFun_shift_observationPast {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ≥0)
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    IndepFun
      (fun u t => scalarContinuousInnovation z B (T + t) u -
        scalarContinuousInnovation z B T u)
      (fun u (t : Iic T) => scalarHiddenContinuousField z B t u)
      (scalarHiddenBrownianLaw z P) := by
  obtain ⟨Ypaths, hYm, he, hi⟩ :=
    scalarContinuousInnovation_future_indep_observationPaths P T z B hB
  let Φ : ScalarContinuousPath T → Iic T → ℝ :=
    fun f t => f ⟨(t : ℝ≥0), (t : ℝ≥0).coe_nonneg, t.property⟩
  have hΦ : Measurable Φ := Measurable.of_eval (fun t => ContinuousMap.measurable_eval _)
  have hiΦ := hi.comp (φ := id) (ψ := Φ) measurable_id hΦ
  have heΦ : Φ ∘ Ypaths =ᵐ[scalarHiddenBrownianLaw z P]
      (fun u (t : Iic T) => scalarHiddenContinuousField z B t u) := by
    filter_upwards [he] with u hu
    funext t
    exact hu ⟨(t : ℝ≥0), (t : ℝ≥0).coe_nonneg, t.property⟩
  exact hiΦ.congr (Filter.Eventually.of_forall (fun _ => rfl)) heΦ

end SKConstants
