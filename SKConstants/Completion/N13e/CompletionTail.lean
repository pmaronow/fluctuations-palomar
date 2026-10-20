module

public import SKConstants.Completion.LM5.GrowingLinkedEnergy

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal Matrix

namespace SKConstants.Completion.N13e
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal LC5 LM5

theorem completionEnergy_product_tail {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] {n k : ℕ}
    (N : ℝ) (hN : 0 < N) (c : U → Fin k → ℝ) (y : U → Fin n → ℝ)
    (hc : Measurable c) (hy : Measurable y)
    (hbudget : ∀ a, (∑ j, c a j^2) ≤ 1)
    (hnorm : ∀ a, N⁻¹ * dot (y a) (y a) = 1-∑ j, c a j^2)
    (u : ℝ) (hu : 0 < u) :
    (μ.prod (completionNoiseLaw n k)).real
      {z | u ≤ |completionEnergy N (c z.1) (y z.1) z.2|} ≤ 2*Real.exp (-N*u^2) := by
  have hE : MeasurableSet {z : U × _ | u ≤ |completionEnergy N (c z.1) (y z.1) z.2|} :=
    measurableSet_le measurable_const (measurable_completionEnergy N c y hc hy).abs
  have hsection (a : U) : (completionNoiseLaw n k)
      {z | u ≤ |completionEnergy N (c a) (y a) z|} ≤ ENNReal.ofReal (2*Real.exp (-N*u^2)) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (completion_tail N hN _ _ (hbudget a) (hnorm a) u hu)
  have hle : (μ.prod (completionNoiseLaw n k))
      {z | u ≤ |completionEnergy N (c z.1) (y z.1) z.2|} ≤ ENNReal.ofReal (2*Real.exp (-N*u^2)) := by
    rw [Measure.prod_apply hE]
    calc
      _ ≤ ∫⁻ _a, ENNReal.ofReal (2*Real.exp (-N*u^2)) ∂μ := lintegral_mono hsection
      _ = _ := by simp
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

variable {S Past : Type*} [MeasurableSpace S] [MeasurableSpace Past]

theorem measurable_sourceDiscardedEnergy
    (r K : ℕ) (N : ℝ) (hN : 0 < N)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (initial : S → Past) (hi : Measurable initial)
    (htarget : ∀ j i, Measurable (fun a => target j a i))
    (hupdate : ∀ j, Measurable (Function.uncurry (update j)))
    (hblind : ∀ j p z w, (∀ i, z (.inl i) = w (.inl i)) → update j p z = update j p w) :
    Measurable (sourceDiscardedEnergy r K N target update initial) := by
  have hm := (measurable_completionEnergy N
    (visibleSpinCoefficients r K N target update initial)
    (visibleResidualSpin r K target update initial)
    (measurable_visibleSpinCoefficients r K N target update initial hi htarget hupdate)
    (measurable_visibleResidualSpin r K target update initial hi htarget hupdate)).comp
      (measurable_terminalSourceCompact (S := S) (r+K) K)
  convert hm using 1
  funext z
  exact sourceDiscardedEnergy_eq_completion r K N hN target update hblind initial z

theorem sourceDiscardedEnergy_tail (μ : Measure S) [IsProbabilityMeasure μ]
    (r K : ℕ) (hN : 0 < r+K) (β : ℝ) (H : ℝ≥0)
    (target : ℕ → Past → Fin (r+K) → ℝ)
    (update : ℕ → Past → EuclideanSpace ℝ (Fin (r+K) ⊕ Unit) → Past)
    (initial : S → Past) (hi : Measurable initial)
    (htarget : ∀ j i, Measurable (fun a => target j a i))
    (hupdate : ∀ j, Measurable (Function.uncurry (update j)))
    (hblind : ∀ j p z w, (∀ i, z (.inl i) = w (.inl i)) → update j p z = update j p w)
    (Y : S × PaperCompletionNoise (r+K) K → Fin (r+K) → ℝ) (hY : Measurable Y)
    (u : ℝ) (hu : 0 < u) :
    (terminalSourceLaw μ (r+K) K β H Y).real
      {z | u ≤ |sourceDiscardedEnergy r K (r+K:ℕ) target update initial z|} ≤
        2*Real.exp (-((r+K:ℕ):ℝ)*u^2) := by
  have hp : (0:ℝ) < (r+K:ℕ) := Nat.cast_pos.mpr hN
  let ν := M1.TerminalLinkedLaw β H (μ.prod (paperCompletionNoiseLaw (r+K) K)) Y
  have : IsProbabilityMeasure ν := M1.terminalLinkedLaw_probability β H _ Y hY
  let c := visibleSpinCoefficients r K (r+K:ℕ) target update initial
  let y := visibleResidualSpin r K target update initial
  have hc := measurable_visibleSpinCoefficients r K (r+K:ℕ) target update initial hi htarget hupdate
  have hy := measurable_visibleResidualSpin r K target update initial hi htarget hupdate
  have hE := measurableSet_le (measurable_const (a := u))
    (measurable_completionEnergy (r+K:ℕ) c y hc hy).abs
  have hlaw : HasLaw (terminalSourceCompact (S := S) (r+K) K)
      (ν.prod (completionNoiseLaw (r+K) K)) (terminalSourceLaw μ (r+K) K β H Y) :=
    ⟨(measurable_terminalSourceCompact _ _).aemeasurable,
      terminalSourceCompact_law μ _ _ β H Y hY⟩
  have he := hlaw.measureReal_eq hE
  have hpoint (z) : sourceDiscardedEnergy r K (r+K:ℕ) target update initial z =
      completionEnergy (r+K:ℕ) (c (terminalSourceCompact (r+K) K z).1)
        (y (terminalSourceCompact (r+K) K z).1) (terminalSourceCompact (r+K) K z).2 :=
    sourceDiscardedEnergy_eq_completion r K _ hp target update hblind initial z
  simp_rw [← hpoint] at he
  rw [he]
  exact completionEnergy_product_tail ν (r+K:ℕ) hp c y hc hy
    (fun z => actualPaper_coefficient_budget r K _ hp target update _ _ _ (signSpin_norm_sq z.1))
    (fun z => actualPaper_residual_norm_identity r K _ hp target update _ _ _ (signSpin_norm_sq z.1)) u hu

theorem measurable_growingSourceDiscardedEnergy {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0)
    (r K : ℕ) (hN : 0 < r+K) :
    Measurable (growingSourceDiscardedEnergy W β hβ δ r K) := by
  exact (measurable_sourceDiscardedEnergy r K (r+K:ℕ) (Nat.cast_pos.mpr hN)
    (M1.Target W β hβ δ r K) (M1.Update δ r K) (growingInitial δ r K)
    (measurable_scalarGrowingPaperInitialState _ _ _) (measurable_growingTarget W β hβ δ r K)
    (measurable_growingUpdate δ r K) (growingUpdate_blind δ r K)).comp
      (measurable_id.prodMap (measurable_growingProjectOriginal δ r K))

theorem growingSourceDiscardedEnergy_tail {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0)
    (r K : ℕ) (hN : 0 < r+K) (u : ℝ) (hu : 0 < u) :
    (M1.SourceLinkedLaw W β hβ δ r K).real
      {z | u ≤ |growingSourceDiscardedEnergy W β hβ δ r K z|} ≤
        2*Real.exp (-((r+K:ℕ):ℝ)*u^2) := by
  have hmp : MeasurePreserving (Prod.map id (growingProjectOriginal δ r K))
      (M1.SourceLinkedLaw W β hβ δ r K)
      (terminalSourceLaw (scalarGrowingPaperInitialDataLaw W (M1.Horizon δ K) δ (r+K))
        (r+K) K β (M1.Horizon δ K) (growingVisibleField W β hβ δ r K)) :=
    ⟨measurable_id.prodMap (measurable_growingProjectOriginal δ r K),
      growingSource_linked_original_law W β hβ δ r K⟩
  have hm := measurable_sourceDiscardedEnergy r K (r+K:ℕ) (Nat.cast_pos.mpr hN)
    (M1.Target W β hβ δ r K) (M1.Update δ r K) (growingInitial δ r K)
    (measurable_scalarGrowingPaperInitialState _ _ _) (measurable_growingTarget W β hβ δ r K)
    (measurable_growingUpdate δ r K) (growingUpdate_blind δ r K)
  have he := hmp.hasLaw.measureReal_eq (measurableSet_le (measurable_const (a := u)) hm.abs)
  change (M1.SourceLinkedLaw W β hβ δ r K).real
    {z | u ≤ |growingSourceDiscardedEnergy W β hβ δ r K z|} = _ at he
  rw [he]
  exact sourceDiscardedEnergy_tail
    (scalarGrowingPaperInitialDataLaw W (M1.Horizon δ K) δ (r+K)) r K hN β (M1.Horizon δ K)
    (M1.Target W β hβ δ r K) (M1.Update δ r K) (growingInitial δ r K)
    (measurable_scalarGrowingPaperInitialState _ _ _) (measurable_growingTarget W β hβ δ r K)
    (measurable_growingUpdate δ r K) (growingUpdate_blind δ r K)
    (growingVisibleField W β hβ δ r K) (measurable_growingVisibleField W β hβ δ r K) u hu

end SKConstants.Completion.N13e
