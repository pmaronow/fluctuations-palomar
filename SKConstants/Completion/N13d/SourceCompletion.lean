module

public import SKConstants.Completion.N13d.ConditionalGaussian
public import SKConstants.Completion.N13d.ScalarWeights
public import SKConstants.Completion.LM5.GrowingCompletionLaw
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal RealInnerProductSpace

namespace SKConstants.Completion.N13d
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal LC5 LM5 LGram
variable {Ω : Type*} [MeasurableSpace Ω]

abbrev GrowingTranscript (δ : ℝ≥0) (r K : ℕ) :=
  (Fin (r+K) → Bool) × GrowingVisible δ r K

def growingTranscriptLaw (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) : Measure (GrowingTranscript δ r K) :=
  M1.TerminalLinkedLaw β (M1.Horizon δ K)
    ((scalarGrowingPaperInitialDataLaw W (M1.Horizon δ K) δ (r+K)).prod
      (paperCompletionNoiseLaw (r+K) K)) (growingVisibleField W β hβ δ r K)

instance growingTranscriptLaw_probability (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) : IsProbabilityMeasure (growingTranscriptLaw W β hβ δ r K) :=
  M1.terminalLinkedLaw_probability β (M1.Horizon δ K) _ _
    (measurable_growingVisibleField W β hβ δ r K)

def growingCoefficients (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (t : GrowingTranscript δ r K) : EuclideanSpace ℝ (Fin K) :=
  WithLp.toLp 2 (visibleSpinCoefficients r K (r+K:ℕ)
    (M1.Target W β hβ δ r K) (M1.Update δ r K) (growingInitial δ r K) t)

def growingResidual (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) : GrowingTranscript δ r K → Fin (r+K) → ℝ :=
  visibleResidualSpin r K (M1.Target W β hβ δ r K) (M1.Update δ r K) (growingInitial δ r K)

def growingS (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (K : ℕ) :=
  populationTargetSpin W W β hβ (growingQueryTime δ)
    (fun j => growingQueryTime δ (j+1)) K (growingQueryTime δ (K+1))

def growingCoefficientEvent (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (τ : ℝ) : Set (GrowingTranscript δ r K) :=
  {t | ‖growingCoefficients W β hβ δ r K t-growingS W β hβ δ K‖ ≤ τ}

def growingVarianceBudget (W : BrownianSystem Ω) (β : ℝ) (δ : ℝ≥0) (r K : ℕ) (τ : ℝ) : ℝ :=
  ((r+K:ℕ):ℝ)⁻¹ * (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ)/2)*(δ : ℝ) +
    5*τ^2+(actualParisiFullSusceptibilityExpected W β (growingQueryTime δ K))^2)

theorem measurable_growingCoefficients (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) : Measurable (growingCoefficients W β hβ δ r K) :=
  (WithLp.measurable_toLp 2 _).comp
    (measurable_visibleSpinCoefficients r K _ _ _ _
      (measurable_scalarGrowingPaperInitialState _ _ _) (measurable_growingTarget W β hβ δ r K)
      (measurable_growingUpdate δ r K))

theorem measurable_growingResidual (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) : Measurable (growingResidual W β hβ δ r K) :=
  measurable_visibleResidualSpin r K _ _ _
    (measurable_scalarGrowingPaperInitialState _ _ _) (measurable_growingTarget W β hβ δ r K)
    (measurable_growingUpdate δ r K)

theorem measurableSet_growingCoefficientEvent (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (τ : ℝ) :
    MeasurableSet (growingCoefficientEvent W β hβ δ r K τ) :=
  measurableSet_le ((measurable_growingCoefficients W β hβ δ r K).sub measurable_const).norm
    measurable_const

theorem growingCoefficients_norm_le_one (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (hN : 0 < r+K) (t : GrowingTranscript δ r K) :
    ‖growingCoefficients W β hβ δ r K t‖ ≤ 1 := by
  have h := actualPaper_coefficient_budget r K (r+K:ℕ) (Nat.cast_pos.mpr hN)
    (M1.Target W β hβ δ r K) (M1.Update δ r K)
    (growingInitial δ r K t.2.1) (visibleSource (r+K) K t.2.2) (signSpin t.1)
    (signSpin_norm_sq t.1)
  have he : ‖growingCoefficients W β hβ δ r K t‖^2 =
      ∑ j, (visibleSpinCoefficients r K (r+K:ℕ) (M1.Target W β hβ δ r K)
        (M1.Update δ r K) (growingInitial δ r K) t j)^2 :=
    EuclideanSpace.real_norm_sq_eq _
  change (∑ j, (visibleSpinCoefficients r K (r+K:ℕ) (M1.Target W β hβ δ r K)
    (M1.Update δ r K) (growingInitial δ r K) t j)^2) ≤ 1 at h
  nlinarith [norm_nonneg (growingCoefficients W β hβ δ r K t)]

theorem growingResidual_norm_identity (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (hN : 0 < r+K) (t : GrowingTranscript δ r K) :
    ((r+K:ℕ):ℝ)⁻¹*dot (growingResidual W β hβ δ r K t) (growingResidual W β hβ δ r K t) =
      1-∑ j, (growingCoefficients W β hβ δ r K t j)^2 :=
  actualPaper_residual_norm_identity r K _ (Nat.cast_pos.mpr hN)
    (M1.Target W β hβ δ r K) (M1.Update δ r K) _ _ _ (signSpin_norm_sq t.1)

theorem growingSourceCompact_product (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) :
    MeasurePreserving (growingSourceCompact δ r K) (M1.SourceLinkedLaw W β hβ δ r K)
      ((growingTranscriptLaw W β hβ δ r K).prod (completionNoiseLaw (r+K) K)) :=
  ⟨measurable_growingSourceCompact δ r K, growingSourceCompact_law W β hβ δ r K⟩

theorem growingSource_unused_terms_gaussian (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (hN : 0 < r+K) (t : GrowingTranscript δ r K) :
    let c := growingCoefficients W β hβ δ r K t
    let y := growingResidual W β hβ δ r K t
    IndepFun (fun z => discardedDiagonalEnergy (2*skSigma (r+K:ℕ)) (fun j => c j) z.1)
      (fun z => quadraticEnergy (r+K:ℕ) y (goeMatrix (skSigma (r+K:ℕ)) z.2))
      (completionNoiseLaw (r+K) K) ∧
    HasLaw (fun z => discardedDiagonalEnergy (2*skSigma (r+K:ℕ)) (fun j => c j) z.1)
      (gaussianReal 0 (((1/2:ℝ)*((r+K:ℕ):ℝ)⁻¹*∑ j, (c j)^4).toNNReal))
      (completionNoiseLaw (r+K) K) ∧
    HasLaw (fun z => quadraticEnergy (r+K:ℕ) y (goeMatrix (skSigma (r+K:ℕ)) z.2))
      (gaussianReal 0 (((1/2:ℝ)*((r+K:ℕ):ℝ)⁻¹*(1-∑ j, (c j)^2)^2).toNNReal))
      (completionNoiseLaw (r+K) K) :=
  unused_terms_gaussian _ (Nat.cast_pos.mpr hN) _ _
    (growingResidual_norm_identity W β hβ δ r K hN t)

theorem growingSource_completionVariance_sharp_le
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r K : ℕ) (hN : 0 < r+K) (τ : ℝ) (hτ : 0 ≤ τ)
    (hpost : parisiEquilibriumPhysicalEndpoint β ≤ growingQueryTime δ K)
    (t : GrowingTranscript δ r K) (ht : t ∈ growingCoefficientEvent W β hβ δ r K τ) :
    completionVariance (r+K:ℕ) (fun j => growingCoefficients W β hβ δ r K t j)
      (growingResidual W β hβ δ r K t) ≤ growingVarianceBudget W β δ r K τ := by
  apply completionVariance_sharp_le (r+K:ℕ) (Nat.cast_pos.mpr hN)
    (growingCoefficients W β hβ δ r K t) (growingS W β hβ δ K) _
    (Real.exp ((parisiEquilibriumPhysicalEndpoint β : ℝ)/2)*(δ : ℝ)) τ
    (actualParisiFullSusceptibilityExpected W β (growingQueryTime δ K))
    (by positivity) hτ (actualParisiFullSusceptibilityExpected_nonneg _ _ _)
    (growingCoefficients_norm_le_one W β hβ δ r K hN t) ht
  · exact populationTargetSpin_growing_coordinate_sq_le W W β hβ δ hδ _ K _
      ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ K))
  · exact populationTargetSpin_norm_sq_eq_defect W W β hβ _
      (growingQueryTime_strictMono δ hδ) rfl _ K _
      ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ K)) hpost
  · exact growingResidual_norm_identity W β hβ δ r K hN t

theorem growingSourceDiscardedEnergy_tail_on
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ)
    (r K : ℕ) (hN : 0 < r+K) (τ : ℝ) (hτ : 0 ≤ τ)
    (hpost : parisiEquilibriumPhysicalEndpoint β ≤ growingQueryTime δ K)
    (u : ℝ) (hu : 0 < u) :
    (M1.SourceLinkedLaw W β hβ δ r K).real {z |
      (growingSourceCompact δ r K z).1 ∈ growingCoefficientEvent W β hβ δ r K τ ∧
      u ≤ |growingSourceDiscardedEnergy W β hβ δ r K z|} ≤
      2*Real.exp (-u^2/(2*growingVarianceBudget W β δ r K τ)) := by
  let c := fun t : GrowingTranscript δ r K => fun j => growingCoefficients W β hβ δ r K t j
  let y := growingResidual W β hβ δ r K
  have hc : Measurable c := (WithLp.measurable_ofLp 2 _).comp
    (measurable_growingCoefficients W β hβ δ r K)
  have hy := measurable_growingResidual W β hβ δ r K
  have hE := measurableSet_growingCoefficientEvent W β hβ δ r K τ
  have hm := (hE.preimage measurable_fst).inter (measurableSet_le (measurable_const (a := u))
    (measurable_completionEnergy (r+K:ℕ) c y hc hy).abs)
  have he := (growingSourceCompact_product W β hβ δ r K).hasLaw.measureReal_eq hm
  have hpoint (z) : completionEnergy (r+K:ℕ) (c (growingSourceCompact δ r K z).1)
      (y (growingSourceCompact δ r K z).1) (growingSourceCompact δ r K z).2 =
        growingSourceDiscardedEnergy W β hβ δ r K z :=
    (growingSourceDiscardedEnergy_eq_completion W β hβ δ r K hN z).symm
  change (M1.SourceLinkedLaw W β hβ δ r K).real {z |
    (growingSourceCompact δ r K z).1 ∈ growingCoefficientEvent W β hβ δ r K τ ∧
    u ≤ |completionEnergy (r+K:ℕ) (c (growingSourceCompact δ r K z).1)
      (y (growingSourceCompact δ r K z).1) (growingSourceCompact δ r K z).2|} = _ at he
  simp_rw [hpoint] at he
  rw [he]
  exact completionEnergy_product_tail_on (growingTranscriptLaw W β hβ δ r K)
    (r+K:ℕ) (Nat.cast_pos.mpr hN) c y hc hy _ hE _ u
    (by unfold growingVarianceBudget; positivity) hu
    (growingSource_completionVariance_sharp_le W β hβ δ hδ r K hN τ hτ hpost)

theorem growingSourceDiscardedEnergy_mgf_on
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0)
    (r K : ℕ) (hN : 0 < r+K) (E : Set (GrowingTranscript δ r K))
    (hE : MeasurableSet E) (θ : ℝ) :
    (∫⁻ z in {z | (growingSourceCompact δ r K z).1 ∈ E},
      ENNReal.ofReal (Real.exp (θ*growingSourceDiscardedEnergy W β hβ δ r K z))
      ∂M1.SourceLinkedLaw W β hβ δ r K) =
    ∫⁻ z in {z | (growingSourceCompact δ r K z).1 ∈ E},
      ENNReal.ofReal (Real.exp (θ^2*completionVariance (r+K:ℕ)
        (fun j => growingCoefficients W β hβ δ r K (growingSourceCompact δ r K z).1 j)
        (growingResidual W β hβ δ r K (growingSourceCompact δ r K z).1)/2))
      ∂M1.SourceLinkedLaw W β hβ δ r K := by
  let μ := growingTranscriptLaw W β hβ δ r K
  let c := fun t : GrowingTranscript δ r K => fun j => growingCoefficients W β hβ δ r K t j
  let y := growingResidual W β hβ δ r K
  let F := fun z : GrowingTranscript δ r K ×
      (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ ((Fin (r+K) × Fin (r+K)))) =>
    ENNReal.ofReal (Real.exp (θ*completionEnergy (r+K:ℕ) (c z.1) (y z.1) z.2))
  let G := fun z : GrowingTranscript δ r K ×
      (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ ((Fin (r+K) × Fin (r+K)))) =>
    ENNReal.ofReal (Real.exp (θ^2*completionVariance (r+K:ℕ) (c z.1) (y z.1)/2))
  have hc : Measurable c := (WithLp.measurable_ofLp 2 _).comp
    (measurable_growingCoefficients W β hβ δ r K)
  have hy := measurable_growingResidual W β hβ δ r K
  have hF : Measurable F :=
    (((measurable_completionEnergy (r+K:ℕ) c y hc hy).const_mul θ).exp).ennreal_ofReal
  have hv : Measurable (fun t => completionVariance (r+K:ℕ) (c t) (y t)) := by
    unfold completionVariance dot
    fun_prop
  have hG : Measurable G :=
    (((hv.comp measurable_fst).const_mul (θ^2)).div_const 2).exp.ennreal_ofReal
  have hset : MeasurableSet (E ×ˢ (Set.univ : Set
      (EuclideanSpace ℝ (Fin K) × EuclideanSpace ℝ ((Fin (r+K) × Fin (r+K)))))) :=
    hE.prod MeasurableSet.univ
  have hmp := growingSourceCompact_product W β hβ δ r K
  have hleft := hmp.setLIntegral_comp_preimage hset hF
  have hright := hmp.setLIntegral_comp_preimage hset hG
  have hprod : (∫⁻ z in E ×ˢ Set.univ, F z ∂μ.prod (completionNoiseLaw (r+K) K)) =
      ∫⁻ z in E ×ˢ Set.univ, G z ∂μ.prod (completionNoiseLaw (r+K) K) := by
    rw [completionEnergy_product_mgf_on μ (r+K:ℕ) (Nat.cast_pos.mpr hN) c y hc hy E θ]
    rw [← Measure.restrict_prod_eq_prod_univ, lintegral_prod _ hG.aemeasurable]
    simp only [G, lintegral_const, measure_univ, mul_one]
  have hpoint (z) : F (growingSourceCompact δ r K z) =
      ENNReal.ofReal (Real.exp (θ*growingSourceDiscardedEnergy W β hβ δ r K z)) := by
    exact congrArg (fun a : ℝ => ENNReal.ofReal (Real.exp (θ*a)))
      (growingSourceDiscardedEnergy_eq_completion W β hβ δ r K hN z).symm
  have he := hleft.trans (hprod.trans hright.symm)
  simpa only [Set.preimage, Set.mem_prod, Set.mem_univ, and_true, hpoint, G] using he

end SKConstants.Completion.N13d
