module
public import SKConstants.Completion.LC4a.TerminalLinkLocal

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.LC4a
open SKConstantsOAI.ZeroTemperatureSK

variable {Ω : Type*} [MeasurableSpace Ω]

def growingReplayDLeftSum (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) (l : ℕ) :
    GrowingReplaySpace Ω δ ranks q → ℝ :=
  brownianVectorContinuousLeftSum W.B
    (actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q) (brownianDyadicGrid V) 1 l

def growingReplayDBracket (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) :
    GrowingReplaySpace Ω δ ranks q → ℝ :=
  brownianVectorContinuousQuadraticVariation W.B
    (actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q) V

def growingReplayDExponential (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ) : GrowingReplaySpace Ω δ ranks q → ℝ :=
  brownianVectorContinuousExponential W.B
    (actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q) V I

def growingReplayDReference (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ) : Measure (GrowingReplaySpace Ω δ ranks q) :=
  (growingReplayUnlinkedLaw W δ ranks q).withDensity
    (fun u => ENNReal.ofReal (growingReplayDExponential W β hβ δ hδ ranks q V I u))

def IsGrowingReplayDIntegral (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ) : Prop :=
  MemLp I 2 (growingReplayUnlinkedLaw W δ ranks q) ∧
    (∀ l, Integrable (fun u => (growingReplayDLeftSum W β hβ δ hδ ranks q V l u - I u)^2)
      (growingReplayUnlinkedLaw W δ ranks q)) ∧
    Tendsto (fun l => ∫ u, (growingReplayDLeftSum W β hβ δ hδ ranks q V l u - I u)^2
      ∂growingReplayUnlinkedLaw W δ ranks q) atTop (𝓝 0)

theorem growingReplayDIntegral_unique (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I J : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I)
    (hJ : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V J) :
    I =ᵐ[growingReplayUnlinkedLaw W δ ranks q] J :=
  tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_integral_sq hI.2.1 hI.2.2)
    (tendstoInMeasure_of_tendsto_integral_sq hJ.2.1 hJ.2.2)

theorem growingReplayDReference_unique (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I J : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I)
    (hJ : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V J) :
    growingReplayDReference W β hβ δ hδ ranks q V I =
      growingReplayDReference W β hβ δ hδ ranks q V J := by
  apply withDensity_congr_ae
  filter_upwards [growingReplayDIntegral_unique W β hβ δ hδ ranks q V I J hI hJ] with u hu
  simp only [growingReplayDExponential, brownianVectorContinuousExponential, hu]

lemma measurable_replayDCoefficient (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (s : ℝ≥0) :
    Measurable (actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q s) :=
  measurable_actualParisiVectorDCoefficient β Prod.snd measurable_snd _ _
    (measurable_actualParisiGrowingSpinReplayFieldPast W β hβ δ hδ ranks q) s

lemma replayDCoefficient_bound (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) :
    ∀ s u i, ‖actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q s u i‖ ≤ 2 := by
  apply actualParisiVectorDCoefficient_bound
  intro s
  rw [Real.norm_eq_abs, abs_of_nonneg (actualParisiQuerySigma_bounds W β hβ s).1]
  exact (actualParisiQuerySigma_bounds W β hβ s).2

lemma replayDCoefficient_continuous_ae (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (i : Fin (ranks + q)) :
    ∀ᵐ u ∂growingReplayUnlinkedLaw W δ ranks q,
      Continuous (fun s => brownianVectorContinuousCoefficient W.B
        (actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q) s u i) := by
  filter_upwards [actualParisiGrowingSpinReplayFieldPast_continuous_ae W β hβ δ hδ ranks q i]
    with u hu
  exact continuous_actualParisiVectorDCoefficient_path W.B β Prod.snd _
    ((continuous_actualParisiQuerySigma W β).comp NNReal.continuous_coe) _ u i hu

lemma memLp_growingReplayDLeftSum (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) (l : ℕ) :
    MemLp (growingReplayDLeftSum W β hβ δ hδ ranks q V l) 2
      (growingReplayUnlinkedLaw W δ ranks q) := by
  let := W.isProbability
  exact memLp_brownianVectorContinuousLeftSum _ _ W.B W.brownian.toIsPreBrownianReal W.measurable
    _ (measurable_replayDCoefficient W β hβ δ hδ ranks q) 2
    (replayDCoefficient_bound W β hβ δ hδ ranks q) (brownianDyadicGrid V) 1 l

lemma growingReplayDBracket_bounds (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (u : GrowingReplaySpace Ω δ ranks q) :
    0 ≤ growingReplayDBracket W β hβ δ hδ ranks q V u ∧
      growingReplayDBracket W β hβ δ hδ ranks q V u ≤ 4 * (ranks + q : ℕ) * (V : ℝ) := by
  have h := brownianVectorContinuousQuadraticVariation_bounds W.B
    (actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q) 2
    (replayDCoefficient_bound W β hβ δ hδ ranks q) V u
  refine ⟨h.1, h.2.trans_eq ?_⟩
  simp only [Fintype.card_fin]
  ring

lemma aestronglyMeasurable_growingReplayDBracket (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) :
    AEStronglyMeasurable (growingReplayDBracket W β hβ δ hδ ranks q V)
      (growingReplayUnlinkedLaw W δ ranks q) := by
  let := W.isProbability
  have h := (brownianVectorContinuousVariation_tendsto_L2
    (parisiGrowingReplaySpinStaticLaw W δ (ranks + q) q) W.law W.B
    W.brownian.toIsPreBrownianReal W.measurable _
    (measurable_replayDCoefficient W β hβ δ hδ ranks q) 2
    (replayDCoefficient_bound W β hβ δ hδ ranks q)
    (replayDCoefficient_continuous_ae W β hβ δ hδ ranks q)
    (brownianDyadicGrid V) 1 (brownianDyadicWidth V) (brownianDyadicWidth_tendsto V)
    (fun l i _ => brownianDyadicGrid_width_le V l i)).1
  simpa only [brownianDyadicGrid_horizon, growingReplayDBracket, growingReplayUnlinkedLaw] using h

theorem actualReplayGaussianReference_integral_exists
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0) :
    ∃ I : GrowingReplaySpace Ω δ ranks q → ℝ,
      IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I ∧
      Integrable (growingReplayDExponential W β hβ δ hδ ranks q V I)
        (growingReplayUnlinkedLaw W δ ranks q) ∧
      (∫ u, growingReplayDExponential W β hβ δ hδ ranks q V I u
        ∂growingReplayUnlinkedLaw W δ ranks q) = 1 ∧
      IsProbabilityMeasure (growingReplayDReference W β hβ δ hδ ranks q V I) ∧
      (growingReplayDReference W β hβ δ hδ ranks q V I).map Prod.fst =
        parisiGrowingReplaySpinStaticLaw W δ (ranks + q) q ∧
      (growingReplayDReference W β hβ δ hδ ranks q V I).map (fun u => (u.1.1.2.1, u.1.2)) =
        (skDisorderLaw (ranks + q)).prod
          (Measure.pi (fun _ : Fin (ranks + q) => scalarHiddenPriorBool 0)) := by
  let := W.isProbability
  obtain ⟨I, hI, hlim, hEi, hmean, hprob, hmarg⟩ := actualParisiVectorDReference_exists
    (parisiGrowingReplaySpinStaticLaw W δ (ranks + q) q) W.law W.B
    W.brownian.toIsPreBrownianReal W.measurable β Prod.snd measurable_snd
    (fun t : ℝ≥0 => actualParisiQuerySigma W β t)
    ((continuous_actualParisiQuerySigma W β).comp NNReal.continuous_coe)
    (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (actualParisiQuerySigma_bounds W β hβ t).1]
      exact (actualParisiQuerySigma_bounds W β hβ t).2)
    (actualParisiGrowingSpinReplayFieldPast W β hβ δ hδ ranks q)
    (measurable_actualParisiGrowingSpinReplayFieldPast W β hβ δ hδ ranks q)
    (actualParisiGrowingSpinReplayFieldPast_continuous_ae W β hβ δ hδ ranks q)
    (brownianDyadicGrid V) 1 (brownianDyadicWidth V) (brownianDyadicWidth_tendsto V)
    (fun l d i _ => brownianDyadicGrid_left_le V l d i)
    (fun l i _ => brownianDyadicGrid_width_le V l i)
  simp only [brownianDyadicGrid_horizon] at hEi hmean hprob hmarg
  refine ⟨I, ⟨hI, ?_, hlim⟩, hEi, hmean, hprob, hmarg, ?_⟩
  · intro l
    exact ((memLp_growingReplayDLeftSum W β hβ δ hδ ranks q V l).sub hI).integrable_sq
  · exact parisiGrowingReplay_density_matrix_spin_marginal W δ (ranks + q) q _ hmarg

theorem growingReplayDIntegral_reference_probability
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I) :
    IsProbabilityMeasure (growingReplayDReference W β hβ δ hδ ranks q V I) := by
  obtain ⟨J, hJ, _, _, hprob, _, _⟩ :=
    actualReplayGaussianReference_integral_exists W β hβ δ hδ ranks q V
  rw [growingReplayDReference_unique W β hβ δ hδ ranks q V I J hI hJ]
  exact hprob

end SKConstants.Completion.LC4a
