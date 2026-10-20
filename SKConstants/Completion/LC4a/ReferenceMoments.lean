module
public import SKConstants.Completion.LC4a.ReplayInformation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.LC4a
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

theorem growingReplayDExponential_memLp_two
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I) :
    MemLp (growingReplayDExponential W β hβ δ hδ ranks q V I) 2
      (growingReplayUnlinkedLaw W δ ranks q) := by
  let := W.isProbability
  let P := parisiGrowingReplaySpinStaticLaw W δ (ranks + q) q
  let H := actualParisiGrowingReplayDCoefficient W β hβ δ hδ ranks q
  let G := brownianDyadicGrid V
  let B : ℝ := (ranks + q : ℕ) * (2 : ℝ)^2 * (V : ℝ)
  let X : ℕ → GrowingReplaySpace Ω δ ranks q → ℝ := fun l =>
    brownianVectorFullPastExponential W.B (G.time l)
      (brownianVectorContinuousMeshCoefficient H (G.time l)) 1 (1 * 2^l)
  have hm (l : ℕ) : Measurable (X l) :=
    measurable_brownianVectorFullPastExponential W.B W.measurable (G.time l) (G.monotone l)
      _ (fun k => measurable_replayDCoefficient W β hβ δ hδ ranks q _) 1 _
  have hv := brownianVectorContinuousVariation_tendsto_L2 P W.law W.B
    W.brownian.toIsPreBrownianReal W.measurable H
    (measurable_replayDCoefficient W β hβ δ hδ ranks q) 2
    (replayDCoefficient_bound W β hβ δ hδ ranks q)
    (replayDCoefficient_continuous_ae W β hβ δ hδ ranks q) G 1
    (brownianDyadicWidth V) (brownianDyadicWidth_tendsto V)
    (fun l i _ => brownianDyadicGrid_width_le V l i)
  have hsm (l : ℕ) := (memLp_growingReplayDLeftSum W β hβ δ hδ ranks q V l).aestronglyMeasurable
  have hvm (l : ℕ) : AEStronglyMeasurable
      (brownianVectorPredictableVariation W.B (G.time l)
        (brownianVectorContinuousMeshCoefficient H (G.time l)) (1 * 2^l))
      (growingReplayUnlinkedLaw W δ ranks q) :=
    (aemeasurable_predictableGaussianVectorVariation _ _ _
      (fun i => (measurable_brownianVectorStaticCoefficient W.B W.measurable _ _
        (fun k => measurable_replayDCoefficient W β hβ δ hδ ranks q _) i).aemeasurable)
      _).aestronglyMeasurable
  have ht := tendstoInMeasure_continuous_two_real hsm hvm
    (tendstoInMeasure_of_tendsto_integral_sq hI.2.1 hI.2.2)
    (tendstoInMeasure_of_tendsto_integral_sq hv.2.1 hv.2.2)
    (fun p : ℝ × ℝ => Real.exp (p.1 - p.2 / 2)) (by fun_prop)
  have hlim : TendstoInMeasure (growingReplayUnlinkedLaw W δ ranks q) X atTop
      (growingReplayDExponential W β hβ δ hδ ranks q V I) := by
    convert ht using 1
    · funext l u
      simp only [X, brownianVectorFullPastExponential, one_mul, one_pow,
        growingReplayDLeftSum, brownianVectorContinuousLeftSum, H, G]
    · simp only [G, brownianDyadicGrid_horizon]
      rfl
  have hcap (l : ℕ) : eLpNorm (X l) 2 (growingReplayUnlinkedLaw W δ ranks q) ≤
      ENNReal.ofReal (Real.exp B) ^ (1 / (2 : ℝ)) := by
    apply eLpNorm_brownianVectorFullPastExponential_two_le P W.law W.B
      W.brownian.toIsPreBrownianReal W.measurable _ (G.monotone l) _
      (fun k => measurable_replayDCoefficient W β hβ δ hδ ranks q _) _ B
    intro u
    change brownianVectorPredictableVariation W.B (G.time l)
      (brownianVectorContinuousMeshCoefficient H (G.time l)) (1 * 2^l) u ≤ B
    have hb := brownianVectorContinuousVariation_le W.B H 2
      (replayDCoefficient_bound W β hβ δ hδ ranks q) G 1 l u
    simpa only [G, B, brownianDyadicGrid_horizon, Fintype.card_fin] using hb
  exact (eLpNorm_le_of_tendstoInMeasure (Eventually.of_forall hcap) hlim
    (fun l => (hm l).aestronglyMeasurable)).trans_lt
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)

theorem growingReplayDIntegral_integrable_reference
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (V : ℝ≥0)
    (I : GrowingReplaySpace Ω δ ranks q → ℝ)
    (hI : IsGrowingReplayDIntegral W β hβ δ hδ ranks q V I) :
    Integrable I (growingReplayDReference W β hβ δ hδ ranks q V I) := by
  apply (integrable_withDensity_iff_integrable_smul₀'
    (aemeasurable_growingReplayDExponential W β hβ δ hδ ranks q V I hI.1).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).2
  have h := (growingReplayDExponential_memLp_two W β hβ δ hδ ranks q V I hI).integrable_mul hI.1
  simp only [ENNReal.toReal_ofReal (growingReplayDExponential_pos W β hβ δ hδ ranks q V I _).le,
    smul_eq_mul]
  exact h

end SKConstants.Completion.LC4a
