module

public import SKConstants.Completion.LM1a.LinkedHistoryLaw
public import SKConstants.Completion.LFine.SpinMarginal
public import SKConstants.Completion.LC0.PrimitivePathVersions
public import SKConstants.ParisiFullSpinRowMoments

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.NReplay
open SKConstantsOAI.ZeroTemperatureSK M1

variable {Ω : Type*} [MeasurableSpace Ω]

theorem weightedPath_law (W : BrownianSystem Ω)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (H : ℝ≥0)
    (hunit : ∀ t ∈ Icc (0 : ℝ) (H : ℝ), (f t)^2 + (g t)^2 = 1) :
    ((scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw W H)).map
      (scalarTwoDriverWeightedPath f g hf hg H) = scalarPrimitiveBrownianPathLaw W H := by
  have h := congrArg (fun ν => ν.map Prod.fst)
    (weightedPair_preserves_brownian_law W W f g hf hg H hunit)
  rw [Measure.map_map measurable_fst (measurable_WeightedPair f g hf hg H),
    Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

theorem primitivePosterior_mean_zero (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (H : ℝ≥0) :
    (∫ p, actualParisiFullMagnetization β H
      (scalarForwardPicardPath (actualParisiFullScalarDrift β) H (0,p)
        ⟨H, H.coe_nonneg, le_rfl⟩) ∂scalarPrimitiveBrownianPathLaw W H) = 0 := by
  let F : ScalarContinuousPath H → ℝ := fun p => actualParisiFullMagnetization β H
    (scalarForwardPicardPath (actualParisiFullScalarDrift β) H (0,p)
      ⟨H, H.coe_nonneg, le_rfl⟩)
  have hF : Measurable F :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable.comp
        ((ContinuousMap.measurable_eval _).comp
          ((measurable_scalarForwardPicardPath _ _).comp
            (measurable_const.prodMk measurable_id)))
  change (∫ p, F p ∂scalarPrimitiveBrownianPathLaw W H) = 0
  rw [scalarPrimitiveBrownianPathLaw,
    integral_map (measurable_scalarPrimitiveBrownianPathVersion W H).aemeasurable
      hF.aestronglyMeasurable]
  calc
    _ = ∫ w, actualParisiMagnetizationObservable W β H w ∂W.law := by
      apply integral_congr_ae
      filter_upwards [scalarForwardPicardPath_primitive_version W (actualParisiFullScalarDrift β) H]
        with w hw
      exact congrArg (actualParisiFullMagnetization β H) (hw ⟨H, H.coe_nonneg, le_rfl⟩)
    _ = 0 := actualParisiMagnetizationObservable_mean_zero W β hβ H

theorem twoDriverPosterior_mean_zero (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (H : ℝ≥0) :
    (∫ p, actualParisiFullMagnetization β H
      (scalarTwoDriverPicardPath (actualParisiFullScalarDrift β)
        (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
        (continuous_actualParisiNegativeRhoStieltjes W β hβ)
        (continuous_actualParisiSigmaStieltjes W β hβ) H (0,p)
          ⟨H, H.coe_nonneg, le_rfl⟩)
      ∂(scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw W H)) = 0 := by
  let F : ScalarContinuousPath H → ℝ := fun p => actualParisiFullMagnetization β H
    (scalarForwardPicardPath (actualParisiFullScalarDrift β) H (0,p)
      ⟨H, H.coe_nonneg, le_rfl⟩)
  have hF : Measurable F :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable.comp
        ((ContinuousMap.measurable_eval _).comp
          ((measurable_scalarForwardPicardPath _ _).comp
            (measurable_const.prodMk measurable_id)))
  have hlaw : HasLaw
      (scalarTwoDriverWeightedPath (actualParisiNegativeRhoStieltjes W β hβ)
        (actualParisiSigmaStieltjes W β hβ)
        (continuous_actualParisiNegativeRhoStieltjes W β hβ)
        (continuous_actualParisiSigmaStieltjes W β hβ) H)
      (scalarPrimitiveBrownianPathLaw W H)
      ((scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw W H)) :=
    ⟨(measurable_scalarTwoDriverWeightedPath _ _ _ _ _).aemeasurable,
      weightedPath_law W _ _ _ _ H (fun t _ => actualParisiStieltjesCoefficients_unit W β hβ t)⟩
  exact (hlaw.integral_comp hF.aestronglyMeasurable).trans
    (primitivePosterior_mean_zero W β hβ H)

theorem canonicalLinkedDrivers_spin_marginal (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (n q : ℕ) :
    (CanonicalLinkedDriversLaw W β hβ δ n q).map Prod.fst = uniformSpinLaw n := by
  let H := Horizon δ q
  let X : ScalarContinuousPath H × ScalarContinuousPath H → ℝ := fun p =>
    actualParisiFullMagnetization β H
      (scalarTwoDriverPicardPath (actualParisiFullScalarDrift β)
        (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
        (continuous_actualParisiNegativeRhoStieltjes W β hβ)
        (continuous_actualParisiSigmaStieltjes W β hβ) H (0,p)
          ⟨H, H.coe_nonneg, le_rfl⟩)
  have hX : Measurable X :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable.comp
        ((ContinuousMap.measurable_eval _).comp
          ((measurable_scalarTwoDriverPicardPath _ _ _ _ _ _).comp
            (measurable_const.prodMk measurable_id)))
  have hind : iIndepFun (fun i (b : DriverRows δ n q) => X (b i))
      (driverRowsLaw W δ n q) := iIndepFun_pi (fun _ => hX.aemeasurable)
  have hmean (i : Fin n) : (∫ b, X (b i) ∂driverRowsLaw W δ n q) = 0 := by
    exact ((measurePreserving_eval (fun _ : Fin n =>
      (scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw W H)) i).hasLaw.integral_comp
        hX.aestronglyMeasurable).trans (twoDriverPosterior_mean_zero W β hβ H)
  rw [← Completion.LFine.spinPrior_eq_uniformSpinLaw]
  exact Completion.LFine.terminalLinkedLaw_spin_marginal_of_rows
    (driverRowsLaw W δ n q) n β H (DriverTerminalField W β hβ δ n q)
      (measurable_DriverTerminalField W β hβ δ n q) hind hmean

theorem replayLinkedLaw_spin_marginal (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ)
    (hN : 0 < Size r₀ q) :
    (ReplayLinkedLaw W β hβ δ r₀ q).map Prod.fst = uniformSpinLaw (Size r₀ q) := by
  have h := congrArg (fun ν => ν.map Prod.fst)
    (literal_linked_replay_drivers_law W β hβ δ hδ r₀ q hN)
  rw [Measure.map_map measurable_fst
    (measurable_id.prodMap (measurable_ReplayDrivers W β hβ δ r₀ q))] at h
  exact h.trans (canonicalLinkedDrivers_spin_marginal W β hβ δ (Size r₀ q) q)

end SKConstants.NReplay
