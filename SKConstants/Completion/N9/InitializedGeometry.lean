module

public import SKConstants.Completion.LFine.PosteriorGeometry
public import SKConstants.Completion.LC0.SourceReplay
public import SKConstants.Completion.LC0.BridgeReconstruction
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators Matrix

namespace SKConstants.Completion.N9
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport GaussianProposal LFine
variable {Ω : Type*} [MeasurableSpace Ω]

theorem actualParisiFullMagnetization_at_zero_field (β v : ℝ) :
    actualParisiFullMagnetization β v 0 = 0 := by
  apply SKConstantsOAI.SK.Analytic.scalarCDFGradient_zero β
    (fun z => ⟨cdf_nonneg _ z,cdf_le_one _ z⟩) (cdf (parisiEquilibriumMeasure β : Measure ℝ)).mono
  rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
  linarith [(cdfTimeClamp_mem (v/β^2)).1]

theorem scalarTwoDriverPicardPath_initial (b : BoundedLipschitzDrift)
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g)
    (H : ℝ≥0) (z : ℝ) (B D : ScalarContinuousPath H)
    (hB : B ⟨0,le_rfl,H.coe_nonneg⟩ = 0) (hD : D ⟨0,le_rfl,H.coe_nonneg⟩ = 0) :
    scalarTwoDriverPicardPath b f g hf hg H (z,(B,D)) ⟨0,le_rfl,H.coe_nonneg⟩ = z := by
  have he := scalarForwardPicardPath_integral_equation b H
    (z,scalarTwoDriverWeightedPath f g hf hg H (B,D)) ⟨0,le_rfl,H.coe_nonneg⟩
  simpa only [scalarTwoDriverPicardPath, scalarTwoDriverWeightedPath,
    ContinuousMap.add_apply, ContinuousMap.neg_apply, scalarStieltjesWeightedPath,
    ContinuousMap.coe_mk, intervalIntegral.integral_same, hB, hD, mul_zero,
    sub_zero, neg_zero, add_zero] using he

theorem actualGrowing_initialized_mean_zero (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (n q : ℕ)
    (p : ScalarGrowingPaperInitialData (scalarGrowingSourceHorizon δ q) δ n)
    (hD : ∀ i, p.1 i ⟨0,le_rfl,(scalarGrowingSourceHorizon δ q).coe_nonneg⟩ = 0)
    (hB : ∀ i, p.2.1 i ⟨0,le_rfl,(growingQueryDuration δ 0).coe_nonneg⟩ = 0) :
    actualGrowingMeanAt W β hβ δ n q 0
      (scalarGrowingPaperInitialState (scalarGrowingSourceHorizon δ q) δ n p) = 0 := by
  ext i
  unfold actualGrowingMeanAt scalarMeshMeanAt
  simp only [NNReal.coe_zero, Pi.zero_apply]
  rw [show (projIcc 0 (scalarGrowingSourceHorizon δ q : ℝ)
    (scalarGrowingSourceHorizon δ q).coe_nonneg (0 : ℝ)) =
      ⟨0,le_rfl,(scalarGrowingSourceHorizon δ q).coe_nonneg⟩ from
        projIcc_of_mem _ ⟨le_rfl,(scalarGrowingSourceHorizon δ q).coe_nonneg⟩]
  change actualParisiFullMagnetization β 0
    (scalarTwoDriverPicardPath _ _ _ _ _ _ (0,(_,_)) _) = 0
  rw [scalarTwoDriverPicardPath_initial]
  · exact actualParisiFullMagnetization_at_zero_field β 0
  · change scalarInitialAuxiliaryB (scalarGrowingSourceHorizon δ q)
      (growingQueryDuration δ 0) (p.2.1 i) _ = 0
    simpa only [scalarInitialAuxiliaryB, ContinuousMap.coe_mk, IccExtend,
      Function.comp_apply, projIcc_of_mem _ ⟨le_rfl,(growingQueryDuration δ 0).coe_nonneg⟩] using hB i
  · exact hD i

theorem actualGrowing_initialized_mean_zero_ae (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (n q : ℕ) :
    ∀ᵐ p ∂scalarGrowingPaperInitialDataLaw W (scalarGrowingSourceHorizon δ q) δ n,
      actualGrowingMeanAt W β hβ δ n q 0
        (scalarGrowingPaperInitialState (scalarGrowingSourceHorizon δ q) δ n p) = 0 := by
  let H := scalarGrowingSourceHorizon δ q
  let μD := Measure.pi (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W H)
  let μB := Measure.pi (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0))
  let μC := Measure.infinitePi (fun k : ℕ => Measure.pi
    (fun _ : Fin n => scalarPrimitiveBridgePathLaw W (growingQueryDuration δ k)))
  have hD : ∀ᵐ D ∂μD, ∀ i, D i ⟨0,le_rfl,H.coe_nonneg⟩ = 0 := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W H) i).quasiMeasurePreserving.ae
      (M1.scalarPrimitiveBrownianPathLaw_zero_ae W H)
  have hB : ∀ᵐ B ∂μB, ∀ i, B i ⟨0,le_rfl,(growingQueryDuration δ 0).coe_nonneg⟩ = 0 := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval
      (fun _ : Fin n => scalarPrimitiveBrownianPathLaw W (growingQueryDuration δ 0)) i).quasiMeasurePreserving.ae
      (M1.scalarPrimitiveBrownianPathLaw_zero_ae W (growingQueryDuration δ 0))
  have hDdata := (measurePreserving_fst (μ := μD) (ν := μB.prod μC)).quasiMeasurePreserving.ae hD
  have hBdata := ((measurePreserving_fst (μ := μB) (ν := μC)).comp
    (measurePreserving_snd (μ := μD) (ν := μB.prod μC))).quasiMeasurePreserving.ae hB
  change ∀ᵐ p ∂μD.prod (μB.prod μC), _
  filter_upwards [hDdata,hBdata] with p hpD hpB
  exact actualGrowing_initialized_mean_zero W β hβ δ n q p hpD hpB

theorem actualSource_projection_kills_posterior_ae (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) :
    ∀ᵐ u ∂M1.SourceLaw W δ r q, ∀ j : Fin (q+1),
      paperRemainingProjectionTrace r (r+q) (M1.Target W β hβ δ r q) (M1.Update δ r q) q
        (M1.Initial δ r q u,1) (M1.Original δ r q u) j *ᵥ
      actualGrowingMeanAt W β hβ δ (r+q) q (growingQueryTime δ j.val)
        (paperScalarPastTrace r (r+q) (M1.Target W β hβ δ r q) (M1.Update δ r q) q
          (M1.Initial δ r q u,1) (M1.Original δ r q u) j) = 0 := by
  have hz := (measurePreserving_fst
    (μ := scalarGrowingPaperInitialDataLaw W (scalarGrowingSourceHorizon δ q) δ (r+q))
    (ν := paperAugmentedNoiseLaw (r+q) q)).quasiMeasurePreserving.ae
      (actualGrowing_initialized_mean_zero_ae W β hβ δ (r+q) q)
  filter_upwards [hz] with u hu
  intro j
  exact actualGrowing_projection_kills_posterior W β hβ δ hδ r q (M1.Initial δ r q u) hu
    (M1.Original δ r q u) j

theorem actualLinkedSource_projection_kills_posterior_ae (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r q : ℕ) :
    ∀ᵐ u ∂M1.SourceLinkedLaw W β hβ δ r q, ∀ j : Fin (q+1),
      paperRemainingProjectionTrace r (r+q) (M1.Target W β hβ δ r q) (M1.Update δ r q) q
        (M1.Initial δ r q u.2,1) (M1.Original δ r q u.2) j *ᵥ
      actualGrowingMeanAt W β hβ δ (r+q) q (growingQueryTime δ j.val)
        (paperScalarPastTrace r (r+q) (M1.Target W β hβ δ r q) (M1.Update δ r q) q
          (M1.Initial δ r q u.2,1) (M1.Original δ r q u.2) j) = 0 := by
  have hpres : MeasurePreserving Prod.snd (M1.SourceLinkedLaw W β hβ δ r q)
      (M1.SourceLaw W δ r q) :=
    ⟨measurable_snd,M1.sourceLinkedLaw_base_marginal W β hβ δ r q⟩
  exact hpres.quasiMeasurePreserving.ae
    (actualSource_projection_kills_posterior_ae W β hβ δ hδ r q)

end SKConstants.Completion.N9
