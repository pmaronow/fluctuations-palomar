module

public import SKConstants.GaussianProposalScalarPrefixReplay
public import SKConstants.ParisiFullVarianceIntegral
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal BigOperators
namespace SKConstants
open GaussianProposal
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

def actualParisiGrowingSourceTarget (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (ranks q : ℕ) :=
  scalarGrowingPaperTarget (actualParisiFullScalarDrift β)
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ)
    (actualParisiFullMagnetization β) (actualParisiFullSusceptibilitySquareExpected W β)
    (scalarGrowingSourceHorizon δ q) δ (ranks+q) q

def actualParisiGrowingReplayField (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (ranks q : ℕ) :=
  scalarGrowingReplayField (actualParisiFullScalarDrift β)
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ)
    (actualParisiFullMagnetization β) (actualParisiFullSusceptibilitySquareExpected W β) δ ranks q

def actualParisiGrowingReplayPastCallback (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) :=
  scalarGrowingReplayPastCallback (actualParisiFullScalarDrift β)
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ)
    (actualParisiFullMagnetization β) (continuous_actualParisiFullMagnetization β).measurable
    (actualParisiFullSusceptibilitySquareExpected W β) δ hδ ranks q

lemma measurable_actualParisiGrowingReplayPastCallback (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) (t : ℝ≥0) :
    Measurable (actualParisiGrowingReplayPastCallback W β hβ δ hδ ranks q t) :=
  measurable_scalarGrowingReplayPastCallback _ _ _ _ _ _ _ _ _ _ _ _ _

lemma continuous_actualParisiGrowingReplayField_time (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (ranks q : ℕ)
    (x : ScalarGrowingReplayStaticData δ (ranks+q) q ×
      (Fin (ranks+q) → ScalarContinuousPath (scalarGrowingSourceHorizon δ q))) :
    Continuous (fun t : ℝ≥0 => actualParisiGrowingReplayField W β hβ δ ranks q t x) :=
  continuous_scalarGrowingReplayField_time _ _ _ _ _ _ _ _ _ _ _

theorem actualParisiGrowingReplayPastCallback_brownian_ae (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ) :
    ∀ᵐ ω ∂Measure.pi (fun _ : Fin (ranks+q) => W.law),
      ∀ (a : ScalarGrowingReplayStaticData δ (ranks+q) q) (t : ℝ≥0),
        actualParisiGrowingReplayPastCallback W β hβ δ hδ ranks q t
          (a,fun u i => W.B u (ω i)) =
        actualParisiGrowingReplayField W β hβ δ ranks q t
          (a,fun i => scalarPrimitiveBrownianPathVersion W (scalarGrowingSourceHorizon δ q) (ω i)) :=
  scalarGrowingReplayPastCallback_brownian_ae W _ _ _ _ _ _ _ _ _ _ _ _

theorem actualParisiGrowingReplayPastCallback_continuous_brownian_ae (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (ranks q : ℕ)
    (P : Measure (ScalarGrowingReplayStaticData δ (ranks+q) q)) [SFinite P] :
    ∀ᵐ x ∂P.prod (Measure.pi (fun _ : Fin (ranks+q) => W.law)),
      Continuous (fun t : ℝ≥0 => actualParisiGrowingReplayPastCallback W β hβ δ hδ ranks q t
        (x.1,fun u i => W.B u (x.2 i))) :=
  scalarGrowingReplayPastCallback_continuous_brownian_ae W _ _ _ _ _ _ _ _ _ _ _ _ P

theorem actualParisiGrowingSourceReplayInput_joint_law (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (ranks q : ℕ) :
    ((scalarGrowingPaperInitialDataLaw W (scalarGrowingSourceHorizon δ q) δ (ranks+q)).prod
      (paperAugmentedNoiseLaw (ranks+q) q)).map (fun p =>
        ((p.1.2,scalarGrowingSourceAugmentedOutput (actualParisiFullScalarDrift β)
          (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
          (continuous_actualParisiNegativeRhoStieltjes W β hβ)
          (continuous_actualParisiSigmaStieltjes W β hβ)
          (actualParisiFullMagnetization β) (actualParisiFullSusceptibilitySquareExpected W β)
          δ ranks q p.1 p.2),p.1.1)) =
      (scalarGrowingReplayStaticLaw W δ (ranks+q) q).prod
        (Measure.pi (fun _ : Fin (ranks+q) =>
          scalarPrimitiveBrownianPathLaw W (scalarGrowingSourceHorizon δ q))) :=
  scalarGrowingSourceReplayInput_joint_law W _ _ _ _ _ _
    (continuous_actualParisiFullMagnetization β).measurable _ _ _ _

def actualParisiGrowingSourceAugmentedOutput (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (ranks q : ℕ) :=
  scalarGrowingSourceAugmentedOutput (actualParisiFullScalarDrift β)
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ)
    (actualParisiFullMagnetization β) (actualParisiFullSusceptibilitySquareExpected W β) δ ranks q

theorem actualParisiGrowingReplayField_eq_source (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (ranks q : ℕ) (hn : 0 < ranks+q)
    (p : ScalarGrowingPaperInitialData (scalarGrowingSourceHorizon δ q) δ (ranks+q))
    (z : PaperAugmentedNoise (ranks+q) q) (t : ℝ≥0) :
    actualParisiGrowingReplayField W β hβ δ ranks q t
      ((p.2,actualParisiGrowingSourceAugmentedOutput W β hβ δ ranks q p z),p.1) =
    fun i => scalarMeshPaperObservation (actualParisiFullScalarDrift β)
      (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
      (continuous_actualParisiNegativeRhoStieltjes W β hβ)
      (continuous_actualParisiSigmaStieltjes W β hβ) (scalarGrowingSourceHorizon δ q)
      (growingQueryDuration δ) (growingQueryTime δ) (ranks+q)
      (proposalTerminalPast (scalarGrowingPaperUpdate (scalarGrowingSourceHorizon δ q) δ (ranks+q) q) q
        (scalarGrowingPaperInitialState (scalarGrowingSourceHorizon δ q) δ (ranks+q) p)
        (paperAugmentedOriginal (ranks+q) q z)) i
      (projIcc 0 (scalarGrowingSourceHorizon δ q : ℝ) (scalarGrowingSourceHorizon δ q).coe_nonneg t) :=
  scalarGrowingReplayField_eq_source _ _ _ _ _ _ _ _ _ _ hn p z t

theorem actualParisiGrowingIncrementScale_eq_posterior
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (j : ℕ) (hj : 0 < j) :
    scalarMeshPaperIncrementScale (actualParisiFullSusceptibilitySquareExpected W β)
      (growingQueryTime δ) j =
    (actualParisiPosteriorIntervalScale W β (growingQueryTime δ (j-1)) (growingQueryTime δ j):ℝ) := by
  exact (actualParisiPosteriorIntervalScale_eq_sqrt_integral W β hβ _ _
    (growingQueryTime_strictMono δ hδ (by omega : j-1<j))).symm

lemma actualParisiGrowingIncrementScale_pos
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (j : ℕ) (hj : 0 < j) :
    0 < scalarMeshPaperIncrementScale (actualParisiFullSusceptibilitySquareExpected W β)
      (growingQueryTime δ) j := by
  rw [actualParisiGrowingIncrementScale_eq_posterior W β hβ δ hδ j hj]
  exact NNReal.coe_pos.mpr (actualParisiPosteriorIntervalScale_pos W β hβ _ _
    (growingQueryTime_strictMono δ hδ (by omega : j-1<j)))

end SKConstants
