module

public import SKConstants.Completion.LC0.PathConcatenation
public import SKConstants.GaussianProposalActualParisiCallbacks
public import SKConstants.FineInformationQuery
public import SKConstants.Upstream.OAI.Probability.SKBarriers.SpinGlass.LogPartition
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SKConstants.Completion.LFine
open SKConstantsOAI.ZeroTemperatureSK M1 FineInformation
variable {Ω : Type*} [MeasurableSpace Ω]

abbrev FreshRowSeed (h f : ℝ≥0) :=
  ScalarContinuousPath h ×
    (ScalarContinuousPath f × (ScalarContinuousPath (h+f) × ℝ))

def freshRowSeedLaw (W : BrownianSystem Ω) (h f : ℝ≥0) : Measure (FreshRowSeed h f) :=
  (scalarPrimitiveBridgePathLaw W h).prod
    ((scalarPrimitiveBrownianPathLaw W f).prod
      ((scalarPrimitiveBrownianPathLaw W (h+f)).prod SKConstantsOAI.SK.unitIntervalLaw))

instance freshRowSeedLaw_probability (W : BrownianSystem Ω) (h f : ℝ≥0) :
    IsProbabilityMeasure (freshRowSeedLaw W h f) := by
  unfold freshRowSeedLaw
  infer_instance

def freshRowDrivers (a h f : ℝ≥0) (Bpast Dpast : ScalarContinuousPath a)
    (z : ℝ × FreshRowSeed h f) :
    ScalarContinuousPath (a+(h+f)) × ScalarContinuousPath (a+(h+f)) :=
  (scalarConcatPath a (h+f) (Bpast,
      scalarConcatPath h f (scalarQueryBridgeComplete h (z.1,z.2.1),z.2.2.1)),
    scalarConcatPath a (h+f) (Dpast,z.2.2.2.1))

theorem measurable_freshRowDrivers (a h f : ℝ≥0) (Bpast Dpast : ScalarContinuousPath a) :
    Measurable (freshRowDrivers a h f Bpast Dpast) := by
  apply Measurable.prodMk
  · apply (measurable_scalarConcatPath a (h+f)).comp
    apply Measurable.prodMk measurable_const
    apply (measurable_scalarConcatPath h f).comp
    exact ((measurable_scalarQueryBridgeComplete h).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
        (measurable_fst.comp (measurable_snd.comp measurable_snd))
  · exact (measurable_scalarConcatPath a (h+f)).comp
      (measurable_const.prodMk
        (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))

def freshRowTerminalField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (Bpast Dpast : ScalarContinuousPath a)
    (z : ℝ × FreshRowSeed h f) : ℝ :=
  scalarTwoDriverPicardPath (actualParisiFullScalarDrift β)
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ) (a+(h+f))
    (0,freshRowDrivers a h f Bpast Dpast z)
      ⟨a+(h+f),(a+(h+f)).coe_nonneg,le_rfl⟩

theorem measurable_freshRowTerminalField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (Bpast Dpast : ScalarContinuousPath a) :
    Measurable (freshRowTerminalField W β hβ a h f Bpast Dpast) := by
  apply (ContinuousMap.measurable_eval _).comp
  exact (measurable_scalarTwoDriverPicardPath _ _ _ _ _ _).comp
    (measurable_const.prodMk (measurable_freshRowDrivers a h f Bpast Dpast))

def freshRowSign (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (Bpast Dpast : ScalarContinuousPath a)
    (z : ℝ × FreshRowSeed h f) : Bool :=
  if z.2.2.2.2 ≤ (1 + actualParisiFullMagnetization β (a+(h+f))
    (freshRowTerminalField W β hβ a h f Bpast Dpast z)) / 2 then true else false

theorem measurable_freshRowSign (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (Bpast Dpast : ScalarContinuousPath a) :
    Measurable (freshRowSign W β hβ a h f Bpast Dpast) := by
  have hm₀ : Measurable (fun y : ℝ => actualParisiFullMagnetization β (a+(h+f)) y) :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hm : Measurable (fun z : ℝ × FreshRowSeed h f =>
      actualParisiFullMagnetization β (a+(h+f))
        (freshRowTerminalField W β hβ a h f Bpast Dpast z)) :=
    hm₀.comp (measurable_freshRowTerminalField W β hβ a h f Bpast Dpast)
  unfold freshRowSign
  exact Measurable.ite (measurableSet_le (by fun_prop)
    ((measurable_const.add hm).div_const 2)) measurable_const measurable_const

def freshRowsLaw (W : BrownianSystem Ω) (h f : ℝ≥0) (n : ℕ) :
    Measure (Fin n → ℝ × FreshRowSeed h f) :=
  gaussianSeedLaw (fun _ : Fin n => freshRowSeedLaw W h f)

instance freshRowsLaw_probability (W : BrownianSystem Ω) (h f : ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (freshRowsLaw W h f n) := by
  unfold freshRowsLaw
  infer_instance

theorem freshRows_oneQuery_expectation (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (a h f : ℝ≥0) (n : ℕ) (Bpast Dpast : Fin n → ScalarContinuousPath a)
    (N : ℝ) (u : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hkilled : ∀ i, ∑ j, P j i *
      meanSpin (freshRowsLaw W h f n)
        (gaussianSignRows (fun j => freshRowSign W β hβ a h f (Bpast j) (Dpast j))) j = 0) :
    let row := gaussianSignRows (fun j => freshRowSign W β hβ a h f (Bpast j) (Dpast j))
    (∫ z, oneQueryEnergy row N u P z ∂freshRowsLaw W h f n) =
      (N⁻¹ * ∑ i, u i * meanSpin (freshRowsLaw W h f n) row i) *
        (N⁻¹ * ∑ j, P j j * mixedMean (freshRowsLaw W h f n) row j) -
      2 * (N⁻¹)^2 * ∑ i, u i * P i i *
        meanSpin (freshRowsLaw W h f n) row i * mixedMean (freshRowsLaw W h f n) row i := by
  exact gaussianSign_oneQuery_expectation (fun _ => freshRowSeedLaw W h f)
    (fun j => freshRowSign W β hβ a h f (Bpast j) (Dpast j))
    (fun j => measurable_freshRowSign W β hβ a h f (Bpast j) (Dpast j)) N u P hkilled

end SKConstants.Completion.LFine
