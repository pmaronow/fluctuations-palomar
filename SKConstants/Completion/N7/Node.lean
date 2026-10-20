module

public import SKConstants.Completion.N7.ProposalBridge

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.N7
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint LC4a LM3

def ReplayDHistoryLawStatement : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0), 0 < δ → ∀ r₀ q : ℕ, 0 < r₀ →
      CanonicalObservationDHistoryStatement W β hβ δ r₀ q
        (scalarGrowingSourceHorizon δ q) le_rfl

theorem forwardKL_holds (hInput : ReplayInputLawStatement) (hThreshold : ThresholdLinkStatement)
    (hHistory : ReplayDHistoryLawStatement) : ForwardKLStatement := by
  intro Ω _ W β hβ δ hδ r₀ q hr₀ n h
  subst n
  have hn : 0 < r₀ + q := lt_of_lt_of_le hr₀ (Nat.le_add_right r₀ q)
  let V := scalarGrowingSourceHorizon δ q
  let Q := replayProposalGen W β hβ δ r₀ q rfl
  let R := growingReplayLinkedLaw W β hβ δ r₀ q V
  have hOutput : Q.map (fun p => (physical (r₀ + q) p.2, p.1)) =
      R.map (replayOutput δ r₀ q) :=
    (replayProposalGen_physical_eq_linkedReplay hInput hThreshold W β hβ δ r₀ q).trans
      (actualReplay_output_eq_pathReplay W β hβ δ r₀ q).symm
  have hKL := actualReplay_forward_KL_of_historyLaw W β hβ δ hδ r₀ q hn V le_rfl
    (hHistory W β hβ δ hδ r₀ q hr₀)
  have hLift := replayProposalGen_KL_le_physical W β hβ δ r₀ q hn
  rw [← replayProposalGen_physical_output W β hβ δ r₀ q, hOutput] at hLift
  have hPressure : (∫ G, Real.log (gibbsPartition β G) ∂skDisorderLaw (r₀ + q)) =
      ∫ g, primitiveGOEPressure (r₀ + q) β g ∂primLaw (r₀ + q) := by
    unfold skDisorderLaw
    rw [integral_map (continuous_goeMatrix _).measurable.aemeasurable
      ((continuous_gibbsPartition β).measurable.log).aestronglyMeasurable]
    rfl
  have hH : Measurable (fun p : Matrix (Fin (r₀ + q)) (Fin (r₀ + q)) ℝ × Spin (r₀ + q) =>
      quadraticHamiltonian p.1 p.2) :=
    LF0.measurable_coupled_energy Prod.fst Prod.snd measurable_fst measurable_snd
  have hG : Measurable (fun p : Spin (r₀ + q) × Prim (r₀ + q) =>
      (physical (r₀ + q) p.2, p.1)) :=
    ((continuous_goeMatrix _).measurable.comp measurable_snd).prodMk measurable_fst
  have hEnergy : (∫ u, quadraticHamiltonian (replayOutput δ r₀ q u).1
      (replayOutput δ r₀ q u).2 ∂ R) =
      ∫ y, goeSpinHamiltonian (1 / Real.sqrt (2 * (r₀ + q : ℕ))) y.1 y.2 ∂ Q := by
    have hRaw := integral_map (μ := R) (measurable_replayOutput δ r₀ q).aemeasurable
      hH.aestronglyMeasurable
    have hPrim := integral_map (μ := Q) hG.aemeasurable hH.aestronglyMeasurable
    rw [hOutput] at hPrim
    exact hRaw.symm.trans hPrim
  rw [hPressure, hEnergy] at hKL
  exact hLift.trans hKL

end SKConstants.Completion.N7
