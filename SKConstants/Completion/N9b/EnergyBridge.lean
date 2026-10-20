module

public import SKConstants.Completion.N9.Node
public import SKConstants.Completion.N7.ProposalBridge
public import SKConstants.Completion.NReplay.Node
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators

namespace SKConstants.Completion.N9b
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint M1 LFine N9
variable {Ω : Type} [MeasurableSpace Ω]

theorem replayProposalGen_energy_eq_source (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r q : ℕ) (hn : 0 < r+q) :
    (∫ y, goeSpinHamiltonian (1/Real.sqrt (2*(r+q : ℕ))) y.1 y.2
      ∂replayProposalGen W β hβ δ r q rfl)/(r+q : ℕ) =
      ∫ z, LM5.growingSourceEnergy W β hβ δ r q z ∂SourceLinkedLaw W β hβ δ r q := by
  let Q := replayProposalGen W β hβ δ r q rfl
  let G := fun p : Spin (r+q) × Prim (r+q) => (physical (r+q) p.2,p.1)
  let S := fun z : (Fin (r+q) → Bool) × SourceInput δ r q =>
    (LM5.growingSourceMatrix W β hβ δ r q z.2,z.1)
  have hG : Measurable G :=
    ((continuous_goeMatrix _).measurable.comp measurable_snd).prodMk measurable_fst
  have hS : Measurable S :=
    ((LM5.measurable_growingSourceMatrix W β hβ δ r q).comp measurable_snd).prodMk measurable_fst
  have hTo : Measurable (fun z : (Fin (r+q) → Bool) × SourceInput δ r q =>
      (z.1,ToReplay W β hβ δ r q z.2)) :=
    measurable_fst.prodMk ((measurable_ToReplay W β hβ δ r q).comp measurable_snd)
  have hmap : Q.map G = (SourceLinkedLaw W β hβ δ r q).map S := by
    rw [N7.replayProposalGen_physical_eq_linkedReplay replayInputLaw_holds thresholdLink_holds,
      ← growingSource_toReplay_linked_law W β hβ δ r q hn,
      Measure.map_map (N7.measurable_pathReplayOutput δ r q) hTo]
    rfl
  have hH : Measurable (fun z : Matrix (Fin (r+q)) (Fin (r+q)) ℝ × Spin (r+q) =>
      quadraticHamiltonian z.1 z.2) :=
    LF0.measurable_coupled_energy Prod.fst Prod.snd measurable_fst measurable_snd
  have hprim := integral_map (μ := Q) hG.aemeasurable hH.aestronglyMeasurable
  have hsource := integral_map (μ := SourceLinkedLaw W β hβ δ r q)
    hS.aemeasurable hH.aestronglyMeasurable
  rw [hmap] at hprim
  have he : (∫ y, goeSpinHamiltonian (1/Real.sqrt (2*(r+q : ℕ))) y.1 y.2 ∂Q) =
      ∫ z, quadraticHamiltonian (LM5.growingSourceMatrix W β hβ δ r q z.2) z.1
        ∂SourceLinkedLaw W β hβ δ r q := hprim.symm.trans hsource
  rw [he]
  simp only [LM5.growingSourceEnergy, LM5.quadraticEnergy_signSpin_eq, integral_const_mul,
    div_eq_mul_inv, mul_comm]

theorem replayProposalGen_energy_eq_query (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r q : ℕ) (hn : 0 < r+q) :
    (∫ y, goeSpinHamiltonian (1/Real.sqrt (2*(r+q : ℕ))) y.1 y.2
      ∂replayProposalGen W β hβ δ r q rfl)/(r+q : ℕ) =
      ∫ z, LM5.growingSourceQueryEnergy W β hβ δ r q z ∂SourceLinkedLaw W β hβ δ r q :=
  (replayProposalGen_energy_eq_source W β hβ δ r q hn).trans
    (LM5.growingSource_energy_integral_eq_query W β hβ δ r q hn)

theorem replayProposalGen_zeroQueries_energy (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r : ℕ) (hr : 0 < r) :
    (∫ y, goeSpinHamiltonian (1/Real.sqrt (2*(r+0 : ℕ))) y.1 y.2
      ∂replayProposalGen W β hβ δ r 0 rfl)/(r+0 : ℕ) = 0 := by
  rw [replayProposalGen_energy_eq_source W β hβ δ r 0 (by omega)]
  exact fineEnergy_source_zeroQueries_mean W β hβ δ r hr

end SKConstants.Completion.N9b
