module

public import SKConstants.Completion.NReplay.InputLaw
public import SKConstants.Completion.NReplay.ThresholdLink
public import SKConstants.Completion.NReplay.SpinMarginal

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal unitInterval
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.NReplay
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint

variable {Ω : Type*} [MeasurableSpace Ω]

theorem replayProposalGen_spin_eq_linked (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) :
    (replayProposalGen W β hβ δ r₀ q rfl).fst =
      (M1.ReplayLinkedLaw W β hβ δ r₀ q).map Prod.fst := by
  let F : Prim (r₀ + q) × ReplayAux δ r₀ q → M1.ReplayInput δ r₀ q :=
    fun z => replayInput (physical (r₀ + q) z.1) z.2
  have hF : Measurable F := (measurable_replayInput δ r₀ q).comp
    (((continuous_goeMatrix _).measurable.comp measurable_fst).prodMk measurable_snd)
  let Y := actualParisiGrowingReplayField W β hβ δ r₀ q (M1.Horizon δ q)
  have hY : Measurable Y := M1.measurable_ReplayField W β hβ δ r₀ q _
  let R : M1.ReplayInput δ r₀ q × (Fin (r₀ + q) → I) → Spin (r₀ + q) :=
    fun z => thresholdSpin (fun i => actualParisiFullMagnetization β (M1.Horizon δ q) (Y z.1 i)) z.2
  have hM : Measurable (fun v => fun i =>
      actualParisiFullMagnetization β (M1.Horizon δ q) (Y v i)) :=
    Measurable.of_eval (fun i => ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable.comp
        ((measurable_pi_apply i).comp hY))
  have hR : Measurable R := (measurable_thresholdSpin _).comp
    ((hM.comp measurable_fst).prodMk measurable_snd)
  have hinput : (((primLaw (r₀ + q)).prod (replayAuxLaw W δ r₀ q)).prod
      (thresholdLaw (r₀ + q))).map (Prod.map F id) =
        (M1.ReplayLaw W δ r₀ q).prod (thresholdLaw (r₀ + q)) := by
    rw [← Measure.map_prod_map _ _ hF measurable_id, Measure.map_id, replayInput_law]
  have hlinked := congrArg (fun ν => ν.map Prod.fst)
    (threshold_terminalLinkedLaw β (M1.Horizon δ q) (M1.ReplayLaw W δ r₀ q) Y hY)
  have hG : Measurable (fun z : M1.ReplayInput δ r₀ q × (Fin (r₀ + q) → I) =>
      (R z, z.1)) := hR.prodMk measurable_fst
  rw [Measure.map_map measurable_fst hG] at hlinked
  have hP : Measurable (fun z : (Prim (r₀ + q) × ReplayAux δ r₀ q) × (Fin (r₀ + q) → I) =>
      (replaySpinGen W β hβ δ r₀ q rfl z.1.1 z.1.2 z.2, z.1.1)) :=
    (hR.comp (hF.prodMap measurable_id)).prodMk measurable_fst.fst
  unfold replayProposalGen Measure.fst
  rw [Measure.map_map measurable_fst hP]
  change (((primLaw (r₀ + q)).prod (replayAuxLaw W δ r₀ q)).prod
    (thresholdLaw (r₀ + q))).map (R ∘ Prod.map F id) = _
  rw [← Measure.map_map hR (hF.prodMap measurable_id), hinput]
  exact hlinked

theorem replayProposalGen_spin_marginal (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (hδ : 0 < δ) (r₀ q : ℕ) (hN : 0 < r₀ + q)
    {n : ℕ} (h : r₀ + q = n) :
    (replayProposalGen W β hβ δ r₀ q h).fst = uniformSpinLaw n := by
  subst n
  rw [replayProposalGen_spin_eq_linked]
  exact replayLinkedLaw_spin_marginal W β hβ δ hδ r₀ q hN

end SKConstants.NReplay
