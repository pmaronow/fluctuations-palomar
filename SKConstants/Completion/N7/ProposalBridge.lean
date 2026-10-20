module

public import SKConstants.Completion.N7.ReplayKL
public import SKConstants.Completion.N7.PrimitiveLift
public import SKConstants.Completion.Blueprint.NodesLower

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory InformationTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology unitInterval

namespace SKConstants.Completion.N7
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal Blueprint LC4a LM3
variable {Ω : Type} [MeasurableSpace Ω]

def replayOutputRule (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ)
    (p : Matrix (Fin (r₀ + q)) (Fin (r₀ + q)) ℝ ×
      (ReplayAux δ r₀ q × (Fin (r₀ + q) → I))) : Spin (r₀ + q) :=
  thresholdSpin (replayMag W β hβ δ r₀ q (scalarGrowingSourceHorizon δ q) p.1 p.2.1) p.2.2

theorem measurable_replayOutputRule (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r₀ q : ℕ) : Measurable (replayOutputRule W β hβ δ r₀ q) :=
  (measurable_thresholdSpin (r₀ + q)).comp
    (((measurable_replayMag W β hβ δ r₀ q _).comp
      (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)

theorem replayProposalGen_eq_product_rule
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r₀ q : ℕ) :
    replayProposalGen W β hβ δ r₀ q rfl =
      ((primLaw (r₀ + q)).prod ((replayAuxLaw W δ r₀ q).prod (thresholdLaw (r₀ + q)))).map
        (fun p => (replayOutputRule W β hβ δ r₀ q (physical (r₀ + q) p.1, p.2), p.1)) := by
  have hK : Measurable (fun p : Prim (r₀ + q) ×
      (ReplayAux δ r₀ q × (Fin (r₀ + q) → I)) =>
      (replayOutputRule W β hβ δ r₀ q (physical (r₀ + q) p.1, p.2), p.1)) :=
    ((measurable_replayOutputRule W β hβ δ r₀ q).comp
      (((continuous_goeMatrix _).measurable.comp measurable_fst).prodMk measurable_snd)).prodMk
      measurable_fst
  rw [← (measurePreserving_prodAssoc (primLaw (r₀ + q))
    (replayAuxLaw W δ r₀ q) (thresholdLaw (r₀ + q))).map_eq,
    Measure.map_map hK MeasurableEquiv.prodAssoc.measurable]
  rfl

theorem replayProposalGen_physical_output
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r₀ q : ℕ) :
    (replayProposalGen W β hβ δ r₀ q rfl).map
        (fun p => (physical (r₀ + q) p.2, p.1)) =
      ((skDisorderLaw (r₀ + q)).prod
        ((replayAuxLaw W δ r₀ q).prod (thresholdLaw (r₀ + q)))).map
        (fun p => (p.1, replayOutputRule W β hβ δ r₀ q p)) := by
  have hG : Measurable (fun p : Spin (r₀ + q) × Prim (r₀ + q) =>
      (physical (r₀ + q) p.2, p.1)) :=
    ((continuous_goeMatrix _).measurable.comp measurable_snd).prodMk measurable_fst
  have hK : Measurable (fun p : Prim (r₀ + q) ×
      (ReplayAux δ r₀ q × (Fin (r₀ + q) → I)) =>
      (replayOutputRule W β hβ δ r₀ q (physical (r₀ + q) p.1, p.2), p.1)) :=
    ((measurable_replayOutputRule W β hβ δ r₀ q).comp
      (((continuous_goeMatrix _).measurable.comp measurable_fst).prodMk measurable_snd)).prodMk
      measurable_fst
  have hF : Measurable (fun p => (p.1, replayOutputRule W β hβ δ r₀ q p)) :=
    measurable_fst.prodMk (measurable_replayOutputRule W β hβ δ r₀ q)
  rw [replayProposalGen_eq_product_rule, Measure.map_map hG hK]
  change _ = (((primLaw (r₀ + q)).map (physical (r₀ + q))).prod
    ((replayAuxLaw W δ r₀ q).prod (thresholdLaw (r₀ + q)))).map _
  rw [← Measure.map_id (μ := (replayAuxLaw W δ r₀ q).prod (thresholdLaw (r₀ + q))),
    Measure.map_prod_map _ _ (continuous_goeMatrix _).measurable measurable_id,
    Measure.map_map hF ((continuous_goeMatrix _).measurable.prodMap measurable_id)]
  simp only [Measure.map_id]
  rfl

theorem replayProposalGen_physical_eq_linkedReplay
    (hInput : ReplayInputLawStatement) (hThreshold : ThresholdLinkStatement)
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r₀ q : ℕ) :
    (replayProposalGen W β hβ δ r₀ q rfl).map
        (fun p => (physical (r₀ + q) p.2, p.1)) =
      (M1.ReplayLinkedLaw W β hβ δ r₀ q).map (pathReplayOutput δ r₀ q) := by
  let ins : Prim (r₀ + q) × ReplayAux δ r₀ q → M1.ReplayInput δ r₀ q :=
    fun p => replayInput (physical (r₀ + q) p.1) p.2
  have hIns : Measurable ins := (measurable_replayInput δ r₀ q).comp
    (((continuous_goeMatrix _).measurable.comp measurable_fst).prodMk measurable_snd)
  let draw : M1.ReplayInput δ r₀ q × (Fin (r₀ + q) → I) →
      Spin (r₀ + q) × M1.ReplayInput δ r₀ q := fun p =>
    (thresholdSpin (fun i => actualParisiFullMagnetization β (M1.Horizon δ q)
      (actualParisiGrowingReplayField W β hβ δ r₀ q (M1.Horizon δ q) p.1 i)) p.2, p.1)
  have hDraw : Measurable draw := by
    have hm : Measurable (fun p : M1.ReplayInput δ r₀ q => fun i =>
        actualParisiFullMagnetization β (M1.Horizon δ q)
          (actualParisiGrowingReplayField W β hβ δ r₀ q (M1.Horizon δ q) p i)) := by
      apply Measurable.of_eval
      intro i
      exact (((continuous_actualParisiFullMagnetization β).comp
        (continuous_const.prodMk continuous_id)).measurable).comp
          ((measurable_pi_apply i).comp (M1.measurable_ReplayField W β hβ δ r₀ q _))
    exact ((measurable_thresholdSpin (r₀ + q)).comp
      ((hm.comp measurable_fst).prodMk measurable_snd)).prodMk measurable_fst
  have hLaw : ((((primLaw (r₀ + q)).prod (replayAuxLaw W δ r₀ q)).prod
      (thresholdLaw (r₀ + q))).map (Prod.map ins id)) =
      (M1.ReplayLaw W δ r₀ q).prod (thresholdLaw (r₀ + q)) := by
    rw [← Measure.map_prod_map _ _ hIns measurable_id, Measure.map_id]
    exact congrArg (fun μ => μ.prod (thresholdLaw (r₀ + q))) (hInput W δ r₀ q)
  rw [← hThreshold W β hβ δ r₀ q, Measure.map_map (measurable_pathReplayOutput δ r₀ q) hDraw,
    ← hLaw, Measure.map_map ((measurable_pathReplayOutput δ r₀ q).comp hDraw)
      (hIns.prodMap measurable_id)]
  unfold replayProposalGen
  have hm : Measurable (fun p : (Prim (r₀ + q) × ReplayAux δ r₀ q) × (Fin (r₀ + q) → I) =>
      (replaySpinGen W β hβ δ r₀ q rfl p.1.1 p.1.2 p.2, p.1.1)) :=
    ((measurable_thresholdSpin (r₀ + q)).comp
      (((measurable_castReplayMag W β hβ δ r₀ q rfl _).comp measurable_fst).prodMk
        measurable_snd)).prodMk measurable_fst.fst
  have hG : Measurable (fun p : Spin (r₀ + q) × Prim (r₀ + q) =>
      (physical (r₀ + q) p.2, p.1)) :=
    ((continuous_goeMatrix _).measurable.comp measurable_snd).prodMk measurable_fst
  rw [Measure.map_map hG hm]
  rfl

theorem replayProposalGen_KL_le_physical
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r₀ q : ℕ)
    (hn : 0 < r₀ + q) :
    klDiv (replayProposalGen W β hβ δ r₀ q rfl)
      ((primitiveJointGibbsLaw (r₀ + q) β (1 / Real.sqrt (2 * (r₀ + q : ℕ)))).map Prod.swap) ≤
      klDiv (((skDisorderLaw (r₀ + q)).prod
        ((replayAuxLaw W δ r₀ q).prod (thresholdLaw (r₀ + q)))).map
        (fun p => (p.1, replayOutputRule W β hβ δ r₀ q p))) (skJointLaw (r₀ + q) β) := by
  have hnR : 0 < (r₀ + q : ℕ) := hn
  have hσ : (1 / Real.sqrt (2 * (r₀ + q : ℕ) : ℝ)) ≠ 0 := by
    apply one_div_ne_zero
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    positivity
  rw [replayProposalGen_eq_product_rule]
  exact randomizedPrimitiveProposal_KL_le (r₀ + q) β _ hσ
    ((replayAuxLaw W δ r₀ q).prod (thresholdLaw (r₀ + q)))
    (replayOutputRule W β hβ δ r₀ q) (measurable_replayOutputRule W β hβ δ r₀ q)

end SKConstants.Completion.N7
