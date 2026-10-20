module

public import SKConstants.Completion.N4c.ScalarLaw
public import SKConstants.Completion.LM1a.LinkedHistoryLaw
public import SKConstants.Completion.LM1b.ContinuousGraph
public import SKConstants.ParisiFullMixedRows

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators

namespace SKConstants.Completion.NDH
open SKConstantsOAI.ZeroTemperatureSK M1
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def modelFullHistory (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (H : ℝ≥0) (u : (Bool × Ω) × A) : ScalarDriverHistory H :=
  (u.1.1, (boundedDriftPastPath W (actualParisiFullScalarDrift β) H u.1.2,
    (brownianFinitePath (actualParisiQueryBrownianSystem W Z β hβ) H (u.1.2,u.2),
     brownianFinitePath (actualParisiAuxBrownianSystem W Z β hβ) H (u.1.2,u.2))))

theorem measurable_modelFullHistory (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (H : ℝ≥0) : Measurable (modelFullHistory W Z β hβ H) :=
  measurable_fst.fst.prodMk
    (((measurable_boundedDriftPastPath W _ H).comp measurable_fst.snd).prodMk
      (((measurable_brownianFinitePath _ H).comp
        (measurable_fst.snd.prodMk measurable_snd)).prodMk
       ((measurable_brownianFinitePath _ H).comp
        (measurable_fst.snd.prodMk measurable_snd))))

def pairFullHistory (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β) (H : ℝ≥0)
    (u : Bool × (ScalarContinuousPath H × ScalarContinuousPath H)) : ScalarDriverHistory H :=
  (u.1, (PairObservation W β hβ H u.2, u.2))

theorem measurable_pairFullHistory (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (H : ℝ≥0) : Measurable (pairFullHistory W β hβ H) :=
  measurable_fst.prodMk
    (((measurable_PairObservation W β hβ H).comp measurable_snd).prodMk measurable_snd)

theorem pair_full_path_law (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (H : ℝ≥0) :
    ((scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw Z H)).map
      (fun p => (PairObservation W β hβ H p,p)) =
    (W.law.prod Z.law).map (fun u =>
      (boundedDriftPastPath W (actualParisiFullScalarDrift β) H u.1,
        (brownianFinitePath (actualParisiQueryBrownianSystem W Z β hβ) H u,
         brownianFinitePath (actualParisiAuxBrownianSystem W Z β hβ) H u))) := by
  let := W.isProbability
  let := Z.isProbability
  let T := WeightedPair (actualParisiNegativeRhoStieltjes W β hβ)
    (actualParisiSigmaStieltjes W β hβ) (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ) H
  let F : ScalarContinuousPath H → ScalarContinuousPath H :=
    fun p => scalarForwardPicardPath (actualParisiFullScalarDrift β) H (0,p)
  have hF : Measurable F := (measurable_scalarForwardPicardPath _ H).comp
    (measurable_const.prodMk measurable_id)
  have hT : Measurable T := measurable_WeightedPair _ _ _ _ H
  let K : ((ScalarContinuousPath H × ScalarContinuousPath H) ×
      (ScalarContinuousPath H × ScalarContinuousPath H)) →
      ScalarContinuousPath H × (ScalarContinuousPath H × ScalarContinuousPath H) :=
    fun p => (F p.2.1,p.1)
  have hK : Measurable K := (hF.comp measurable_snd.fst).prodMk measurable_fst
  have hLeft : Measurable (fun p => (p,T p)) := measurable_id.prodMk hT
  have hRight : Measurable (fun p => (T p,p)) := hT.prodMk measurable_id
  have he := congrArg (fun ν => ν.map K)
    (actualParisi_continuousGraphExchange W Z β hβ H)
  change (((scalarPrimitiveBrownianPathLaw W H).prod
    (scalarPrimitiveBrownianPathLaw Z H)).map (fun p => (p,T p))).map K =
    (((scalarPrimitiveBrownianPathLaw W H).prod
    (scalarPrimitiveBrownianPathLaw Z H)).map (fun p => (T p,p))).map K at he
  rw [Measure.map_map hK hLeft, Measure.map_map hK hRight] at he
  change ((scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw Z H)).map
      (fun p => (PairObservation W β hβ H p,p)) =
    ((scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw Z H)).map
      (fun p => (F p.1,T p)) at he
  have hOriginal : Measurable (fun p => (F p.1,T p)) :=
    (hF.comp measurable_fst).prodMk hT
  rw [he, ← primitiveBrownianPairPath_law W Z H,
    Measure.map_map hOriginal
      ((measurable_scalarPrimitiveBrownianPathVersion W H).prodMap
        (measurable_scalarPrimitiveBrownianPathVersion Z H))]
  apply Measure.map_congr
  filter_upwards [actualParisiQueryAux_primitive_path_version W Z β hβ H,
    brownianFinitePath_version (actualParisiQueryBrownianSystem W Z β hβ) H,
    brownianFinitePath_version (actualParisiAuxBrownianSystem W Z β hβ) H,
    (measurePreserving_fst (μ := W.law) (ν := Z.law)).quasiMeasurePreserving.ae
      (scalarPrimitiveBrownianPathVersion_eq_finitePath_ae W H)] with u hu hB hD hM
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · change scalarForwardPicardPath _ H (0,scalarPrimitiveBrownianPathVersion W H u.1) = _
    rw [hM]
    rfl
  · exact ContinuousMap.ext (fun t => (congrArg Prod.fst (hu t)).symm.trans (hB t).symm)
  · exact ContinuousMap.ext (fun t => (congrArg Prod.snd (hu t)).symm.trans (hD t).symm)

theorem pair_full_history_law (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (H : ℝ≥0) :
    ((scalarHiddenPriorBool 0).prod
      ((scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw Z H))).map
        (pairFullHistory W β hβ H) =
    (((scalarHiddenPriorBool 0).prod W.law).prod Z.law).map
      (modelFullHistory W Z β hβ H) := by
  let := W.isProbability
  let := Z.isProbability
  let F := fun u : Ω × A =>
    (boundedDriftPastPath W (actualParisiFullScalarDrift β) H u.1,
      (brownianFinitePath (actualParisiQueryBrownianSystem W Z β hβ) H u,
       brownianFinitePath (actualParisiAuxBrownianSystem W Z β hβ) H u))
  have hF : Measurable F :=
    ((measurable_boundedDriftPastPath W _ H).comp measurable_fst).prodMk
      ((measurable_brownianFinitePath _ H).prodMk (measurable_brownianFinitePath _ H))
  have hP : Measurable (fun p : ScalarContinuousPath H × ScalarContinuousPath H =>
      (PairObservation W β hβ H p,p)) :=
    (measurable_PairObservation W β hβ H).prodMk measurable_id
  change ((scalarHiddenPriorBool 0).prod
    ((scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw Z H))).map
      (Prod.map id (fun p => (PairObservation W β hβ H p,p))) = _
  rw [← Measure.map_prod_map _ _ measurable_id hP, Measure.map_id,
    pair_full_path_law W Z β hβ H]
  have hb : (scalarHiddenPriorBool 0).prod ((W.law.prod Z.law).map F) =
      ((scalarHiddenPriorBool 0).prod (W.law.prod Z.law)).map (Prod.map id F) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map (scalarHiddenPriorBool 0) (W.law.prod Z.law) measurable_id hF)
  rw [hb]
  rw [← Measure.prodAssoc_prod]
  rw [Measure.map_map (measurable_id.prodMap hF) MeasurableEquiv.prodAssoc.measurable]
  rfl

def fullHistoryLinkDensity (β : ℝ) (H : ℝ≥0) (u : ScalarDriverHistory H) : ℝ≥0∞ :=
  ENNReal.ofReal (actualParisiSpinLinkDensity β u.1 H (u.2.1 ⟨H,H.coe_nonneg,le_rfl⟩))

theorem measurable_fullHistoryLinkDensity (β : ℝ) (H : ℝ≥0) :
    Measurable (fullHistoryLinkDensity β H) := by
  have h := measurable_scalarTerminalDensity β H
    (fun p : ScalarContinuousPath H × (ScalarContinuousPath H × ScalarContinuousPath H) =>
      p.1 ⟨H,H.coe_nonneg,le_rfl⟩)
    ((ContinuousMap.measurable_eval _).comp measurable_fst)
  exact h

theorem model_full_history_linked_eq_withDensity
    (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (H : ℝ≥0) :
    (actualParisiFullQuerySpinLaw W Z β H).map (modelFullHistory W Z β hβ H) =
      ((((scalarHiddenPriorBool 0).prod W.law).prod Z.law).map
        (modelFullHistory W Z β hβ H)).withDensity (fullHistoryLinkDensity β H) := by
  let := W.isProbability
  let := Z.isProbability
  let μ := ((scalarHiddenPriorBool 0).prod W.law).prod Z.law
  have hY := ((measurePreserving_snd (μ := scalarHiddenPriorBool 0) (ν := W.law)).comp
    (measurePreserving_fst (μ := (scalarHiddenPriorBool 0).prod W.law)
      (ν := Z.law))).quasiMeasurePreserving.ae
        (boundedDriftPastPath_version W (actualParisiFullScalarDrift β) H)
  have hd : (fun u : (Bool × Ω) × A =>
      ENNReal.ofReal (actualParisiFullTerminalSpinDensity β W H u.1)) =ᵐ[μ]
      fullHistoryLinkDensity β H ∘ modelFullHistory W Z β hβ H := by
    filter_upwards [hY] with u hu
    exact congrArg (fun y => ENNReal.ofReal (actualParisiSpinLinkDensity β u.1.1 H y))
      (hu ⟨H,H.coe_nonneg,le_rfl⟩).symm
  unfold actualParisiFullQuerySpinLaw actualParisiFullTerminalSpinLaw
  rw [prod_withDensity_left (measurable_actualParisiFullTerminalSpinDensity β W H).ennreal_ofReal,
    withDensity_congr_ae hd]
  exact map_withDensity_comp μ _ (measurable_modelFullHistory W Z β hβ H) _
    (measurable_fullHistoryLinkDensity β H)

theorem pair_linked_full_history_law (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (H : ℝ≥0) :
    (ScalarTerminalLinkedLaw β H
      ((scalarPrimitiveBrownianPathLaw W H).prod (scalarPrimitiveBrownianPathLaw Z H))
      (fun p => PairObservation W β hβ H p ⟨H,H.coe_nonneg,le_rfl⟩)).map
        (pairFullHistory W β hβ H) =
    (actualParisiFullQuerySpinLaw W Z β H).map (modelFullHistory W Z β hβ H) := by
  rw [model_full_history_linked_eq_withDensity W Z β hβ H]
  change (((scalarHiddenPriorBool 0).prod _).withDensity
    (fullHistoryLinkDensity β H ∘ pairFullHistory W β hβ H)).map _ = _
  rw [map_withDensity_comp _ _ (measurable_pairFullHistory W β hβ H) _
    (measurable_fullHistoryLinkDensity β H), pair_full_history_law W Z β hβ H]

end SKConstants.Completion.NDH
