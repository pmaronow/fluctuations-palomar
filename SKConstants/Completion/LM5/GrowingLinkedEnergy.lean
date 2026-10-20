module

public import SKConstants.Completion.LM5.LinkedEnergy
public import SKConstants.Completion.LC0.SourceReplay
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SKConstantsOAI.ZeroTemperatureSK
open scoped BigOperators Matrix NNReal ENNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace SKConstants.Completion.LM5
open GaussianProposal LC5
variable {Ω : Type*} [MeasurableSpace Ω]

abbrev GrowingStatic (δ : ℝ≥0) (r K : ℕ) :=
  ScalarGrowingPaperInitialData (M1.Horizon δ K) δ (r+K)

abbrev GrowingVisible (δ : ℝ≥0) (r K : ℕ) :=
  GrowingStatic δ r K × PaperCompletionNoise (r+K) K

def growingInitial (δ : ℝ≥0) (r K : ℕ) :=
  scalarGrowingPaperInitialState (M1.Horizon δ K) δ (r+K)

theorem measurable_growingTarget (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K k : ℕ) (i : Fin (r+K)) :
    Measurable (fun a => M1.Target W β hβ δ r K k a i) :=
  measurable_scalarMeshPaperTarget _ _ _ _ _ _
    (continuous_actualParisiFullMagnetization β).measurable _ _ _ _ _ _ k i

theorem measurable_growingUpdate (δ : ℝ≥0) (r K k : ℕ) :
    Measurable (Function.uncurry (M1.Update δ r K k)) :=
  measurable_scalarMeshPaperUpdate _ _ _ _ _ k

theorem growingUpdate_blind (δ : ℝ≥0) (r K j : ℕ)
    (p : ScalarGrowingPaperPast (M1.Horizon δ K) δ (r+K))
    (z w : EuclideanSpace ℝ (Fin (r+K) ⊕ Unit))
    (h : ∀ i, z (.inl i) = w (.inl i)) :
    M1.Update δ r K j p z = M1.Update δ r K j p w :=
  scalarGrowingPaperUpdate_eq_of_endpoint_eq _ _ _ _ _ p z w h

def growingTerminalObservation (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ)
    (p : ScalarGrowingPaperPast (M1.Horizon δ K) δ (r+K)) (i : Fin (r+K)) : ℝ :=
  scalarMeshPaperObservation (actualParisiFullScalarDrift β)
    (actualParisiNegativeRhoStieltjes W β hβ) (actualParisiSigmaStieltjes W β hβ)
    (continuous_actualParisiNegativeRhoStieltjes W β hβ)
    (continuous_actualParisiSigmaStieltjes W β hβ)
    (M1.Horizon δ K) (growingQueryDuration δ) (growingQueryTime δ) (r+K) p i
    (projIcc 0 (M1.Horizon δ K : ℝ) (M1.Horizon δ K).coe_nonneg (M1.Horizon δ K))

theorem measurable_growingTerminalObservation (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) :
    Measurable (growingTerminalObservation W β hβ δ r K) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (ContinuousMap.measurable_eval _).comp
    (measurable_scalarMeshPaperObservation _ _ _ _ _ _ _ _ _ i)

def growingVisibleField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (v : GrowingVisible δ r K) : Fin (r+K) → ℝ :=
  growingTerminalObservation W β hβ δ r K
    (proposalTerminalPast (M1.Update δ r K) K (growingInitial δ r K v.1)
      (visibleSource (r+K) K v.2))

theorem measurable_growingVisibleField (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) : Measurable (growingVisibleField W β hβ δ r K) :=
  (measurable_growingTerminalObservation W β hβ δ r K).comp
    ((M1.measurable_proposalTerminalPast (r+K) (M1.Update δ r K)
      (measurable_growingUpdate δ r K) K).comp
        (((measurable_scalarGrowingPaperInitialState _ _ _).comp measurable_fst).prodMk
          ((measurable_visibleSource (r+K) K).comp measurable_snd)))

def growingProjectOriginal (δ : ℝ≥0) (r K : ℕ) (s : M1.SourceInput δ r K) :
    GrowingStatic δ r K × StoppedNoise (Fin (r+K)) K :=
  (s.1, M1.Original δ r K s)

theorem measurable_growingProjectOriginal (δ : ℝ≥0) (r K : ℕ) :
    Measurable (growingProjectOriginal δ r K) :=
  measurable_fst.prodMk ((paperAugmentedOriginal_measurable (r+K) K).comp measurable_snd)

theorem growingProjectOriginal_law (W : BrownianSystem Ω) (δ : ℝ≥0) (r K : ℕ) :
    (M1.SourceLaw W δ r K).map (growingProjectOriginal δ r K) =
      (scalarGrowingPaperInitialDataLaw W (M1.Horizon δ K) δ (r+K)).prod
        (stoppedNoiseLaw (Fin (r+K)) K) := by
  change ((scalarGrowingPaperInitialDataLaw W (M1.Horizon δ K) δ (r+K)).prod
    (paperAugmentedNoiseLaw (r+K) K)).map
      (Prod.map id (paperAugmentedOriginal (r+K) K)) = _
  rw [← Measure.map_prod_map _ _ measurable_id (paperAugmentedOriginal_measurable (r+K) K),
    Measure.map_id, paperAugmentedOriginal_law]

theorem growingSourceField_factors_visible (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (s : M1.SourceInput δ r K) :
    M1.SourceField W β hβ δ r K (M1.Horizon δ K) s =
      growingVisibleField W β hβ δ r K
        (sourceVisible (r+K) K (growingProjectOriginal δ r K s)) := by
  have hp := proposalTerminalPast_factors_visible r (r+K) (M1.Target W β hβ δ r K)
    (M1.Update δ r K) (growingUpdate_blind δ r K) K
    (growingInitial δ r K s.1,1) (M1.Original δ r K s)
  change growingTerminalObservation W β hβ δ r K
    (proposalTerminalPast (M1.Update δ r K) K (growingInitial δ r K s.1)
      (M1.Original δ r K s)) = _
  rw [hp]
  rfl

theorem growingSource_linked_original_law (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) :
    (M1.SourceLinkedLaw W β hβ δ r K).map (Prod.map id (growingProjectOriginal δ r K)) =
      terminalSourceLaw (scalarGrowingPaperInitialDataLaw W (M1.Horizon δ K) δ (r+K))
        (r+K) K β (M1.Horizon δ K) (growingVisibleField W β hβ δ r K) := by
  have he : M1.SourceField W β hβ δ r K (M1.Horizon δ K) =
      (growingVisibleField W β hβ δ r K ∘ sourceVisible (r+K) K) ∘
        growingProjectOriginal δ r K := funext (growingSourceField_factors_visible W β hβ δ r K)
  unfold M1.SourceLinkedLaw
  rw [he, M1.terminalLinkedLaw_map β (M1.Horizon δ K) (M1.SourceLaw W δ r K)
    (growingProjectOriginal δ r K) (measurable_growingProjectOriginal δ r K)
    (growingVisibleField W β hβ δ r K ∘ sourceVisible (r+K) K)
    ((measurable_growingVisibleField W β hβ δ r K).comp (measurable_sourceVisible _ _)),
    growingProjectOriginal_law]
  rfl

def growingSourceDiscardedEnergy (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (z : (Fin (r+K) → Bool) × M1.SourceInput δ r K) : ℝ :=
  sourceDiscardedEnergy r K (r+K : ℕ) (M1.Target W β hβ δ r K) (M1.Update δ r K)
    (growingInitial δ r K) (z.1,growingProjectOriginal δ r K z.2)

theorem growingSourceDiscardedEnergy_eq_actual (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (z : (Fin (r+K) → Bool) × M1.SourceInput δ r K) :
    growingSourceDiscardedEnergy W β hβ δ r K z =
      quadraticEnergy (r+K : ℕ) (signSpin z.1)
        (actualParisiGrowingSourceAugmentedOutput W β hβ δ r K z.2.1 z.2.2).1 -
      paperQueryEnergy r (r+K) (r+K : ℕ) (M1.Target W β hβ δ r K) (M1.Update δ r K) K
        (growingInitial δ r K z.2.1,1) (M1.Original δ r K z.2) (signSpin z.1) := by
  simp only [growingSourceDiscardedEnergy, sourceDiscardedEnergy, growingProjectOriginal,
    actualParisiGrowingSourceAugmentedOutput, scalarGrowingSourceAugmentedOutput,
    actualPaperAugmentedOutput, actualPaperProposal, M1.Target, actualParisiGrowingSourceTarget,
    M1.Update, growingInitial, M1.Original, M1.Horizon, M1.Size, Nat.cast_add]

theorem growingSourceDiscardedEnergy_memLp_two (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (hN : 0 < r+K) :
    MemLp (growingSourceDiscardedEnergy W β hβ δ r K) 2 (M1.SourceLinkedLaw W β hβ δ r K) := by
  have hmp : MeasurePreserving (Prod.map id (growingProjectOriginal δ r K))
      (M1.SourceLinkedLaw W β hβ δ r K)
      (terminalSourceLaw (scalarGrowingPaperInitialDataLaw W (M1.Horizon δ K) δ (r+K))
        (r+K) K β (M1.Horizon δ K) (growingVisibleField W β hβ δ r K)) :=
    ⟨measurable_id.prodMap (measurable_growingProjectOriginal δ r K),
      growingSource_linked_original_law W β hβ δ r K⟩
  have h := sourceDiscardedEnergy_memLp_two
    (scalarGrowingPaperInitialDataLaw W (M1.Horizon δ K) δ (r+K)) r K hN β (M1.Horizon δ K)
    (M1.Target W β hβ δ r K) (M1.Update δ r K) (growingInitial δ r K)
    (measurable_scalarGrowingPaperInitialState _ _ _) (measurable_growingTarget W β hβ δ r K)
    (measurable_growingUpdate δ r K) (growingUpdate_blind δ r K)
    (growingVisibleField W β hβ δ r K) (measurable_growingVisibleField W β hβ δ r K)
  exact h.comp_measurePreserving hmp

theorem growingSourceDiscardedEnergy_centered_test (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (δ : ℝ≥0) (r K : ℕ) (hN : 0 < r+K)
    (φ : (Fin (r+K) → Bool) × GrowingVisible δ r K → ℝ)
    (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, |φ t| ≤ C) :
    let F := fun z : (Fin (r+K) → Bool) × M1.SourceInput δ r K =>
      φ (z.1,sourceVisible (r+K) K (growingProjectOriginal δ r K z.2)) *
        growingSourceDiscardedEnergy W β hβ δ r K z
    Integrable F (M1.SourceLinkedLaw W β hβ δ r K) ∧
      (∫ z, F z ∂M1.SourceLinkedLaw W β hβ δ r K) = 0 := by
  have h := sourceDiscardedEnergy_centered_test
    (scalarGrowingPaperInitialDataLaw W (M1.Horizon δ K) δ (r+K)) r K hN β (M1.Horizon δ K)
    (M1.Target W β hβ δ r K) (M1.Update δ r K) (growingInitial δ r K)
    (measurable_scalarGrowingPaperInitialState _ _ _) (measurable_growingTarget W β hβ δ r K)
    (measurable_growingUpdate δ r K) (growingUpdate_blind δ r K)
    (growingVisibleField W β hβ δ r K) (measurable_growingVisibleField W β hβ δ r K) φ hφ C hC
  have hmp : MeasurePreserving (Prod.map id (growingProjectOriginal δ r K))
      (M1.SourceLinkedLaw W β hβ δ r K)
      (terminalSourceLaw (scalarGrowingPaperInitialDataLaw W (M1.Horizon δ K) δ (r+K))
        (r+K) K β (M1.Horizon δ K) (growingVisibleField W β hβ δ r K)) :=
    ⟨measurable_id.prodMap (measurable_growingProjectOriginal δ r K),
      growingSource_linked_original_law W β hβ δ r K⟩
  exact ⟨hmp.integrable_comp_of_integrable h.1,
    (hmp.hasLaw.integral_comp h.1.aestronglyMeasurable).trans h.2⟩

end SKConstants.Completion.LM5
