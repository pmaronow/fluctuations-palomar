module

public import SKConstants.Completion.Y1.ProjectionMoments
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators Matrix

namespace SKConstants.Completion.Y1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation LFine LQ N9 M1 Blueprint5 N9T1 N9Y2
variable {Ω : Type*} [MeasurableSpace Ω]
attribute [local irreducible] M1.SourceTargets M1.Target M1.Update
  fineCellRemainingProjection fineCellRemovedSquare N9Y2.earlierFreshTarget earlierCellProjection

theorem fineCellRemovedSquare_integral_fresh (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (e : Fin K) (k : ℕ)
    (hi : Integrable (fun z => fineCellRemovedSquare W β hβ δ r K e z^k)
      (SourceLinkedLaw W β hβ δ r K)) :
    Integrable (fun u => (freshRemovedSquare W β hβ δ hδ r K e u.1 u.2)^k)
      ((Measure.pi (fun _ : Fin (r+K) => earlierRowPastLaw W δ e)).prod
        (freshRowsLaw W (growingQueryDuration δ e.val)
          (Horizon δ K-growingQueryTime δ (e.val+1)) (r+K))) ∧
    (∫ z, fineCellRemovedSquare W β hβ δ r K e z^k ∂SourceLinkedLaw W β hβ δ r K) =
      ∫ p, ∫ u, (freshRemovedSquare W β hβ δ hδ r K e p u)^k
        ∂freshRowsLaw W (growingQueryDuration δ e.val)
          (Horizon δ K-growingQueryTime δ (e.val+1)) (r+K)
        ∂Measure.pi (fun _ : Fin (r+K) => earlierRowPastLaw W δ e) := by
  let P := Measure.pi (fun _ : Fin (r+K) => earlierRowPastLaw W δ e)
  let Q := freshRowsLaw W (growingQueryDuration δ e.val)
    (Horizon δ K-growingQueryTime δ (e.val+1)) (r+K)
  letI : IsProbabilityMeasure Q := freshRowsLaw_probability W _ _ _
  letI : IsFiniteMeasure Q := IsZeroOrProbabilityMeasure.toIsFiniteMeasure Q
  letI : SigmaFinite Q := IsFiniteMeasure.toSigmaFinite Q
  letI : SFinite Q := inferInstance
  let S := fun z : (Fin (r+K) → Bool) × SourceInput δ r K =>
    ((fun i => N9c.historyDriverPast (growingQueryTime δ e.val) (Horizon δ K)
      ((growingQueryTime_strictMono δ hδ).monotone (by omega))
      (SourceHistories W β hβ δ r K z i)),SourceTargets W β hβ δ r K z.2 e)
  let R := fun u : OriginalPastRows (growingQueryTime δ e.val) (r+K) ×
      (Fin (r+K) → ℝ × FreshRowSeed (growingQueryDuration δ e.val)
        (Horizon δ K-growingQueryTime δ (e.val+1))) =>
    (u.1,fun i => earlierFreshTarget W β hβ δ hδ K e (u.1 i) (u.2 i))
  let G := fun v : OriginalPastRows (growingQueryTime δ e.val) (r+K) × (Fin (r+K) → ℝ) =>
    (pastRemovedSquare W β hβ δ r K e v.1 v.2)^k
  have hG : Measurable G := (measurable_pastRemovedSquare W β hβ δ r K e).pow_const k
  have hS : Measurable S :=
    (Measurable.of_eval fun i : Fin (r+K) => (N9c.measurable_historyDriverPast
      (growingQueryTime δ e.val) (Horizon δ K)
      ((growingQueryTime_strictMono δ hδ).monotone (by omega))).comp
        ((measurable_pi_apply i).comp (N9c.measurable_SourceHistories W β hβ δ r K))).prodMk
      (((measurable_pi_apply e).comp (measurable_SourceTargets W β hβ δ r K)).comp measurable_snd)
  have hR : Measurable R := measurable_fst.prodMk (Measurable.of_eval fun i : Fin (r+K) =>
    (measurable_earlierFreshTarget_joint W β hβ δ hδ K e).comp
      (f := fun u : OriginalPastRows (growingQueryTime δ e.val) (r+K) ×
        (Fin (r+K) → ℝ × FreshRowSeed (growingQueryDuration δ e.val)
          (Horizon δ K-growingQueryTime δ (e.val+1))) => (u.1 i,u.2 i))
      (((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)))
  have hlaw : (SourceLinkedLaw W β hβ δ r K).map S = (P.prod Q).map R :=
    sourcePastTargets_productFresh_law W β hβ δ hδ r K e
  have hGS (z : (Fin (r+K) → Bool) × SourceInput δ r K) :
      G (S z) = fineCellRemovedSquare W β hβ δ r K e z^k := by
    change (pastRemovedSquare W β hβ δ r K e _ _)^k = _
    unfold pastRemovedSquare fineCellRemovedSquare
    rw [earlierCellProjection_source W β hβ δ hδ r K e z]
  have hmap : Integrable G ((P.prod Q).map R) := by
    rw [← hlaw]
    apply (integrable_map_measure hG.aestronglyMeasurable hS.aemeasurable).mpr
    exact hi.congr (ae_of_all _ fun z => (hGS z).symm)
  have hprod : Integrable (fun u => G (R u)) (P.prod Q) :=
    (integrable_map_measure hG.aestronglyMeasurable hR.aemeasurable).mp hmap
  refine ⟨hprod,?_⟩
  calc
    _ = ∫ z, G (S z) ∂SourceLinkedLaw W β hβ δ r K :=
      integral_congr_ae (ae_of_all _ fun z => (hGS z).symm)
    _ = ∫ v, G v ∂(SourceLinkedLaw W β hβ δ r K).map S :=
      (integral_map hS.aemeasurable hG.aestronglyMeasurable).symm
    _ = ∫ v, G v ∂(P.prod Q).map R := by rw [hlaw]
    _ = ∫ u, G (R u) ∂P.prod Q := integral_map hR.aemeasurable hG.aestronglyMeasurable
    _ = _ := integral_prod _ hprod

end SKConstants.Completion.Y1
