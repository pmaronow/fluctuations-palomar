module

public import SKConstants.Completion.N9Y1.ProjectionTrace
public import SKConstants.Completion.N9Y1.ScalarMoments
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators Matrix

namespace SKConstants.Completion.N9Y1
open SKConstantsOAI.ZeroTemperatureSK GaussianProposal FineInformation LFine LQ N9 M1 Blueprint5
variable {Ω : Type*} [MeasurableSpace Ω]
attribute [local irreducible] fineCellRemovedSquare fineCellRemainingProjection
  M1.SourceTargets M1.Target M1.Update

theorem fineProjectionMoment_integrability_holds (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (hr : 0 < r) (e : Fin K) :
    Integrable (fineCellRemovedSquare W β hβ δ r K e) (SourceLinkedLaw W β hβ δ r K) ∧
      Integrable (fun z => fineCellRemovedSquare W β hβ δ r K e z^2)
        (SourceLinkedLaw W β hβ δ r K) :=
  ⟨fineCellRemovedSquare_integrable W β hβ δ hδ r K (by omega) e,
    fineCellRemovedSquare_sq_integrable W β hβ δ hδ r K (by omega) e⟩

theorem fineCellRemovedSquare_mean_le_one (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (hn : 0 < r+K)
    (e : Fin K) :
    (∫ z, fineCellRemovedSquare W β hβ δ r K e z ∂SourceLinkedLaw W β hβ δ r K) ≤ 1 := by
  have hQi : Integrable (fun z : (Fin (r+K) → Bool) × SourceInput δ r K =>
      queryTotalSquare (r+K : ℕ) (SourceTargets W β hβ δ r K z.2 e))
      (SourceLinkedLaw W β hβ δ r K) := by
    unfold queryTotalSquare dot
    simpa only [pow_two] using (integrable_finsetSum _ (fun i _ =>
      (N9b.sourceTarget_memLp W β hβ δ hδ r K hn e i 2).integrable_sq)).const_mul
        (((r+K : ℕ) : ℝ)⁻¹)
  have hQmean : (∫ z : (Fin (r+K) → Bool) × SourceInput δ r K,
      queryTotalSquare (r+K : ℕ) (SourceTargets W β hβ δ r K z.2 e)
        ∂SourceLinkedLaw W β hβ δ r K) = 1 := by
    simpa only [queryTotalSquare,dot,pow_two] using
      N9b.sourceTargets_norm_mean W β hβ δ hδ r K hn e
  exact (integral_mono_ae (fineCellRemovedSquare_integrable W β hβ δ hδ r K hn e)
    hQi (ae_of_all _ fun z => fineCellRemovedSquare_le_total W β hβ δ r K e z)).trans_eq hQmean

theorem sourceTarget_fourth_le_three (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (r K : ℕ) (hn : 0 < r+K)
    (e : Fin K) (i : Fin (r+K)) :
    (∫ z, SourceTargets W β hβ δ r K z.2 e i^4 ∂SourceLinkedLaw W β hβ δ r K) ≤
      3*(meshDuration δ e.val)^2/(actualFineScale W β δ e.val)^4 := by
  have h := N9b.sourceTarget_coordinate_hasLaw W β hβ δ hδ r K hn e i
  have he := h.integral_comp
    (show AEStronglyMeasurable (fun x : ℝ => x^4) _ from by fun_prop)
  simp only [Function.comp_apply] at he
  rw [he,integral_map (N9b.measurable_normalizedIncrement W β _ _).aemeasurable (by fun_prop)]
  simpa only [growingQueryTime_succ,NNReal.coe_add,add_sub_cancel_left,
    actualFineScale,meshDuration] using normalizedIncrement_fourth_le_three W β hβ
      (growingQueryTime δ e.val) (growingQueryTime δ (e.val+1))
      ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ _))

theorem fineProjectionMoment_zero_holds (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (r K : ℕ) (e : Fin K) (he : e.val=0) :
    Integrable (fineCellRemovedSquare W β hβ δ r K e) (SourceLinkedLaw W β hβ δ r K) ∧
      Integrable (fun z => fineCellRemovedSquare W β hβ δ r K e z^2)
        (SourceLinkedLaw W β hβ δ r K) ∧
      (∫ z, fineCellRemovedSquare W β hβ δ r K e z ∂SourceLinkedLaw W β hβ δ r K) ≤
        ((e.val+1 : ℕ) : ℝ)*meshDuration δ e.val/
          (((r+K : ℕ) : ℝ)*(actualFineScale W β δ e.val)^2) ∧
      (∫ z, fineCellRemovedSquare W β hβ δ r K e z^2 ∂SourceLinkedLaw W β hβ δ r K) ≤
        3*(((e.val+1 : ℕ) : ℝ)^2+((e.val+1 : ℕ) : ℝ))*(meshDuration δ e.val)^2/
          (((r+K : ℕ) : ℝ)^2*(actualFineScale W β δ e.val)^4) := by
  have hz : fineCellRemovedSquare W β hβ δ r K e = 0 :=
    funext (fineCellRemovedSquare_eq_zero_of_val_zero W β hβ δ r K e he)
  rw [hz]
  refine ⟨integrable_const 0,?_,?_,?_⟩
  · simpa only [Pi.zero_apply,zero_pow (by omega : 2 ≠ 0)] using
      (integrable_const (0 : ℝ) : Integrable
        (fun _ : (Fin (r+K) → Bool) × SourceInput δ r K => (0 : ℝ))
        (SourceLinkedLaw W β hβ δ r K))
  · simp only [Pi.zero_apply,integral_zero]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (growingQueryDuration δ e.val).coe_nonneg)
      (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  · simp only [Pi.zero_apply,zero_pow (by omega : 2 ≠ 0),integral_zero]
    positivity

end SKConstants.Completion.N9Y1
