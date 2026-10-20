module

public import SKConstants.Completion.Y1.FreshMoments
public import SKConstants.Completion.Y1.TestDisintegration
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

namespace SKConstants.Completion.Y1
open SKConstantsOAI.ZeroTemperatureSK LFine LQ N9b N9c N9Y2 M1
variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_earlierFreshTarget_joint (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (e : Fin K) :
    Measurable (fun u : FreshRowInput (growingQueryTime δ e.val) (growingQueryDuration δ e.val)
      (Horizon δ K-growingQueryTime δ (e.val+1)) =>
      earlierFreshTarget W β hβ δ hδ K e u.1 u.2) :=
  ((EuclideanSpace.proj (LGram.posteriorIndex K e)).continuous.measurable.comp
    (NDH.measurable_historyMixedRow W β δ K)).comp
      ((measurable_castDriverHistory _).comp (measurable_freshRowHistory W β hβ _ _ _))

theorem earlierFreshTarget_joint_memLp (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (e : Fin K) (q : ℝ≥0∞) :
    MemLp (fun u => earlierFreshTarget W β hβ δ hδ K e u.1 u.2) q
      ((earlierRowPastLaw W δ e).prod (earlierRowFreshLaw W δ K e)) :=
  MemLp.of_bound (measurable_earlierFreshTarget_joint W β hβ δ hδ K e).aestronglyMeasurable
    (2/actualFineScale W β δ e.val) (ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact historyTarget_abs_le W β δ K e _)

theorem earlierFreshTarget_conditional_moments (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (e : Fin K) :
    ∀ᵐ p ∂earlierRowPastLaw W δ e,
      (∫ u, earlierFreshTarget W β hβ δ hδ K e p u ∂earlierRowFreshLaw W δ K e) = 0 ∧
      (∫ u, earlierFreshTarget W β hβ δ hδ K e p u^2 ∂earlierRowFreshLaw W δ K e) ≤
        meshDuration δ e.val/(actualFineScale W β δ e.val)^2 ∧
      (∫ u, earlierFreshTarget W β hβ δ hδ K e p u^4 ∂earlierRowFreshLaw W δ K e) ≤
        3*(meshDuration δ e.val)^2/(actualFineScale W β δ e.val)^4 := by
  let f := fun u : FreshRowInput (growingQueryTime δ e.val) (growingQueryDuration δ e.val)
    (Horizon δ K-growingQueryTime δ (e.val+1)) => earlierFreshTarget W β hβ δ hδ K e u.1 u.2
  have h0 := ae_fiber_mean_zero_of_weighted_tests (earlierRowPastLaw W δ e)
    (earlierRowFreshLaw W δ K e) f
    ((earlierFreshTarget_joint_memLp W β hβ δ hδ K e 1).integrable le_rfl)
    (earlierFreshTarget_weighted_mean_zero W β hβ δ hδ K e)
  have h2 := ae_fiber_power_le_of_weighted_tests (earlierRowPastLaw W δ e)
    (earlierRowFreshLaw W δ K e) f 2 (by norm_num)
    (earlierFreshTarget_joint_memLp W β hβ δ hδ K e 2).integrable_sq
    (meshDuration δ e.val/(actualFineScale W β δ e.val)^2) (by
      intro F hF hcap
      exact (earlierFreshTarget_weighted_moments_le W β hβ δ hδ K e F hF hcap).1.trans_eq (by ring))
  have h4 := ae_fiber_power_le_of_weighted_tests (earlierRowPastLaw W δ e)
    (earlierRowFreshLaw W δ K e) f 4 (by norm_num)
    (integrable_fourth_of_memLp _ _ (earlierFreshTarget_joint_memLp W β hβ δ hδ K e 4))
    (3*(meshDuration δ e.val)^2/(actualFineScale W β δ e.val)^4) (by
      intro F hF hcap
      exact (earlierFreshTarget_weighted_moments_le W β hβ δ hδ K e F hF hcap).2.trans_eq (by ring))
  filter_upwards [h0,h2,h4] with p hp0 hp2 hp4
  exact ⟨hp0,hp2,hp4⟩

theorem earlierFreshTargets_conditional_moments (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (e : Fin K) (n : ℕ) :
    ∀ᵐ p ∂Measure.pi (fun _ : Fin n => earlierRowPastLaw W δ e), ∀ i : Fin n,
      (∫ u, earlierFreshTarget W β hβ δ hδ K e (p i) (u i)
        ∂freshRowsLaw W (growingQueryDuration δ e.val)
          (Horizon δ K-growingQueryTime δ (e.val+1)) n) = 0 ∧
      (∫ u, earlierFreshTarget W β hβ δ hδ K e (p i) (u i)^2
        ∂freshRowsLaw W (growingQueryDuration δ e.val)
          (Horizon δ K-growingQueryTime δ (e.val+1)) n) ≤
        meshDuration δ e.val/(actualFineScale W β δ e.val)^2 ∧
      (∫ u, earlierFreshTarget W β hβ δ hδ K e (p i) (u i)^4
        ∂freshRowsLaw W (growingQueryDuration δ e.val)
          (Horizon δ K-growingQueryTime δ (e.val+1)) n) ≤
        3*(meshDuration δ e.val)^2/(actualFineScale W β δ e.val)^4 := by
  have hi (i : Fin n) := (measurePreserving_eval (fun _ : Fin n => earlierRowPastLaw W δ e) i).quasiMeasurePreserving.ae
    (earlierFreshTarget_conditional_moments W β hβ δ hδ K e)
  filter_upwards [ae_all_iff.mpr hi] with p hp
  intro i
  have he (k : ℕ) : (∫ u, earlierFreshTarget W β hβ δ hδ K e (p i) (u i)^k
      ∂freshRowsLaw W (growingQueryDuration δ e.val)
        (Horizon δ K-growingQueryTime δ (e.val+1)) n) =
      ∫ u, earlierFreshTarget W β hβ δ hδ K e (p i) u^k ∂earlierRowFreshLaw W δ K e := by
    exact (show HasLaw (fun u : Fin n → ℝ × FreshRowSeed (growingQueryDuration δ e.val)
        (Horizon δ K-growingQueryTime δ (e.val+1)) => u i) (earlierRowFreshLaw W δ K e)
        (freshRowsLaw W (growingQueryDuration δ e.val)
          (Horizon δ K-growingQueryTime δ (e.val+1)) n) from
      ⟨(measurable_pi_apply i).aemeasurable,
        (measurePreserving_eval (fun _ : Fin n => earlierRowFreshLaw W δ K e) i).map_eq⟩).integral_comp
      ((measurable_earlierFreshTarget W β hβ δ hδ K e (p i)).pow_const k).aestronglyMeasurable
  have he0 := he 1
  simp only [pow_one] at he0
  rw [he0,he 2,he 4]
  exact hp i

end SKConstants.Completion.Y1
