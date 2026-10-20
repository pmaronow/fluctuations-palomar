module

public import SKConstants.Completion.Y1.Centering
public import SKConstants.Completion.N9Y2.EarlierFactorization
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

def earlierRowPastLaw (W : BrownianSystem Ω) (δ : ℝ≥0) {K : ℕ} (e : Fin K) :
    Measure (ScalarContinuousPath (growingQueryTime δ e.val) ×
      ScalarContinuousPath (growingQueryTime δ e.val)) :=
  (scalarPrimitiveBrownianPathLaw W (growingQueryTime δ e.val)).prod
    (scalarPrimitiveBrownianPathLaw W (growingQueryTime δ e.val))

instance earlierRowPastLaw_probability (W : BrownianSystem Ω) (δ : ℝ≥0) {K : ℕ} (e : Fin K) :
    IsProbabilityMeasure (earlierRowPastLaw W δ e) := by unfold earlierRowPastLaw; infer_instance

def earlierRowFreshLaw (W : BrownianSystem Ω) (δ : ℝ≥0) (K : ℕ) (e : Fin K) :
    Measure (ℝ × FreshRowSeed (growingQueryDuration δ e.val)
      (Horizon δ K-growingQueryTime δ (e.val+1))) :=
  (gaussianReal 0 1).prod (freshRowSeedLaw W (growingQueryDuration δ e.val)
    (Horizon δ K-growingQueryTime δ (e.val+1)))

instance earlierRowFreshLaw_probability (W : BrownianSystem Ω) (δ : ℝ≥0) (K : ℕ) (e : Fin K) :
    IsProbabilityMeasure (earlierRowFreshLaw W δ K e) := by unfold earlierRowFreshLaw; infer_instance

theorem earlierFreshTarget_integral_eq_model (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (e : Fin K)
    (F : (ScalarContinuousPath (growingQueryTime δ e.val) ×
      ScalarContinuousPath (growingQueryTime δ e.val)) × ℝ → ℝ) (hF : Measurable F) :
    (∫ u, F (u.1,earlierFreshTarget W β hβ δ hδ K e u.1 u.2)
      ∂(earlierRowPastLaw W δ e).prod (earlierRowFreshLaw W δ K e)) =
      ∫ u, F (modelDriverPast W W β hβ (growingQueryTime δ e.val) u,
        normalizedIncrement W β (growingQueryTime δ e.val)
          (growingQueryTime δ (e.val+1)) u.1) ∂W.law.prod W.law := by
  let a := growingQueryTime δ e.val
  let h := growingQueryDuration δ e.val
  let f := Horizon δ K-growingQueryTime δ (e.val+1)
  let H := Horizon δ K
  have ha : a ≤ H := (growingQueryTime_strictMono δ hδ).monotone (by omega)
  let R := castDriverHistory (earlierCell_horizon_eq δ hδ K e) ∘ freshRowHistory W β hβ a h f
  have hR : Measurable R := (measurable_castDriverHistory _).comp
    (measurable_freshRowHistory W β hβ a h f)
  let G := fun v : ScalarDriverHistory H =>
    F (historyDriverPast a H ha v,NDH.historyMixedRow W β δ K v (LGram.posteriorIndex K e))
  have hG : Measurable G := hF.comp ((measurable_historyDriverPast a H ha).prodMk
    ((EuclideanSpace.proj (LGram.posteriorIndex K e)).continuous.measurable.comp
      (NDH.measurable_historyMixedRow W β δ K)))
  have he : (fun u => G (R u)) = (fun u => F (u.1,earlierFreshTarget W β hβ δ hδ K e u.1 u.2)) := by
    funext u
    change F (_,_) = _
    dsimp only [R,Function.comp_apply]
    rw [freshRowHistory_at_horizon_past W β hβ a h f H (earlierCell_horizon_eq δ hδ K e) ha u]
    rfl
  have hlaw : ((earlierRowPastLaw W δ e).prod (earlierRowFreshLaw W δ K e)).map R =
      (actualParisiFullQuerySpinLaw W W β H).map (NDH.modelFullHistory W W β hβ H) :=
    freshRowHistory_law_at_horizon W β hβ a h f H (growingQueryDuration_pos δ hδ e.val)
      (earlierCell_horizon_eq δ hδ K e)
  let i : Fin (1+K) := 0
  have hs := (sourceHistory_coordinate_hasLaw W β hβ δ hδ 1 K i).integral_comp
    hG.aestronglyMeasurable
  simp only [Function.comp_apply] at hs
  calc
    _ = ∫ u, G (R u) ∂(earlierRowPastLaw W δ e).prod (earlierRowFreshLaw W δ K e) := by rw [he]
    _ = ∫ v, G v ∂((earlierRowPastLaw W δ e).prod (earlierRowFreshLaw W δ K e)).map R :=
      (integral_map hR.aemeasurable hG.aestronglyMeasurable).symm
    _ = ∫ v, G v ∂(actualParisiFullQuerySpinLaw W W β H).map
        (NDH.modelFullHistory W W β hβ H) := by rw [hlaw]
    _ = ∫ z, G (SourceHistories W β hβ δ 1 K z i) ∂SourceLinkedLaw W β hβ δ 1 K := hs.symm
    _ = ∫ z, F (historyDriverPast a H ha (SourceHistories W β hβ δ 1 K z i),
        SourceTargets W β hβ δ 1 K z.2 e i) ∂SourceLinkedLaw W β hβ δ 1 K := by
      apply integral_congr_ae
      apply ae_of_all
      intro z
      exact congrArg (fun x => F (historyDriverPast a H ha
        (SourceHistories W β hβ δ 1 K z i),x)) (sourceTarget_eq_history W β hβ δ hδ 1 K z e i).symm
    _ = _ := sourcePastTarget_integral_eq_model W β hβ δ hδ 1 K e i F hF

theorem earlierFreshTarget_weighted_moments_le (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (e : Fin K)
    (F : ScalarContinuousPath (growingQueryTime δ e.val) ×
      ScalarContinuousPath (growingQueryTime δ e.val) → ℝ)
    (hF : Measurable F) (hcap : ∀ p, |F p| ≤ 1) :
    (∫ u, (F u.1*earlierFreshTarget W β hβ δ hδ K e u.1 u.2)^2
        ∂(earlierRowPastLaw W δ e).prod (earlierRowFreshLaw W δ K e)) ≤
      (meshDuration δ e.val*(∫ u, (F u.1)^2
        ∂(earlierRowPastLaw W δ e).prod (earlierRowFreshLaw W δ K e))) /
        (actualFineScale W β δ e.val)^2 ∧
    (∫ u, (F u.1*earlierFreshTarget W β hβ δ hδ K e u.1 u.2)^4
        ∂(earlierRowPastLaw W δ e).prod (earlierRowFreshLaw W δ K e)) ≤
      (3*(meshDuration δ e.val)^2*(∫ u, (F u.1)^2
        ∂(earlierRowPastLaw W δ e).prod (earlierRowFreshLaw W δ K e))) /
        (actualFineScale W β δ e.val)^4 := by
  rw [earlierFreshTarget_integral_eq_model W β hβ δ hδ K e (fun p => (F p.1*p.2)^2) (by fun_prop),
    earlierFreshTarget_integral_eq_model W β hβ δ hδ K e (fun p => (F p.1*p.2)^4) (by fun_prop),
    earlierFreshTarget_integral_eq_model W β hβ δ hδ K e (fun p => F p.1^2) (by fun_prop)]
  simpa only [growingQueryTime_succ,NNReal.coe_add,add_sub_cancel_left,actualFineScale,meshDuration]
    using normalizedIncrement_driverPast_weighted_moments_le W W β hβ
      (growingQueryTime δ e.val) (growingQueryTime δ (e.val+1))
      ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ _)) F hF hcap

theorem earlierFreshTarget_weighted_mean_zero (W : BrownianSystem Ω)
    (β : ℝ) (hβ : 1 < β) (δ : ℝ≥0) (hδ : 0 < δ) (K : ℕ) (e : Fin K)
    (F : ScalarContinuousPath (growingQueryTime δ e.val) ×
      ScalarContinuousPath (growingQueryTime δ e.val) → ℝ)
    (hF : Measurable F) (hcap : ∀ p, |F p| ≤ 1) :
    (∫ u, F u.1*earlierFreshTarget W β hβ δ hδ K e u.1 u.2
      ∂(earlierRowPastLaw W δ e).prod (earlierRowFreshLaw W δ K e)) = 0 := by
  rw [earlierFreshTarget_integral_eq_model W β hβ δ hδ K e (fun p => F p.1*p.2) (by fun_prop)]
  exact normalizedIncrement_driverPast_test_zero W W β hβ _ _
    ((growingQueryTime_strictMono δ hδ).monotone (Nat.le_succ _)) F hF hcap

end SKConstants.Completion.Y1
