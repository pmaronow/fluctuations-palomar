module

public import ComparisonSelectedScore

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal

theorem physical_selected_left_variance_middle_integrable (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ) {a b δ p q : ℝ}
    (hδ : 0 < δ) (hp : a+δ ≤ p) (hpq : p ≤ q) (hq : q ≤ b-δ)
    (hx : ∀u:Fin K,x u < x (u.val+1)) :
    IntervalIntegrable (fun t=>selectedScoreVariance n steps q0 (selectedLeftWeight steps J unit x a t)) volume p q := by
  have hc := physical_selected_left_variance_continuousOn n K steps ha q0 J unit x (a:=a) (b:=b) hδ hx
  have hc' := hc.mono (Icc_subset_Icc hp (by linarith : q ≤ b))
  exact hc'.intervalIntegrable_of_Icc (μ:=volume) hpq

theorem physical_selected_right_variance_middle_integrable (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ) {a b δ p q : ℝ}
    (hδ : 0 < δ) (hp : a+δ ≤ p) (hpq : p ≤ q) (hq : q ≤ b-δ)
    (hx : ∀u:Fin K,x u < x (u.val+1)) :
    IntervalIntegrable (fun t=>selectedScoreVariance n steps q0 (selectedRightWeight steps J unit x b t)) volume p q := by
  have hc := physical_selected_right_variance_continuousOn n K steps ha q0 J unit x (a:=a) (b:=b) hδ hx
  have hc' := hc.mono (Icc_subset_Icc (by linarith : a ≤ p) hq)
  exact hc'.intervalIntegrable_of_Icc (μ:=volume) hpq

theorem physical_selected_left_variance_middle_le (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ) {a b δ p q tau : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hδ : 0 < δ)
    (hp : a+δ ≤ p) (hpq : p ≤ q) (hq : q ≤ b-δ)
    (hx : ∀u:Fin K,x u < x (u.val+1)) (htau : 0 ≤ tau)
    (henergy : ∀u:Fin K,physicalSelectedUnitEnergy n steps q0 J unit u ≤ tau*(x (u.val+1)-x u)) :
    (∫t in p..q,selectedScoreVariance n steps q0 (selectedLeftWeight steps J unit x a t)) ≤ tau*Real.log ((b-a)/δ) := by
  have hδb : δ ≤ b-a := by linarith
  have hfull := physical_selected_left_variance_integral_le n K steps ha q0 J unit x hstart hend hδ hδb hx htau henergy
  have hc := physical_selected_left_variance_continuousOn n K steps ha q0 J unit x (a:=a) (b:=b) hδ hx
  have hi := hc.intervalIntegrable_of_Icc (μ:=volume) (by linarith : a+δ ≤ b)
  have hm := intervalIntegral.integral_mono_interval hp hpq (by linarith : q ≤ b)
    (Filter.Eventually.of_forall (fun _=>variance_nonneg _ _)) hi
  exact hm.trans hfull

theorem physical_selected_right_variance_middle_le (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ) {a b δ p q tau : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hδ : 0 < δ)
    (hp : a+δ ≤ p) (hpq : p ≤ q) (hq : q ≤ b-δ)
    (hx : ∀u:Fin K,x u < x (u.val+1)) (htau : 0 ≤ tau)
    (henergy : ∀u:Fin K,physicalSelectedUnitEnergy n steps q0 J unit u ≤ tau*(x (u.val+1)-x u)) :
    (∫t in p..q,selectedScoreVariance n steps q0 (selectedRightWeight steps J unit x b t)) ≤ tau*Real.log ((b-a)/δ) := by
  have hδb : δ ≤ b-a := by linarith
  have hfull := physical_selected_right_variance_integral_le n K steps ha q0 J unit x hstart hend hδ hδb hx htau henergy
  have hc := physical_selected_right_variance_continuousOn n K steps ha q0 J unit x (a:=a) (b:=b) hδ hx
  have hi := hc.intervalIntegrable_of_Icc (μ:=volume) (by linarith : a ≤ b-δ)
  have hm := intervalIntegral.integral_mono_interval (by linarith : a ≤ p) hpq hq
    (Filter.Eventually.of_forall (fun _=>variance_nonneg _ _)) hi
  exact hm.trans hfull

end OAI.SKFluctuations.WholeUnitSideKernel
