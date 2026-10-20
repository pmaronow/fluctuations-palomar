module

public import PhysicalOverlapClockDerivative

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem physicalFilledOverlap_nonneg (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (T t : ℝ) (x : FeatureIndex n → ℝ) :
    0 ≤ physicalFilledOverlap n d L steps ha hm T t x := by
  apply Finset.sum_nonneg
  intro i _
  change 0 ≤ (physicalSpinFeatureJet n d i L steps ha x).filledSquare hm T t 0
  unfold HeatJet.filledSquare
  apply clockTest_nonneg ((physicalSpinFeatureJet n d i L steps ha x).evolve hm (T - t)).lipschitz
  intro y
  exact sq_nonneg _

theorem physicalFilledOverlap_subinterval_eq_integral_energy (n d : ℕ)
    (L : (Fin (d + 1) → ℝ) →L[ℝ] (FeatureIndex n → ℝ))
    (steps : List (GaussianStep (FeatureIndex n))) {a m T l r : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ T)
    (x : FeatureIndex n → ℝ) :
    (∫ t in l..r, physicalFilledOverlapEnergy n d L steps ha hm T t x) =
      physicalFilledOverlap n d L steps ha hm T r x -
        physicalFilledOverlap n d L steps ha hm T l x := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlr
    (physicalFilledOverlap_continuous n d L steps ha hm T x).continuousOn
  · intro t ht
    exact physicalFilledOverlap_hasDerivAt n d L steps ha hm
      ⟨by linarith [ht.1], by linarith [ht.2]⟩ x
  · exact (physicalFilledOverlapEnergy_continuous n d L steps ha hm T x).intervalIntegrable l r

theorem physicalFilledOverlap_subinterval_eq_integral_fieldTrace (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex (n + 1)))) {a m T l r : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ T)
    (x : FeatureIndex (n + 1) → ℝ) :
    (n + 1 : ℝ) * (∫ t in l..r, physicalFilledFieldTraceExpectation n steps ha hm T t x) =
      physicalFilledOverlap (n + 1) n (physicalUnitFieldDriver (n + 1)) steps ha hm T r x -
        physicalFilledOverlap (n + 1) n (physicalUnitFieldDriver (n + 1)) steps ha hm T l x := by
  have h := physicalFilledOverlap_subinterval_eq_integral_energy
    (n + 1) n (physicalUnitFieldDriver (n + 1)) steps ha hm hl hlr hr x
  simp_rw [physicalFilledOverlapEnergy_eq_fieldTrace] at h
  rw [intervalIntegral.integral_const_mul] at h
  exact h

theorem physicalFilledFieldTrace_band_le (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex (n + 1)))) {a m T l r M : ℝ}
    (ha : OrderedSteps a steps) (hm : 0 < m) (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ T)
    (x : FeatureIndex (n + 1) → ℝ)
    (hmean : physicalFilledOverlap (n + 1) n (physicalUnitFieldDriver (n + 1))
      steps ha hm T r x ≤ M) :
    (∫ t in l..r, physicalFilledFieldTraceExpectation n steps ha hm T t x) ≤ M / (n + 1 : ℝ) := by
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
  have h := physicalFilledOverlap_subinterval_eq_integral_fieldTrace n steps ha hm hl hlr hr x
  have h0 := physicalFilledOverlap_nonneg (n + 1) n
    (physicalUnitFieldDriver (n + 1)) steps ha hm T l x
  nlinarith

theorem trace_integral_le_from_energy {l r k M : ℝ} {E H : ℝ → ℝ}
    (hlr : l ≤ r) (hk : 0 < k)
    (hE : IntervalIntegrable E volume l r) (hH : IntervalIntegrable H volume l r)
    (hfield : ∀ t ∈ Icc l r, k * H t ≤ E t)
    (hcap : (∫ t in l..r, E t) ≤ M) :
    (∫ t in l..r, H t) ≤ M / k := by
  apply (le_div_iff₀ hk).mpr
  have h := intervalIntegral.integral_mono_on hlr (hH.const_mul k) hE hfield
  rw [intervalIntegral.integral_const_mul] at h
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
