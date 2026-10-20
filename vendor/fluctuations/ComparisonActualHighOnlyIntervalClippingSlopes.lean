module

public import ClippedBarrierGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set
open scoped Topology NNReal

theorem interval_clipped_min_ae_slope {a b : ℝ} (hab : a ≤ b)
    {r w lower upper : ℝ → ℝ} {C D : ℝ≥0}
    (hr : LipschitzOnWith C r (Icc a b)) (hw : LipschitzOnWith D w (Icc a b))
    (hdr : ∀ᵐ u ∂volume, u ∈ Icc a b → lower u ≤ deriv r u ∧ deriv r u ≤ upper (r u))
    (hdw : ∀ᵐ u ∂volume, u ∈ Icc a b → w u ≤ r u →
      lower u ≤ deriv w u ∧ deriv w u ≤ upper (w u)) :
    ∀ᵐ u ∂volume, u ∈ Icc a b →
      lower u ≤ deriv (fun v => min (r v) (w v)) u ∧
      deriv (fun v => min (r v) (w v)) u ≤ upper (min (r u) (w u)) := by
  have hrv : AbsolutelyContinuousOnInterval r a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := C)
    simpa only [uIcc_of_le hab] using hr
  have hwv : AbsolutelyContinuousOnInterval w a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := D)
    simpa only [uIcc_of_le hab] using hw
  have hmv : AbsolutelyContinuousOnInterval (fun u => min (r u) (w u)) a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := max C D)
    simpa only [uIcc_of_le hab] using real_min_lipschitzOn hr hw
  filter_upwards [hdr, hdw, hrv.ae_differentiableAt, hwv.ae_differentiableAt, hmv.ae_differentiableAt]
    with u hdr hdw hr hw hm hum
  have hum' : u ∈ uIcc a b := by simpa only [uIcc_of_le hab] using hum
  rcases differentiable_min_selection (hr hum') (hw hum') (hm hum') with h | h
  · rw [h.1, h.2]
    exact hdr hum
  · rw [h.1, h.2]
    exact hdw hum (by rw [← h.1]; exact min_le_left _ _)

theorem interval_clipped_max_ae_slope_at_parent {a b : ℝ} (hab : a ≤ b)
    {r w lower upper : ℝ → ℝ} {C D : ℝ≥0}
    (hr : LipschitzOnWith C r (Icc a b)) (hw : LipschitzOnWith D w (Icc a b))
    (hdr : ∀ᵐ u ∂volume, u ∈ Icc a b → lower u ≤ deriv r u ∧ deriv r u ≤ upper u)
    (hdw : ∀ᵐ u ∂volume, u ∈ Icc a b → r u ≤ w u →
      lower u ≤ deriv w u ∧ deriv w u ≤ upper u) :
    ∀ᵐ u ∂volume, u ∈ Icc a b → lower u ≤ deriv (fun v => max (r v) (w v)) u ∧
      deriv (fun v => max (r v) (w v)) u ≤ upper u := by
  have hrv : AbsolutelyContinuousOnInterval r a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := C)
    simpa only [uIcc_of_le hab] using hr
  have hwv : AbsolutelyContinuousOnInterval w a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := D)
    simpa only [uIcc_of_le hab] using hw
  have hmv : AbsolutelyContinuousOnInterval (fun u => max (r u) (w u)) a b := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := max C D)
    simpa only [uIcc_of_le hab] using real_max_lipschitzOn hr hw
  filter_upwards [hdr, hdw, hrv.ae_differentiableAt, hwv.ae_differentiableAt, hmv.ae_differentiableAt]
    with u hdr hdw hr hw hm hum
  have hum' : u ∈ uIcc a b := by simpa only [uIcc_of_le hab] using hum
  rcases differentiable_max_selection (hr hum') (hw hum') (hm hum') with h | h
  · rw [h.2]
    exact hdr hum
  · rw [h.2]
    exact hdw hum (by rw [← h.1]; exact le_max_left _ _)

end OAI.SKFluctuations.LaplaceWindowFormalization
