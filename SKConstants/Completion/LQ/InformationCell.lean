module

public import SKConstants.Completion.LQ.GrowingMeshGeometry

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped NNReal BigOperators Interval
namespace SKConstants.Completion.LQ

lemma integral_time_offset (a b : ℝ) :
    (∫ v in a..b, (v - a)) = (b - a)^2 / 2 := by
  rw [intervalIntegral.integral_sub (f := fun v : ℝ => v) (g := fun _ : ℝ => a)
    (continuous_id.intervalIntegrable _ _)
    intervalIntegrable_const, integral_id, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

lemma information_cell_bounds (r k : ℝ → ℝ) (weight a b : ℝ) (hweight : 0 ≤ weight)
    (hab : a ≤ b)
    (hki : IntervalIntegrable k volume a b)
    (hrki : IntervalIntegrable (fun v => r v * k v) volume a b)
    (hr : ∀ v ∈ Icc a b, 0 ≤ r a - r v ∧ r a - r v ≤ 2 * r a * (v - a))
    (hk : ∀ v ∈ Icc a b, 0 ≤ k v ∧ k v ≤ 1) :
    0 ≤ (weight / 2) * (r a * (∫ v in a..b, k v) - ∫ v in a..b, r v * k v) ∧
      (weight / 2) * (r a * (∫ v in a..b, k v) - ∫ v in a..b, r v * k v) ≤
        (weight / 2) * r a * (b - a)^2 := by
  have heq : r a * (∫ v in a..b, k v) - (∫ v in a..b, r v * k v) =
      ∫ v in a..b, (r a - r v) * k v := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hki.const_mul (r a)) hrki]
    congr 1
    funext v
    ring
  rw [heq]
  constructor
  · exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hab
      (fun v hv => mul_nonneg (hr v hv).1 (hk v hv).1))
  · have hbnd : (∫ v in a..b, (r a - r v) * k v) ≤
        ∫ v in a..b, 2 * r a * (v - a) := by
      apply intervalIntegral.integral_mono_on hab
        (by convert (hki.const_mul (r a)).sub hrki using 1; ext v; ring)
        (((continuous_id.sub continuous_const).const_mul (2 * r a)).intervalIntegrable a b)
      intro v hv
      calc
        _ ≤ r a - r v := by nlinarith [(hr v hv).1, (hk v hv).2]
        _ ≤ _ := (hr v hv).2
    rw [intervalIntegral.integral_const_mul, integral_time_offset] at hbnd
    calc
      _ ≤ (weight / 2) * (2 * r a * ((b - a)^2 / 2)) :=
        mul_le_mul_of_nonneg_left hbnd (by positivity)
      _ = _ := by ring

lemma intervalIntegrable_meshCell {f : ℝ → ℝ} {δ : ℝ≥0} {K i : ℕ}
    (hf : IntervalIntegrable f volume 0 (meshTime δ K)) (hi : i < K) :
    IntervalIntegrable f volume (meshTime δ i) (meshTime δ (i + 1)) := by
  apply hf.mono_set
  rw [uIcc_of_le (meshTime_mono δ (Nat.le_succ i)), uIcc_of_le (meshTime_nonneg δ K)]
  exact Icc_subset_Icc (meshTime_nonneg δ i) (meshTime_mono δ (by omega))

lemma mesh_integral_split {f : ℝ → ℝ} (δ : ℝ≥0) (q : ℕ)
    (hf : IntervalIntegrable f volume 0 (meshTime δ (q + 1))) :
    (∫ v in 0..meshTime δ (q + 1), f v) =
      (∫ v in 0..(δ : ℝ), f v) +
        ∑ i ∈ Finset.range q, ∫ v in meshTime δ (i + 1)..meshTime δ (i + 2), f v := by
  have hs := intervalIntegral.sum_integral_adjacent_intervals
    (a := meshTime δ) (n := q + 1)
    (fun i hi => intervalIntegrable_meshCell hf hi)
  rw [meshTime_zero] at hs
  rw [← hs, Finset.sum_range_succ']
  simp only [Nat.zero_add, Nat.reduceAdd, meshTime_zero, meshTime_one, Nat.add_assoc]
  ring

end SKConstants.Completion.LQ
