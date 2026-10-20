module

public import SKConstants.BrownianQuadraticVariation

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal Topology BigOperators
namespace SKConstants.Completion.LBase
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

lemma integrated_product_cell_error (f : ℝ → ℝ) (hf : Continuous f)
    (hf1 : ∀ s, |f s| ≤ 1) {a b η : ℝ} (hab : a ≤ b)
    (hη : ∀ s ∈ Icc a b, |f a - f s| ≤ η) :
    |f a * (∫ s in a..b, f s) - (∫ s in a..b, (f s)^2)| ≤ η * (b - a) := by
  have he : f a * (∫ s in a..b, f s) - (∫ s in a..b, (f s)^2) =
      ∫ s in a..b, (f a - f s) * f s := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      (f := fun s => f a * f s) (g := fun s => (f s)^2)
      ((hf.const_mul _).intervalIntegrable a b) ((hf.pow 2).intervalIntegrable a b)]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  rw [he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun s => (f a - f s) * f s) (C := η) (fun s hs => by
      rw [uIoc_of_le hab] at hs
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (hη s ⟨hs.1.le, hs.2⟩) (hf1 s) (abs_nonneg _) 
        ((abs_nonneg (f a - f s)).trans (hη s ⟨hs.1.le, hs.2⟩))).trans_eq (mul_one η))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using hb

theorem integrated_product_quadrature_tendsto (f : ℝ → ℝ) (hf : Continuous f)
    (hf1 : ∀ s, |f s| ≤ 1) (G : ScalarDyadicNestedGrid) (k : ℕ)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hwidth : ∀ l i, i < k * 2^l → (G.time l (i+1) : ℝ) - G.time l i ≤ δ l) :
    Tendsto (fun l => ∑ i ∈ Finset.range (k * 2^l), f (G.time l i) *
      (∫ s in (G.time l i : ℝ)..(G.time l (i+1) : ℝ), f s)) atTop
      (𝓝 (∫ s in (0 : ℝ)..(G.time 0 k : ℝ), (f s)^2)) := by
  let T := G.time 0 k
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  let η := ε / ((T : ℝ) + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  have hu : UniformContinuousOn f (Icc 0 (T : ℝ)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨d, hd, hUC⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hδ.eventually (eventually_lt_nhds hd))
  refine ⟨N, fun l hl => ?_⟩
  let a : ℕ → ℝ := fun i => G.time l i
  have ha (i : ℕ) : a i ≤ a (i+1) := by exact_mod_cast G.monotone l (by omega : i ≤ i+1)
  have he : (∑ i ∈ Finset.range (k * 2^l), f (a i) * (∫ s in a i..a (i+1), f s)) -
      (∫ s in (0 : ℝ)..T, (f s)^2) = ∑ i ∈ Finset.range (k * 2^l),
        (f (a i) * (∫ s in a i..a (i+1), f s) - (∫ s in a i..a (i+1), (f s)^2)) := by
    rw [Finset.sum_sub_distrib, intervalIntegral.sum_integral_adjacent_intervals
      (a := a) (f := fun s => (f s)^2)
      (fun i hi => (hf.pow 2).intervalIntegrable _ _)]
    simp only [a, G.zero, G.duration, NNReal.coe_zero, T]
  have hb : |(∑ i ∈ Finset.range (k * 2^l), f (a i) * (∫ s in a i..a (i+1), f s)) -
      (∫ s in (0 : ℝ)..T, (f s)^2)| ≤ η * (T : ℝ) := by
    rw [he]
    calc
      _ ≤ ∑ i ∈ Finset.range (k * 2^l),
          |f (a i) * (∫ s in a i..a (i+1), f s) - (∫ s in a i..a (i+1), (f s)^2)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (k * 2^l), η * (a (i+1) - a i) := by
        apply Finset.sum_le_sum
        intro i hi
        apply integrated_product_cell_error f hf hf1 (ha i)
        intro s hs
        have hiN := Finset.mem_range.mp hi
        have hai : a i ∈ Icc 0 (T : ℝ) :=
          ⟨NNReal.coe_nonneg _, by exact_mod_cast G.le_duration hiN.le⟩
        have hai1 : a (i+1) ≤ T := by
          exact_mod_cast G.le_duration (by omega : i+1 ≤ k * 2^l)
        have hsT : s ∈ Icc 0 (T : ℝ) := ⟨hai.1.trans hs.1, hs.2.trans hai1⟩
        have hdist : dist (a i) s < d := by
          rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hs.1)]
          exact (sub_le_sub_right hs.2 _).trans_lt ((hwidth l i hiN).trans_lt (hN l hl))
        exact (show |f (a i) - f s| < η by
          simpa only [Real.dist_eq] using hUC _ hai _ hsT hdist).le
      _ = η * (T : ℝ) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub]
        simp only [a, G.zero, G.duration, NNReal.coe_zero, sub_zero, T]
  have hηT : η * (T : ℝ) < ε := by
    dsimp only [η]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < (T : ℝ) + 1)).mpr
    nlinarith
  rw [Real.dist_eq]
  exact hb.trans_lt hηT

end SKConstants.Completion.LBase
