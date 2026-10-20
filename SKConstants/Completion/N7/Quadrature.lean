module

public import SKConstants.Completion.LBase.IntegratedQuadrature

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.N7

theorem left_integrated_quadrature_tendsto (f g : ℝ → ℝ) (hf : Continuous f)
    (hg : Continuous g) (hg1 : ∀ s, |g s| ≤ 1)
    (G : ScalarDyadicNestedGrid) (k : ℕ) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hwidth : ∀ l i, i < k * 2 ^ l → (G.time l (i + 1) : ℝ) - G.time l i ≤ δ l) :
    Tendsto (fun l => ∑ i ∈ Finset.range (k * 2 ^ l), f (G.time l i) *
      (∫ s in (G.time l i : ℝ)..(G.time l (i + 1) : ℝ), g s)) atTop
      (𝓝 (∫ s in (0 : ℝ)..(G.time 0 k : ℝ), f s * g s)) := by
  let T := G.time 0 k
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  let η := ε / ((T : ℝ) + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨d, hd, hUC⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn) η hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hδ.eventually (eventually_lt_nhds hd))
  refine ⟨N, fun l hl => ?_⟩
  let a : ℕ → ℝ := fun i => G.time l i
  have ha (i : ℕ) : a i ≤ a (i + 1) := by
    exact_mod_cast G.monotone l (Nat.le_succ i)
  have hcell (i : ℕ) (hi : i < k * 2 ^ l) :
      |f (a i) * (∫ s in a i..a (i + 1), g s) -
        (∫ s in a i..a (i + 1), f s * g s)| ≤ η * (a (i + 1) - a i) := by
    have he : f (a i) * (∫ s in a i..a (i + 1), g s) -
        (∫ s in a i..a (i + 1), f s * g s) =
        ∫ s in a i..a (i + 1), (f (a i) - f s) * g s := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
        (f := fun s => f (a i) * g s) (g := fun s => f s * g s)
        ((hg.const_mul _).intervalIntegrable _ _) ((hf.mul hg).intervalIntegrable _ _)]
      apply intervalIntegral.integral_congr
      intro s _
      ring
    rw [he]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a i) (b := a (i + 1)) (f := fun s => (f (a i) - f s) * g s)
      (C := η) (fun s hs => by
        rw [uIoc_of_le (ha i)] at hs
        have hai : a i ∈ Icc 0 (T : ℝ) :=
          ⟨NNReal.coe_nonneg _, by exact_mod_cast G.le_duration hi.le⟩
        have hai1 : a (i + 1) ≤ T := by
          exact_mod_cast G.le_duration (by omega : i + 1 ≤ k * 2 ^ l)
        have hsT : s ∈ Icc 0 (T : ℝ) := ⟨hai.1.trans hs.1.le, hs.2.trans hai1⟩
        have hdist : dist (a i) s < d := by
          rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hs.1.le)]
          exact (sub_le_sub_right hs.2 _).trans_lt ((hwidth l i hi).trans_lt (hN l hl))
        have hfs : |f (a i) - f s| ≤ η :=
          (show |f (a i) - f s| < η by
            simpa only [Real.dist_eq] using hUC _ hai _ hsT hdist).le
        rw [Real.norm_eq_abs, abs_mul]
        exact (mul_le_mul hfs (hg1 s) (abs_nonneg _) hη.le).trans_eq (mul_one η))
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (ha i))] using hb
  have he : (∑ i ∈ Finset.range (k * 2 ^ l), f (a i) *
      (∫ s in a i..a (i + 1), g s)) - (∫ s in (0 : ℝ)..T, f s * g s) =
      ∑ i ∈ Finset.range (k * 2 ^ l), (f (a i) * (∫ s in a i..a (i + 1), g s) -
        (∫ s in a i..a (i + 1), f s * g s)) := by
    rw [Finset.sum_sub_distrib, intervalIntegral.sum_integral_adjacent_intervals
      (a := a) (f := fun s => f s * g s)
      (fun i _ => (hf.mul hg).intervalIntegrable _ _)]
    simp only [a, G.zero, G.duration, NNReal.coe_zero, T]
  have hb : |(∑ i ∈ Finset.range (k * 2 ^ l), f (a i) *
      (∫ s in a i..a (i + 1), g s)) - (∫ s in (0 : ℝ)..T, f s * g s)| ≤ η * (T : ℝ) := by
    rw [he]
    calc
      _ ≤ ∑ i ∈ Finset.range (k * 2 ^ l), |f (a i) *
          (∫ s in a i..a (i + 1), g s) - (∫ s in a i..a (i + 1), f s * g s)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (k * 2 ^ l), η * (a (i + 1) - a i) :=
        Finset.sum_le_sum (fun i hi => hcell i (Finset.mem_range.mp hi))
      _ = η * (T : ℝ) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub]
        simp only [a, G.zero, G.duration, NNReal.coe_zero, sub_zero, T]
  rw [Real.dist_eq]
  apply hb.trans_lt
  dsimp only [η]
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ (by positivity : 0 < (T : ℝ) + 1)).mpr
  nlinarith

end SKConstants.Completion.N7
