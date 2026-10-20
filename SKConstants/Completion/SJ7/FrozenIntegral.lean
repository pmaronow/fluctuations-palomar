module

public import SKConstants.BrownianQuadraticVariation
public import SKConstants.BrownianDyadicGrid

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators

namespace SKConstants.Completion.SJ7

theorem frozen_integral_tendsto (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (T : ℝ≥0) (hg1 : ∀ s ∈ Icc (0 : ℝ) T, |g s| ≤ 1)
    (t : ℕ → ℕ → ℝ≥0) (n : ℕ → ℕ)
    (ht : ∀ l, Monotone (t l)) (ht0 : ∀ l, t l 0 = 0) (htT : ∀ l, t l (n l) = T)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hwidth : ∀ l k, k < n l → (t l (k + 1) : ℝ) - t l k ≤ δ l) :
    Tendsto (fun l => ∑ k ∈ Finset.range (n l), f (t l k) *
      ∫ s in (t l k : ℝ)..(t l (k + 1) : ℝ), g s) atTop
      (𝓝 (∫ s in (0 : ℝ)..T, f s * g s)) := by
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  let η := ε / ((T : ℝ) + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  have hu : UniformContinuousOn f (Icc (0 : ℝ) T) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨d, hd, hUC⟩ := Metric.uniformContinuousOn_iff.mp hu η hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hδ.eventually (eventually_lt_nhds hd))
  refine ⟨N, fun l hl => ?_⟩
  let a : ℕ → ℝ := fun k => t l k
  have ha (k : ℕ) : a k ≤ a (k + 1) := NNReal.coe_le_coe.mpr (ht l (Nat.le_succ k))
  have haT (k : ℕ) (hk : k ≤ n l) : a k ≤ T := by
    exact_mod_cast (ht l hk).trans_eq (htT l)
  have he : (∑ k ∈ Finset.range (n l), f (a k) * ∫ s in a k..a (k + 1), g s) -
      (∫ s in (0 : ℝ)..T, f s * g s) =
      ∑ k ∈ Finset.range (n l), ∫ s in a k..a (k + 1), (f (a k) - f s) * g s := by
    have hcell (k : ℕ) : (∫ s in a k..a (k + 1), (f (a k) - f s) * g s) =
        f (a k) * (∫ s in a k..a (k + 1), g s) -
          ∫ s in a k..a (k + 1), f s * g s := by
      simp_rw [sub_mul]
      rw [intervalIntegral.integral_sub (f := fun s => f (a k) * g s)
        (g := fun s => f s * g s) ((hg.intervalIntegrable _ _).const_mul _)
        ((hf.mul hg).intervalIntegrable _ _), intervalIntegral.integral_const_mul]
    simp_rw [hcell]
    rw [Finset.sum_sub_distrib, intervalIntegral.sum_integral_adjacent_intervals
      (f := fun s => f s * g s) (fun _ _ => (hf.mul hg).intervalIntegrable _ _)]
    simp only [a, ht0, htT, NNReal.coe_zero]
  have hb : |(∑ k ∈ Finset.range (n l), f (a k) * ∫ s in a k..a (k + 1), g s) -
      (∫ s in (0 : ℝ)..T, f s * g s)| ≤ η * (T : ℝ) := by
    rw [he]
    calc
      _ ≤ ∑ k ∈ Finset.range (n l),
          |∫ s in a k..a (k + 1), (f (a k) - f s) * g s| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (n l), η * (a (k + 1) - a k) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkn := Finset.mem_range.mp hk
        have hkT : a k ∈ Icc (0 : ℝ) T := ⟨(t l k).coe_nonneg, haT k hkn.le⟩
        have hnorm : ∀ s ∈ uIoc (a k) (a (k + 1)), ‖(f (a k) - f s) * g s‖ ≤ η := by
          intro s hs
          rw [uIoc_of_le (ha k)] at hs
          have hsT : s ∈ Icc (0 : ℝ) T := ⟨hkT.1.trans hs.1.le,
            hs.2.trans (haT (k + 1) (by omega))⟩
          have hdist : dist (a k) s < d := by
            rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hs.1.le)]
            exact (sub_le_sub_right hs.2 _).trans_lt ((hwidth l k hkn).trans_lt (hN l hl))
          have hfη : |f (a k) - f s| ≤ η :=
            (show |f (a k) - f s| < η by
              simpa only [Real.dist_eq] using hUC _ hkT _ hsT hdist).le
          rw [Real.norm_eq_abs, abs_mul]
          exact (mul_le_mul hfη (hg1 s hsT) (abs_nonneg _) hη.le).trans_eq (mul_one _)
        have h := intervalIntegral.norm_integral_le_of_norm_le_const hnorm
        simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (ha k))] using h
      _ = η * (T : ℝ) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub]
        simp only [a, ht0, htT, NNReal.coe_zero, sub_zero]
  rw [Real.dist_eq]
  apply hb.trans_lt
  dsimp only [η]
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ (by positivity : 0 < (T : ℝ) + 1)).mpr
  nlinarith

theorem frozen_integral_dyadic_tendsto (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (T : ℝ≥0) (hg1 : ∀ s ∈ Icc (0 : ℝ) T, |g s| ≤ 1) :
    Tendsto (fun l => ∑ k ∈ Finset.range (2 ^ l), f ((brownianDyadicGrid T).time l k) *
      ∫ s in ((brownianDyadicGrid T).time l k : ℝ)..
        ((brownianDyadicGrid T).time l (k + 1) : ℝ), g s) atTop
      (𝓝 (∫ s in (0 : ℝ)..T, f s * g s)) := by
  apply frozen_integral_tendsto f g hf hg T hg1 (brownianDyadicGrid T).time
    (fun l => 2 ^ l) (brownianDyadicGrid T).monotone (brownianDyadicGrid T).zero
    (fun l => by simp [brownianDyadicGrid]) (brownianDyadicWidth T) (brownianDyadicWidth_tendsto T)
  exact fun l k _ => brownianDyadicGrid_width_le T l k

end SKConstants.Completion.SJ7
