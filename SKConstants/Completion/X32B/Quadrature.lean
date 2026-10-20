module

public import SKConstants.Completion.J3B.Node
public import SKConstants.Completion.S32bA.Node
public import SKConstants.Completion.S32bB.Node

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.X32B
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.WeakIto

variable {Ω : Type*} [MeasurableSpace Ω]

def leftIntegralError (F G : ℝ → Ω → ℝ) (V : ℝ≥0) (l : ℕ) (w : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2 ^ l),
    ∫ s in ((brownianDyadicGrid V).time l k : ℝ)..
      ((brownianDyadicGrid V).time l (k + 1) : ℝ),
      (F ((brownianDyadicGrid V).time l k) w - F s w) * G s w

omit [MeasurableSpace Ω] in
theorem leftIntegralError_tendsto (F G : ℝ → Ω → ℝ) (V : ℝ≥0) (w : Ω)
    (hF : Continuous (fun s => F s w)) (D : ℝ) (hD : 0 ≤ D)
    (hG : ∀ s, |G s w| ≤ D) :
    Tendsto (fun l => leftIntegralError F G V l w) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  let η := ε / (D * (V : ℝ) + 1)
  have hDV : 0 ≤ D * (V : ℝ) := mul_nonneg hD V.coe_nonneg
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨r, hr, hUC⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hF.continuousOn
      (s := Icc (0 : ℝ) V)) η hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((brownianDyadicWidth_tendsto V).eventually (eventually_lt_nhds hr))
  refine ⟨N, fun l hl => ?_⟩
  let t : ℕ → ℝ := fun k => (brownianDyadicGrid V).time l k
  have htn : t (2 ^ l) = V := by simp [t, brownianDyadicGrid]
  have ht0 : t 0 = 0 := by simp [t, brownianDyadicGrid]
  have ht : Monotone t := fun i j hij =>
    NNReal.coe_le_coe.mpr ((brownianDyadicGrid V).monotone l hij)
  have hb := J3B.cellIntegralSum_bound t ht (2 ^ l)
    (fun k s => (F (t k) w - F s w) * G s w) (η * D) (by
      intro k hk s hs
      have htV : t (k + 1) ≤ V := (ht (show k + 1 ≤ 2 ^ l by omega)).trans_eq htn
      have hk0 : 0 ≤ t k := NNReal.coe_nonneg _
      have hs0 : 0 ≤ s := hk0.trans hs.1
      have hdist : dist (t k) s < r := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hs.1)]
        exact (sub_le_sub_right hs.2 _).trans_lt
          (by simpa only [t, S32bB.dyadic_step_eq_width] using hN l hl)
      have hdiff : |F (t k) w - F s w| ≤ η :=
        (show |F (t k) w - F s w| < η from by
          simpa only [Real.dist_eq] using
            hUC _ ⟨hk0, (ht (Nat.le_succ k)).trans htV⟩
              _ ⟨hs0, hs.2.trans htV⟩ hdist).le
      rw [abs_mul]
      exact mul_le_mul hdiff (hG s) (abs_nonneg _) hη.le)
  rw [htn, ht0, sub_zero] at hb
  rw [Real.dist_eq, sub_zero]
  apply hb.trans_lt
  have he : η * D * (V : ℝ) = (D * (V : ℝ) * ε) / (D * (V : ℝ) + 1) := by
    dsimp only [η]
    ring
  rw [he]
  apply (div_lt_iff₀ (by positivity : 0 < D * (V : ℝ) + 1)).mpr
  nlinarith

omit [MeasurableSpace Ω] in
theorem leftIntegralError_bound (F G : ℝ → Ω → ℝ) (V : ℝ≥0) (l : ℕ) (w : Ω)
    (C D : ℝ) (hF : ∀ s, |F s w| ≤ C) (hG : ∀ s, |G s w| ≤ D) :
    |leftIntegralError F G V l w| ≤ 2 * C * D * V := by
  have hb := J3B.cellIntegralSum_bound
    (fun k => ((brownianDyadicGrid V).time l k : ℝ))
    (fun i j hij => NNReal.coe_le_coe.mpr ((brownianDyadicGrid V).monotone l hij))
    (2 ^ l) (fun k s => (F ((brownianDyadicGrid V).time l k) w - F s w) * G s w)
    (2 * C * D) (by
      intro k _ s _
      rw [abs_mul]
      apply mul_le_mul _ (hG s) (abs_nonneg _) (by nlinarith [hF s, abs_nonneg (F s w)])
      exact (abs_sub _ _).trans (by linarith [hF ((brownianDyadicGrid V).time l k), hF s]))
  simpa only [leftIntegralError, S32bB.dyadic_end, (brownianDyadicGrid V).zero l,
    NNReal.coe_zero, sub_zero] using hb

theorem measurable_leftIntegralError (F G : ℝ → Ω → ℝ)
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    (V : ℝ≥0) (l : ℕ) : Measurable (leftIntegralError F G V l) := by
  apply Finset.measurable_sum
  intro k _
  apply measurable_time_integral
  exact ((hF.comp (measurable_const.prodMk measurable_snd)).sub hF).mul hG

omit [MeasurableSpace Ω] in
theorem leftIntegralError_eq (F G : ℝ → Ω → ℝ) (V : ℝ≥0) (l : ℕ) (w : Ω)
    (hG : ∀ a b, IntervalIntegrable (fun s => G s w) volume a b)
    (hFG : ∀ a b, IntervalIntegrable (fun s => F s w * G s w) volume a b) :
    leftIntegralError F G V l w =
      (∑ k ∈ Finset.range (2 ^ l),
        F ((brownianDyadicGrid V).time l k) w *
          ∫ s in ((brownianDyadicGrid V).time l k : ℝ)..
            ((brownianDyadicGrid V).time l (k + 1) : ℝ), G s w) -
      ∫ s in (0 : ℝ)..V, F s w * G s w := by
  unfold leftIntegralError
  simp_rw [sub_mul, intervalIntegral.integral_sub
    ((hG _ _).const_mul _) (hFG _ _), intervalIntegral.integral_const_mul]
  rw [Finset.sum_sub_distrib, intervalIntegral.sum_integral_adjacent_intervals
    (fun k _ => hFG _ _)]
  simp only [S32bB.dyadic_end, (brownianDyadicGrid V).zero l, NNReal.coe_zero]

theorem leftIntegralError_tendsto_L2 (μ : Measure Ω) [IsFiniteMeasure μ]
    (F G : ℝ → Ω → ℝ)
    (hFm : Measurable (Function.uncurry F)) (hGm : Measurable (Function.uncurry G))
    (hFc : ∀ᵐ w ∂μ, Continuous (fun s => F s w))
    (C D : ℝ) (hD : 0 ≤ D)
    (hF : ∀ s w, |F s w| ≤ C) (hG : ∀ s w, |G s w| ≤ D) (V : ℝ≥0) :
    J3B.VanishingMeanSquare μ (leftIntegralError F G V) := by
  have hb (l : ℕ) (w : Ω) : ‖leftIntegralError F G V l w ^ 2‖ ≤
      (2 * C * D * (V : ℝ)) ^ 2 := by
    simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) (leftIntegralError_bound F G V l w C D
        (fun s => hF s w) (fun s => hG s w)) 2
  have hm (l : ℕ) : AEStronglyMeasurable (fun w => leftIntegralError F G V l w ^ 2) μ :=
    ((measurable_leftIntegralError F G hFm hGm V l).pow_const 2).aestronglyMeasurable
  refine ⟨fun l => Integrable.of_bound (hm l) _ (ae_of_all _ (hb l)), ?_⟩
  have H := tendsto_integral_of_dominated_convergence (μ := μ)
    (bound := fun _ => (2 * C * D * (V : ℝ)) ^ 2) hm (integrable_const _)
    (fun l => ae_of_all _ (hb l)) (by
      filter_upwards [hFc] with w hw
      simpa only [zero_pow (by decide : 2 ≠ 0)] using
        (leftIntegralError_tendsto F G V w hw D hD (fun s => hG s w)).pow 2)
  simpa only [integral_zero] using H

end SKConstants.Completion.X32B
