module

public import SKConstants.Completion.J3B.PhysicalTime

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.J3B
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.WeakIto SKConstantsOAI.SK.Analytic
variable {Ω : Type*} [MeasurableSpace Ω]

attribute [local irreducible] actualParisiFullMagnetization actualParisiFullCurvature
  actualParisiFullScalarDrift BoundedLipschitzDrift.solution

theorem cellIntegralSum_bound (t : ℕ → ℝ) (ht : Monotone t) (N : ℕ)
    (F : ℕ → ℝ → ℝ) (C : ℝ)
    (hF : ∀ i < N, ∀ s ∈ Icc (t i) (t (i + 1)), |F i s| ≤ C) :
    |∑ i ∈ Finset.range N, ∫ s in t i..t (i + 1), F i s| ≤ C * (t N - t 0) := by
  calc
    _ ≤ ∑ i ∈ Finset.range N, |∫ s in t i..t (i + 1), F i s| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range N, C * (t (i + 1) - t i) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := t i) (b := t (i + 1)) (f := F i) (C := C) (fun s hs => by
          rw [uIoc_of_le (ht (Nat.le_succ i))] at hs
          simpa only [Real.norm_eq_abs] using hF i (Finset.mem_range.mp hi) s ⟨hs.1.le, hs.2⟩)
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (ht (Nat.le_succ i)))] using h
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_range_sub]

def timeTransportSum (d : ℝ → ℝ → ℝ) (V : ℝ≥0) (l : ℕ) (Y : ℝ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range (2 ^ l),
    ∫ s in ((brownianDyadicGrid V).time l i : ℝ)..((brownianDyadicGrid V).time l (i + 1) : ℝ),
      d s (Y ((brownianDyadicGrid V).time l (i + 1))) - d s (Y s)

theorem timeTransportSum_bound (d : ℝ → ℝ → ℝ) (D : ℝ)
    (hd : ∀ s y, |d s y| ≤ D) (V : ℝ≥0) (l : ℕ) (Y : ℝ → ℝ) :
    |timeTransportSum d V l Y| ≤ 2 * D * V := by
  have h := cellIntegralSum_bound (fun i => ((brownianDyadicGrid V).time l i : ℝ))
    (fun i j hij => NNReal.coe_le_coe.mpr ((brownianDyadicGrid V).monotone l hij)) (2 ^ l)
    (fun i s => d s (Y ((brownianDyadicGrid V).time l (i + 1))) - d s (Y s)) (2 * D)
    (fun i _ s _ => (abs_sub _ _).trans (by linarith [hd s (Y ((brownianDyadicGrid V).time l (i + 1))), hd s (Y s)]))
  simpa only [timeTransportSum, brownianDyadicGrid_time_coe, Nat.cast_pow, Nat.cast_ofNat,
    mul_div_cancel_right₀ _ (pow_ne_zero l (by norm_num : (2 : ℝ) ≠ 0)),
    Nat.cast_zero, mul_zero, zero_div, sub_zero] using h

theorem timeTransportSum_tendsto (d : ℝ → ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hd : ∀ s y z, |d s y - d s z| ≤ L * |y - z|)
    (V : ℝ≥0) (Y : ℝ → ℝ) (hY : Continuous Y) :
    Tendsto (fun l => timeTransportSum d V l Y) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
  let η := ε / (L * (V : ℝ) + 1)
  have hLV : 0 ≤ L * (V : ℝ) := mul_nonneg hL V.coe_nonneg
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨r, hr, hUC⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hY.continuousOn (s := Icc (0 : ℝ) V)) η hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((brownianDyadicWidth_tendsto V).eventually (eventually_lt_nhds hr))
  refine ⟨N, fun l hl => ?_⟩
  let t : ℕ → ℝ := fun i => (brownianDyadicGrid V).time l i
  have htn : t (2 ^ l) = V := by simp [t, brownianDyadicGrid]
  have ht0 : t 0 = 0 := by simp [t, brownianDyadicGrid]
  have ht : Monotone t := fun i j hij => NNReal.coe_le_coe.mpr ((brownianDyadicGrid V).monotone l hij)
  have hbound := cellIntegralSum_bound t ht (2 ^ l)
    (fun i s => d s (Y (t (i + 1))) - d s (Y s)) (L * η) (by
      intro i hi s hs
      have hiN : i + 1 ≤ 2 ^ l := by omega
      have htV : t (i + 1) ≤ V := (ht hiN).trans_eq htn
      have htpos : 0 ≤ t (i + 1) := NNReal.coe_nonneg _
      have hspos : 0 ≤ s := (NNReal.coe_nonneg ((brownianDyadicGrid V).time l i)).trans hs.1
      have hdist : dist (t (i + 1)) s < r := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.2)]
        exact (sub_le_sub_left hs.1 _).trans_lt
          ((by simpa only [t, dyadic_cell_width] using hN l hl) : t (i + 1) - t i < r)
      have hy : |Y (t (i + 1)) - Y s| ≤ η :=
        (show |Y (t (i + 1)) - Y s| < η from by
          simpa only [Real.dist_eq] using hUC _ ⟨htpos, htV⟩ _ ⟨hspos, hs.2.trans htV⟩ hdist).le
      exact (hd s _ _).trans (mul_le_mul_of_nonneg_left hy hL))
  rw [htn, ht0, sub_zero] at hbound
  rw [Real.dist_eq, sub_zero]
  apply hbound.trans_lt
  have he : L * η * (V : ℝ) = (L * (V : ℝ) * ε) / (L * (V : ℝ) + 1) := by
    dsimp only [η]
    ring
  rw [he]
  apply (div_lt_iff₀ (by positivity : 0 < L * (V : ℝ) + 1)).mpr
  nlinarith

theorem measurable_physicalValueRate (β : ℝ) :
    Measurable (fun p : ℝ × ℝ => physicalValueRate β p.1 p.2) := by
  have hm := (continuous_actualParisiFullMagnetization β).measurable
  have ha := (continuous_actualParisiFullCurvature β).measurable
  have hα : Measurable (fun p : ℝ × ℝ => cdf (parisiEquilibriumMeasure β : Measure ℝ) (p.1 / β ^ 2)) :=
    (cdf (parisiEquilibriumMeasure β : Measure ℝ)).mono.measurable.comp
    (measurable_fst.div_const (β ^ 2))
  exact (ha.add (hα.mul (hm.pow_const 2))).neg.div_const 2

attribute [local irreducible] physicalValueRate

theorem measurable_actualScalar_real (W : BrownianSystem Ω) (β : ℝ) :
    Measurable (fun p : ℝ × Ω => actualParisiFullScalarProcess W β p.1.toNNReal p.2) := by
  unfold actualParisiFullScalarProcess
  have h := progressive_joint_measurable _
    ((actualParisiFullScalarDrift β).solution_progressive _ W.driver_progressive)
  exact h.comp ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)

def actualTimeTransport (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) (l : ℕ) (w : Ω) : ℝ :=
  timeTransportSum (physicalValueRate β) V l
    (fun s => actualParisiFullScalarProcess W β s.toNNReal w)

theorem measurable_actualTimeTransport (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) (l : ℕ) :
    Measurable (actualTimeTransport W β V l) := by
  unfold actualTimeTransport timeTransportSum
  apply Finset.measurable_sum
  intro i _
  apply measurable_time_integral
  have hfixed : Measurable (fun p : ℝ × Ω => actualParisiFullScalarProcess W β
      ((brownianDyadicGrid V).time l (i + 1)) p.2) :=
    ((actualParisiFullScalarDrift β).solution_measurable W _).comp measurable_snd
  simpa only [Real.toNNReal_coe, Function.comp_def, Pi.sub_def] using
    ((measurable_physicalValueRate β).comp (measurable_fst.prodMk hfixed)).sub
      ((measurable_physicalValueRate β).comp
        (measurable_fst.prodMk (measurable_actualScalar_real W β)))

theorem actualTimeTransport_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) :
    (∀ l, Integrable (fun w => actualTimeTransport W β V l w ^ 2) W.law) ∧
      Tendsto (fun l => ∫ w, actualTimeTransport W β V l w ^ 2 ∂W.law) atTop (𝓝 0) := by
  let := W.isProbability
  have hbound (l : ℕ) (w : Ω) : ‖actualTimeTransport W β V l w ^ 2‖ ≤ (V : ℝ) ^ 2 := by
    have h := timeTransportSum_bound (physicalValueRate β) (1 / 2) (physicalValueRate_abs_le β) V l
      (fun s => actualParisiFullScalarProcess W β s.toNNReal w)
    norm_num at h
    simpa only [actualTimeTransport, Real.norm_eq_abs, abs_pow, sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) h 2
  have hi (l : ℕ) : Integrable (fun w => actualTimeTransport W β V l w ^ 2) W.law :=
    Integrable.of_bound ((measurable_actualTimeTransport W β V l).pow_const 2).aestronglyMeasurable
      ((V : ℝ) ^ 2) (ae_of_all _ (hbound l))
  refine ⟨hi, ?_⟩
  have hpath : ∀ᵐ w ∂W.law,
      Tendsto (fun l => actualTimeTransport W β V l w) atTop (𝓝 0) := by
    filter_upwards [(actualParisiFullScalarDrift β).solution_continuous_ae W] with w hw
    exact timeTransportSum_tendsto _ _ (by positivity)
      (physicalValueRate_spatial_bound β) V _ (hw.comp continuous_real_toNNReal)
  have hlim := tendsto_integral_of_dominated_convergence (μ := W.law)
    (bound := fun _ => (V : ℝ) ^ 2)
    (fun l => ((measurable_actualTimeTransport W β V l).pow_const 2).aestronglyMeasurable)
    (integrable_const _) (fun l => ae_of_all _ (hbound l)) (by
      filter_upwards [hpath] with w hw
      simpa only [zero_pow (by decide : 2 ≠ 0)] using hw.pow 2)
  simpa only [integral_zero] using hlim

theorem physicalValueRate_intervalIntegrable (β y a b : ℝ) :
    IntervalIntegrable (fun s => physicalValueRate β s y) volume a b := by
  apply (intervalIntegrable_const (c := (1 / 2 : ℝ))).mono_fun
    (((measurable_physicalValueRate β).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  exact ae_of_all _ (fun s => by
    simpa only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), Function.comp_def, id_eq] using
      physicalValueRate_abs_le β s y)

theorem physicalValueRate_path_intervalIntegrable (W : BrownianSystem Ω) (β : ℝ)
    (w : Ω) (a b : ℝ) :
    IntervalIntegrable (fun s => physicalValueRate β s
      (actualParisiFullScalarProcess W β s.toNNReal w)) volume a b := by
  have hY : Measurable (fun s : ℝ => actualParisiFullScalarProcess W β s.toNNReal w) :=
    (measurable_actualScalar_real W β).comp (measurable_id.prodMk measurable_const)
  apply (intervalIntegrable_const (c := (1 / 2 : ℝ))).mono_fun
    (((measurable_physicalValueRate β).comp (measurable_id.prodMk hY)).aestronglyMeasurable)
  exact ae_of_all _ (fun s => by
    simpa only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), Function.comp_def, id_eq] using
      physicalValueRate_abs_le β s (actualParisiFullScalarProcess W β s.toNNReal w))

theorem actual_time_increments_eq_transport (W : BrownianSystem Ω) (β : ℝ) (hβ : β ≠ 0)
    (V : ℝ≥0) (hV : (V : ℝ) < β ^ 2) (l : ℕ) (w : Ω) :
    (∑ i ∈ Finset.range (2 ^ l),
      (parisiPhysicalValue β (parisiEquilibriumMeasure β)
          ((brownianDyadicGrid V).time l (i + 1))
          (actualParisiFullScalarProcess W β ((brownianDyadicGrid V).time l (i + 1)) w) -
        parisiPhysicalValue β (parisiEquilibriumMeasure β) ((brownianDyadicGrid V).time l i)
          (actualParisiFullScalarProcess W β ((brownianDyadicGrid V).time l (i + 1)) w))) =
      (∫ s in (0 : ℝ)..V, physicalValueRate β s
        (actualParisiFullScalarProcess W β s.toNNReal w)) + actualTimeTransport W β V l w := by
  let t := (brownianDyadicGrid V).time l
  let Y : ℝ → ℝ := fun s => actualParisiFullScalarProcess W β s.toNNReal w
  have htn : t (2 ^ l) = V := by simp [t, brownianDyadicGrid]
  have ht0 : t 0 = 0 := by simp [t, brownianDyadicGrid]
  have hcell (i : ℕ) (hi : i ∈ Finset.range (2 ^ l)) :
      parisiPhysicalValue β (parisiEquilibriumMeasure β) (t (i + 1)) (Y (t (i + 1))) -
        parisiPhysicalValue β (parisiEquilibriumMeasure β) (t i) (Y (t (i + 1))) =
          ∫ s in (t i : ℝ)..(t (i + 1) : ℝ), physicalValueRate β s (Y (t (i + 1))) := by
    apply physicalValue_integral_time_equation β hβ _ _ (t i).coe_nonneg
      (NNReal.coe_le_coe.mpr ((brownianDyadicGrid V).monotone l (Nat.le_succ i)))
    have hle := (brownianDyadicGrid V).monotone l
      (show i + 1 ≤ 2 ^ l by exact Nat.succ_le_of_lt (Finset.mem_range.mp hi))
    exact (NNReal.coe_le_coe.mpr (hle.trans_eq htn)).trans_lt hV
  have hsum : (∑ i ∈ Finset.range (2 ^ l), ∫ s in (t i : ℝ)..(t (i + 1) : ℝ),
      physicalValueRate β s (Y s)) = ∫ s in (0 : ℝ)..V, physicalValueRate β s (Y s) := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun s => physicalValueRate β s (Y s)) (a := fun i => (t i : ℝ))
      (n := 2 ^ l) (fun i _ => physicalValueRate_path_intervalIntegrable W β w _ _)
    simpa only [htn, ht0, NNReal.coe_zero] using h
  have hdiff : actualTimeTransport W β V l w =
      (∑ i ∈ Finset.range (2 ^ l), ∫ s in (t i : ℝ)..(t (i + 1) : ℝ),
        physicalValueRate β s (Y (t (i + 1)))) -
      ∫ s in (0 : ℝ)..V, physicalValueRate β s (Y s) := by
    unfold actualTimeTransport timeTransportSum
    simp_rw [intervalIntegral.integral_sub
      (physicalValueRate_intervalIntegrable β _ _ _)
      (physicalValueRate_path_intervalIntegrable W β w _ _)]
    simpa only [Finset.sum_sub_distrib, t, Y] using
      congrArg (fun z : ℝ =>
        (∑ i ∈ Finset.range (2 ^ l), ∫ s in (t i : ℝ)..(t (i + 1) : ℝ),
          physicalValueRate β s (Y (t (i + 1)))) - z) hsum
  have hleft : (∑ i ∈ Finset.range (2 ^ l),
      (parisiPhysicalValue β (parisiEquilibriumMeasure β) (t (i + 1)) (Y (t (i + 1))) -
        parisiPhysicalValue β (parisiEquilibriumMeasure β) (t i) (Y (t (i + 1))))) =
      ∑ i ∈ Finset.range (2 ^ l), ∫ s in (t i : ℝ)..(t (i + 1) : ℝ),
        physicalValueRate β s (Y (t (i + 1))) := Finset.sum_congr rfl hcell
  simp only [Y, Real.toNNReal_coe, t] at hleft
  rw [hleft, hdiff]
  simp only [Y, t, Real.toNNReal_coe]
  ring

def potentialTaylorError (W : BrownianSystem Ω) (β : ℝ) (V : ℝ≥0) (l : ℕ) (w : Ω) : ℝ :=
  parisiPhysicalValue β (parisiEquilibriumMeasure β) V (actualParisiFullScalarProcess W β V w) -
    parisiPhysicalValue β (parisiEquilibriumMeasure β) 0 (actualParisiFullScalarProcess W β 0 w) -
    (∑ i ∈ Finset.range (2 ^ l),
      (actualParisiFullMagnetization β ((brownianDyadicGrid V).time l i)
          (actualParisiFullScalarProcess W β ((brownianDyadicGrid V).time l i) w) *
          (actualParisiFullScalarProcess W β ((brownianDyadicGrid V).time l (i + 1)) w -
            actualParisiFullScalarProcess W β ((brownianDyadicGrid V).time l i) w) +
        actualParisiFullCurvature β ((brownianDyadicGrid V).time l i)
          (actualParisiFullScalarProcess W β ((brownianDyadicGrid V).time l i) w) *
          (actualParisiFullScalarProcess W β ((brownianDyadicGrid V).time l (i + 1)) w -
            actualParisiFullScalarProcess W β ((brownianDyadicGrid V).time l i) w) ^ 2 / 2)) -
    ∫ s in (0 : ℝ)..V, physicalValueRate β s (actualParisiFullScalarProcess W β s.toNNReal w)

theorem potentialTaylorError_eq (W : BrownianSystem Ω) (β : ℝ) (hβ : β ≠ 0)
    (V : ℝ≥0) (hV : (V : ℝ) < β ^ 2) (l : ℕ) (w : Ω) :
    potentialTaylorError W β V l w =
      dyadicSpatialRemainder W β V l w + actualTimeTransport W β V l w := by
  have h := time_space_telescope (parisiPhysicalValue β (parisiEquilibriumMeasure β))
    (actualParisiFullMagnetization β) (actualParisiFullCurvature β)
    (fun i => ((brownianDyadicGrid V).time l i : ℝ))
    (fun i => actualParisiFullScalarProcess W β ((brownianDyadicGrid V).time l i) w) (2 ^ l)
  have ht := actual_time_increments_eq_transport W β hβ V hV l w
  have htn : (brownianDyadicGrid V).time l (2 ^ l) = V := by simp [brownianDyadicGrid]
  simp only [Finset.sum_add_distrib, htn, (brownianDyadicGrid V).zero l, NNReal.coe_zero] at h
  rw [ht] at h
  have hs : (∑ i ∈ Finset.range (2 ^ l),
      spatialRemainder (parisiPhysicalValue β (parisiEquilibriumMeasure β))
        (actualParisiFullMagnetization β) (actualParisiFullCurvature β)
        ((brownianDyadicGrid V).time l i)
        (actualParisiFullScalarProcess W β ((brownianDyadicGrid V).time l i) w)
        (actualParisiFullScalarProcess W β ((brownianDyadicGrid V).time l (i + 1)) w)) =
      dyadicSpatialRemainder W β V l w := rfl
  rw [hs] at h
  unfold potentialTaylorError
  rw [Finset.sum_add_distrib]
  linarith

theorem measurable_dyadicSpatialRemainder (W : BrownianSystem Ω) (β : ℝ) (hβ : β ≠ 0)
    (V : ℝ≥0) (hV : (V : ℝ) < β ^ 2) (l : ℕ) :
    Measurable (dyadicSpatialRemainder W β V l) := by
  unfold dyadicSpatialRemainder
  apply Finset.measurable_sum
  intro i hi
  apply measurable_spatialCellRemainder W β hβ
  have hle := (brownianDyadicGrid V).monotone l (Finset.mem_range.mp hi).le
  have htn : (brownianDyadicGrid V).time l (2 ^ l) = V := by simp [brownianDyadicGrid]
  exact (NNReal.coe_le_coe.mpr (hle.trans_eq htn)).trans_lt hV

theorem potentialTaylorError_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (hβ : β ≠ 0)
    (V : ℝ≥0) (hV : (V : ℝ) < β ^ 2) :
    (∀ l, Integrable (fun w => potentialTaylorError W β V l w ^ 2) W.law) ∧
      Tendsto (fun l => ∫ w, potentialTaylorError W β V l w ^ 2 ∂W.law) atTop (𝓝 0) := by
  let R := dyadicSpatialRemainder W β V
  let T := actualTimeTransport W β V
  have hR (l : ℕ) : MemLp (R l) 2 W.law :=
    (memLp_two_iff_integrable_sq (measurable_dyadicSpatialRemainder W β hβ V hV l).aestronglyMeasurable).mpr
      (dyadicSpatialRemainder_meanSquare_le W β hβ V hV l).1
  have hT (l : ℕ) : MemLp (T l) 2 W.law :=
    (memLp_two_iff_integrable_sq (measurable_actualTimeTransport W β V l).aestronglyMeasurable).mpr
      ((actualTimeTransport_tendsto_L2 W β V).1 l)
  have hi (l : ℕ) : Integrable (fun w => potentialTaylorError W β V l w ^ 2) W.law := by
    simpa only [potentialTaylorError_eq W β hβ V hV l, Pi.add_apply, R, T] using ((hR l).add (hT l)).integrable_sq
  refine ⟨hi, ?_⟩
  have hlim := ((dyadicSpatialRemainder_tendsto_L2 W β hβ V hV).const_mul 2).add
    ((actualTimeTransport_tendsto_L2 W β V).2.const_mul 2)
  apply squeeze_zero (fun l => integral_nonneg (fun w => sq_nonneg _)) (fun l => ?_)
    (by simpa only [mul_zero, add_zero] using hlim)
  have hdom : Integrable (fun w => 2 * R l w ^ 2 + 2 * T l w ^ 2) W.law := by
    simpa only [Pi.add_def] using
      ((hR l).integrable_sq.const_mul 2).add ((hT l).integrable_sq.const_mul 2)
  have hbound := integral_mono (hi l) hdom (fun w => by
    rw [potentialTaylorError_eq W β hβ V hV l]
    change (R l w + T l w) ^ 2 ≤ _
    nlinarith [sq_nonneg (R l w - T l w)])
  simpa only [integral_add ((hR l).integrable_sq.const_mul 2) ((hT l).integrable_sq.const_mul 2),
    integral_const_mul, R, T] using hbound

end SKConstants.Completion.J3B
