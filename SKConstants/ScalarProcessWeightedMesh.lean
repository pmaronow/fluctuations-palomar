module
public import SKConstants.ScalarProcessConditionalInnovation
public import Mathlib.Tactic

public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

@[expose] def scalarWeightedDriftMeshError (f : ℝ → ℝ) (w : ℕ → ℝ) (n m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, w k *
    ((∫ s in (scalarUniformTime n k : ℝ)..(scalarUniformTime n (k + 1) : ℝ), f s) -
      (1 / ((n : ℝ) + 1)) * f (scalarUniformTime n k : ℝ))

@[expose] def scalarDriftMeshModulus (f : ℝ → ℝ) (n : ℕ) (T : ℝ) : ℝ :=
  ∫ s in Set.Icc 0 T, ‖f s - f (scalarLeftMeshSample n s)‖

lemma scalarUniformTime_real_increment (n k : ℕ) :
    (scalarUniformTime n (k + 1) : ℝ) - (scalarUniformTime n k : ℝ) =
      1 / ((n : ℝ) + 1) := by
  simp only [scalarUniformTime_coe, Nat.cast_add, Nat.cast_one]
  ring

lemma scalarWeightedDriftMeshError_norm_le (f : ℝ → ℝ) (w : ℕ → ℝ)
    (n m : ℕ) (hf : ∀ s, ‖f s‖ ≤ 1) (hw : ∀ k, ‖w k‖ ≤ 1) :
    ‖scalarWeightedDriftMeshError f w n m‖ ≤ 2 * (scalarUniformTime n m : ℝ) := by
  have hc (k : ℕ) :
      ‖(∫ s in (scalarUniformTime n k : ℝ)..(scalarUniformTime n (k + 1) : ℝ), f s) -
        (1 / ((n : ℝ) + 1)) * f (scalarUniformTime n k : ℝ)‖ ≤ 2 / ((n : ℝ) + 1) := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (scalarUniformTime n k : ℝ)) (b := (scalarUniformTime n (k + 1) : ℝ))
      (fun s _ => hf s)
    rw [abs_of_nonneg (sub_nonneg.mpr (NNReal.coe_le_coe.mpr
      (scalarUniformTime_monotone n (Nat.le_succ k)))), scalarUniformTime_real_increment] at hi
    have hm : ‖(1 / ((n : ℝ) + 1)) * f (scalarUniformTime n k : ℝ)‖ ≤ 1 / ((n : ℝ) + 1) := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact (mul_le_mul_of_nonneg_left (hf _) (by positivity)).trans_eq (mul_one _)
    simp only [one_mul] at hi
    apply (norm_sub_le _ _).trans
    calc
      _ ≤ (1 / ((n : ℝ) + 1)) + (1 / ((n : ℝ) + 1)) := add_le_add hi hm
      _ = _ := by ring
  unfold scalarWeightedDriftMeshError
  calc
    _ ≤ ∑ k ∈ Finset.range m, ‖w k *
      ((∫ s in (scalarUniformTime n k : ℝ)..(scalarUniformTime n (k + 1) : ℝ), f s) -
        (1 / ((n : ℝ) + 1)) * f (scalarUniformTime n k : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range m, (2 / ((n : ℝ) + 1)) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hw k) (norm_nonneg _)).trans
        ((one_mul _).le.trans (hc k))
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      scalarUniformTime_coe]; ring

lemma scalarDriftMeshModulus_tendsto_zero (f : ℝ → ℝ) (hf : Continuous f)
    (hb : ∀ s, ‖f s‖ ≤ 1) (T : ℝ) :
    Tendsto (fun n => scalarDriftMeshModulus f n T) atTop (nhds 0) := by
  have hh := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Set.Icc 0 T))
    (F := fun n s => ‖f s - f (scalarLeftMeshSample n s)‖)
    (f := fun _ => (0 : ℝ)) (fun _ : ℝ => (2 : ℝ))
    (fun n => (hf.measurable.sub (measurable_scalarMeshComposite f n)).norm.aestronglyMeasurable)
    (integrable_const _) (fun n => Filter.Eventually.of_forall (fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact (norm_sub_le _ _).trans (by linarith [hb s, hb (scalarLeftMeshSample n s)])))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      have he := (tendsto_const_nhds : Tendsto (fun _ : ℕ => f s) atTop (nhds (f s))).sub
        (hf.continuousAt.tendsto.comp (scalarLeftMeshSample_tendsto s hs.1))
      simpa only [Function.comp_def, sub_self, norm_zero] using he.norm)
  simpa only [scalarDriftMeshModulus, integral_zero] using hh

lemma scalarWeightedDriftMeshError_norm_le_modulus (f : ℝ → ℝ) (w : ℕ → ℝ)
    (n m : ℕ) (T : ℝ) (hT : 0 ≤ T) (hgrid : (scalarUniformTime n m : ℝ) ≤ T)
    (hf : Continuous f) (hb : ∀ s, ‖f s‖ ≤ 1) (hw : ∀ k, ‖w k‖ ≤ 1) :
    ‖scalarWeightedDriftMeshError f w n m‖ ≤ scalarDriftMeshModulus f n T := by
  let e : ℝ → ℝ := fun s => f s - f (scalarLeftMeshSample n s)
  have hei (a b : ℝ) : IntervalIntegrable e volume a b :=
    (hf.intervalIntegrable a b).sub (intervalIntegrable_scalarMeshComposite f n hb a b)
  have hc (k : ℕ) :
      (∫ s in (scalarUniformTime n k : ℝ)..(scalarUniformTime n (k + 1) : ℝ), f s) -
        (1 / ((n : ℝ) + 1)) * f (scalarUniformTime n k : ℝ) =
      ∫ s in (scalarUniformTime n k : ℝ)..(scalarUniformTime n (k + 1) : ℝ), e s := by
    dsimp only [e]
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
      (intervalIntegrable_scalarMeshComposite f n hb _ _)]
    congr 1
    rw [scalarUniformTime_coe, scalarUniformTime_coe, scalarEulerDrift_cell_integral]
    · congr 1
      push_cast
      ring
    · exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ k) (by positivity)
    · simp only [Nat.cast_add, Nat.cast_one]
      exact le_rfl
  unfold scalarWeightedDriftMeshError
  simp_rw [hc]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k => (scalarUniformTime n k : ℝ)) (n := m)
    (fun k _ => (hei _ _).norm)
  simp only [scalarUniformTime_zero, NNReal.coe_zero] at hsum
  calc
    _ ≤ ∑ k ∈ Finset.range m, ‖w k *
      ∫ s in (scalarUniformTime n k : ℝ)..(scalarUniformTime n (k + 1) : ℝ), e s‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range m,
      ∫ s in (scalarUniformTime n k : ℝ)..(scalarUniformTime n (k + 1) : ℝ), ‖e s‖ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hw k) (norm_nonneg _)).trans
        ((one_mul _).le.trans (intervalIntegral.norm_integral_le_integral_norm
          (NNReal.coe_le_coe.mpr (scalarUniformTime_monotone n (Nat.le_succ k)))))
    _ = ∫ s in (0 : ℝ)..(scalarUniformTime n m : ℝ), ‖e s‖ := hsum
    _ ≤ ∫ s in (0 : ℝ)..T, ‖e s‖ :=
      intervalIntegral.integral_mono_interval (le_refl _) (scalarUniformTime n m).coe_nonneg hgrid
        (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) (hei 0 T).norm
    _ = _ := by
      unfold scalarDriftMeshModulus
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]

lemma scalarWeightedDriftMeshError_tendsto_zero (f : ℝ → ℝ) (w : ℕ → ℕ → ℝ)
    (T : ℝ≥0) (hf : Continuous f) (hb : ∀ s, ‖f s‖ ≤ 1) (hw : ∀ n k, ‖w n k‖ ≤ 1) :
    Tendsto (fun n => scalarWeightedDriftMeshError f (w n) n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊)
      atTop (nhds 0) := by
  apply squeeze_zero_norm
  · intro n
    apply scalarWeightedDriftMeshError_norm_le_modulus f (w n) n _ (T : ℝ) T.coe_nonneg
    · rw [scalarUniformTime_coe]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
      exact (Nat.floor_le (by positivity)).trans_eq (mul_comm _ _)
    · exact hf
    · exact hb
    · exact hw n
  · exact scalarDriftMeshModulus_tendsto_zero f hf hb (T : ℝ)

@[expose] def scalarWeightedInnovationMeshSum {Ω : Type*} (H : ℝ → ℝ) (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (n m : ℕ) (u : Bool × Ω) : ℝ :=
  ∑ k ∈ Finset.range m, H (scalarHiddenContinuousField z B (scalarUniformTime n k) u) *
    scalarInnovation (scalarHiddenContinuousField z B (scalarUniformTime n k) u)
      (brownianMeshVariance (scalarUniformTime n) k)
      (scalarHiddenContinuousField z B (scalarUniformTime n (k + 1)) u)

@[expose] def scalarWeightedBrownianMeshSum {Ω : Type*} (H : ℝ → ℝ) (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (n m : ℕ) (u : Bool × Ω) : ℝ :=
  ∑ k ∈ Finset.range m, H (scalarHiddenContinuousField z B (scalarUniformTime n k) u) *
    (scalarContinuousInnovation z B (scalarUniformTime n (k + 1)) u -
      scalarContinuousInnovation z B (scalarUniformTime n k) u)

lemma scalarContinuousDrift_increment {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (u : Bool × Ω) (hB : Continuous (fun t => B t u.2)) (S T : ℝ≥0) :
    scalarContinuousDrift z B T u - scalarContinuousDrift z B S u =
      ∫ s in (S : ℝ)..(T : ℝ), Real.tanh (scalarHiddenFieldReal z B s u) := by
  have hf := continuous_scalarTanh.comp (continuous_scalarHiddenFieldReal z B u hB)
  unfold scalarContinuousDrift
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le T.coe_nonneg, ← intervalIntegral.integral_of_le S.coe_nonneg]
  exact intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)

lemma scalarWeightedInnovationMeshSum_sub_eq_driftError {Ω : Type*}
    (H : ℝ → ℝ) (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (n m : ℕ)
    (u : Bool × Ω) (hB : Continuous (fun t => B t u.2)) :
    scalarWeightedInnovationMeshSum H z B n m u - scalarWeightedBrownianMeshSum H z B n m u =
      scalarWeightedDriftMeshError (fun s => Real.tanh (scalarHiddenFieldReal z B s u))
        (fun k => H (scalarHiddenContinuousField z B (scalarUniformTime n k) u)) n m := by
  unfold scalarWeightedInnovationMeshSum scalarWeightedBrownianMeshSum scalarWeightedDriftMeshError
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hd := scalarContinuousDrift_increment z B u hB
    (scalarUniformTime n k) (scalarUniformTime n (k + 1))
  have hy : scalarHiddenFieldReal z B (scalarUniformTime n k : ℝ) u =
      scalarHiddenContinuousField z B (scalarUniformTime n k) u := by
    unfold scalarHiddenFieldReal scalarHiddenContinuousField
    rw [Real.toNNReal_coe]
  rw [← hd]
  dsimp only
  rw [hy, brownianMeshVariance_scalarUniformTime]
  unfold scalarInnovation scalarContinuousInnovation
  simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_add, NNReal.coe_natCast]
  ring

lemma aemeasurable_scalarWeightedInnovationMeshSum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : ℝ → ℝ) (hH : Measurable H)
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P) (n m : ℕ) :
    AEMeasurable (scalarWeightedInnovationMeshSum H z B n m) (scalarHiddenBrownianLaw z P) := by
  unfold scalarWeightedInnovationMeshSum
  apply Finset.aemeasurable_fun_sum
  intro k hk
  have hy := aemeasurable_scalarHiddenContinuousField_conditional P z B hB (scalarUniformTime n k)
  have hyn := aemeasurable_scalarHiddenContinuousField_conditional P z B hB (scalarUniformTime n (k + 1))
  exact (hH.comp_aemeasurable hy).mul
    ((measurable_scalarInnovation _).comp_aemeasurable (hy.prodMk hyn))

lemma aemeasurable_scalarWeightedBrownianMeshSum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : ℝ → ℝ) (hH : Measurable H)
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (n m : ℕ) :
    AEMeasurable (scalarWeightedBrownianMeshSum H z B n m) (scalarHiddenBrownianLaw z P) := by
  unfold scalarWeightedBrownianMeshSum
  apply Finset.aemeasurable_fun_sum
  intro k hk
  exact (hH.comp_aemeasurable (aemeasurable_scalarHiddenContinuousField_conditional P z B
    hB.toIsPreBrownianReal _)).mul
    ((aestronglyMeasurable_scalarContinuousInnovation P z B hB _).aemeasurable.sub
      (aestronglyMeasurable_scalarContinuousInnovation P z B hB _).aemeasurable)

lemma scalarWeightedInnovationMeshSum_sub_norm_le_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : ℝ → ℝ) (hbH : ∀ y, ‖H y‖ ≤ 1)
    (z : ℝ) (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (n m : ℕ) :
    ∀ᵐ u ∂scalarHiddenBrownianLaw z P,
      ‖scalarWeightedInnovationMeshSum H z B n m u - scalarWeightedBrownianMeshSum H z B n m u‖ ≤
        2 * (scalarUniformTime n m : ℝ) := by
  have hcont : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hB.cont
  filter_upwards [hcont] with u hu
  rw [scalarWeightedInnovationMeshSum_sub_eq_driftError H z B n m u hu]
  exact scalarWeightedDriftMeshError_norm_le _ _ n m (fun _ => norm_tanh_le_one _) (fun _ => hbH _)

lemma integrable_scalarWeightedInnovationMeshSum_sub_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : ℝ → ℝ) (hH : Measurable H)
    (hbH : ∀ y, ‖H y‖ ≤ 1) (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (n m : ℕ) :
    Integrable (fun u => (scalarWeightedInnovationMeshSum H z B n m u -
      scalarWeightedBrownianMeshSum H z B n m u) ^ 2) (scalarHiddenBrownianLaw z P) := by
  apply Integrable.of_bound
    (((aemeasurable_scalarWeightedInnovationMeshSum P H hH z B hB.toIsPreBrownianReal n m).sub
      (aemeasurable_scalarWeightedBrownianMeshSum P H hH z B hB n m)).pow_const 2).aestronglyMeasurable
    ((2 * (scalarUniformTime n m : ℝ)) ^ 2)
  filter_upwards [scalarWeightedInnovationMeshSum_sub_norm_le_ae P H hbH z B hB n m] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (by simpa only [Pi.sub_apply, Real.norm_eq_abs] using hu)

lemma scalarWeightedInnovationMeshSum_sub_tendsto_L2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : ℝ → ℝ) (hH : Measurable H)
    (hbH : ∀ y, ‖H y‖ ≤ 1) (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    Tendsto (fun n => ∫ u, (scalarWeightedInnovationMeshSum H z B n
        ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u -
      scalarWeightedBrownianMeshSum H z B n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u) ^ 2
      ∂scalarHiddenBrownianLaw z P) atTop (nhds 0) := by
  let m : ℕ → ℕ := fun n => ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊
  let E : ℕ → Bool × Ω → ℝ := fun n u => scalarWeightedInnovationMeshSum H z B n (m n) u -
    scalarWeightedBrownianMeshSum H z B n (m n) u
  have hcont : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hB.cont
  have hm (n : ℕ) : (scalarUniformTime n (m n) : ℝ) ≤ (T : ℝ) := by
    rw [scalarUniformTime_coe]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    exact (Nat.floor_le (by positivity)).trans_eq (mul_comm _ _)
  have hBound (n : ℕ) : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, ‖E n u‖ ≤ 2 * (T : ℝ) := by
    filter_upwards [hcont] with u hu
    dsimp only [E]
    rw [scalarWeightedInnovationMeshSum_sub_eq_driftError H z B n (m n) u hu]
    exact (scalarWeightedDriftMeshError_norm_le _ _ n (m n)
      (fun s => norm_tanh_le_one _) (fun k => hbH _)).trans (mul_le_mul_of_nonneg_left (hm n) (by norm_num))
  have hLimit : ∀ᵐ u ∂scalarHiddenBrownianLaw z P,
      Tendsto (fun n => E n u) atTop (nhds 0) := by
    filter_upwards [hcont] with u hu
    have hf := continuous_scalarTanh.comp (continuous_scalarHiddenFieldReal z B u hu)
    have he := scalarWeightedDriftMeshError_tendsto_zero
      (fun s => Real.tanh (scalarHiddenFieldReal z B s u))
      (fun n k => H (scalarHiddenContinuousField z B (scalarUniformTime n k) u))
      T hf (fun s => norm_tanh_le_one _) (fun n k => hbH _)
    convert he using 1
    funext n
    exact scalarWeightedInnovationMeshSum_sub_eq_driftError H z B n (m n) u hu
  have hMeas (n : ℕ) : AEStronglyMeasurable (fun u => (E n u) ^ 2) (scalarHiddenBrownianLaw z P) :=
    (((aemeasurable_scalarWeightedInnovationMeshSum P H hH z B hB.toIsPreBrownianReal n (m n)).sub
      (aemeasurable_scalarWeightedBrownianMeshSum P H hH z B hB n (m n))).pow_const 2).aestronglyMeasurable
  have hh := tendsto_integral_of_dominated_convergence
    (μ := scalarHiddenBrownianLaw z P) (F := fun n u => (E n u) ^ 2) (f := fun _ => (0 : ℝ))
    (fun _ => (2 * (T : ℝ)) ^ 2) hMeas (integrable_const _)
    (fun n => by
      filter_upwards [hBound n] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (by simpa only [Pi.sub_apply, Real.norm_eq_abs] using hu))
    (by
      filter_upwards [hLimit] with u hu
      simpa only [zero_pow (by decide : 2 ≠ 0)] using hu.pow 2)
  simpa only [integral_zero] using hh

end SKConstants
