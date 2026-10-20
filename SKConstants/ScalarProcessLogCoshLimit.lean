module

public import SKConstants.ScalarProcessLogCoshHistory
public import SKConstants.ScalarProcessPosteriorIntegralLimit
public import SKConstants.ScalarProcessWeightedMesh

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

lemma scalarLogCosh_lipschitz : LipschitzWith 1 scalarLogCosh := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_scalarLogCosh x).differentiableAt)
  intro x
  rw [(hasDerivAt_scalarLogCosh x).deriv]
  exact scalar_tanh_abs_le_one x

lemma scalarLogCosh_abs_sub_le (x y : ℝ) :
    |scalarLogCosh x - scalarLogCosh y| ≤ |x - y| := by
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using scalarLogCosh_lipschitz.dist_le_mul x y

theorem integrable_scalarHiddenContinuousField_increment_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    Integrable (fun u => (scalarHiddenContinuousField z B s u -
      scalarHiddenContinuousField z B t u) ^ 2) (scalarHiddenBrownianLaw z P) := by
  have hl := (hB.hasLaw_sub s t).comp
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).hasLaw
  have hb : Integrable (fun u : Bool × Ω => (B s u.2 - B t u.2) ^ 2)
      (scalarHiddenBrownianLaw z P) :=
    hl.integrable_comp (gaussianReal_integrable_pow 0 (nndist (s : ℝ) (t : ℝ)) 2)
  apply (hb.const_mul 2 |>.add (integrable_const (2 * ((s : ℝ) - (t : ℝ)) ^ 2))).mono'
  · exact (((aemeasurable_scalarHiddenContinuousField P z B hB s).sub
      (aemeasurable_scalarHiddenContinuousField P z B hB t)).pow_const 2).aestronglyMeasurable
  · apply ae_of_all
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have he : scalarHiddenContinuousField z B s u - scalarHiddenContinuousField z B t u =
        scalarHiddenSign u.1 * ((s : ℝ) - (t : ℝ)) + (B s u.2 - B t u.2) := by
      unfold scalarHiddenContinuousField
      ring
    rw [he]
    have hs : (scalarHiddenSign u.1 * ((s : ℝ) - (t : ℝ))) ^ 2 =
        ((s : ℝ) - (t : ℝ)) ^ 2 := by
      cases u.1 <;> norm_num [scalarHiddenSign] <;> ring
    simp only [Pi.add_apply] at *
    nlinarith [sq_nonneg (scalarHiddenSign u.1 * ((s : ℝ) - (t : ℝ)) - (B s u.2 - B t u.2))]

theorem integral_scalarHiddenContinuousField_increment_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    (∫ u, (scalarHiddenContinuousField z B s u - scalarHiddenContinuousField z B t u) ^ 2
      ∂scalarHiddenBrownianLaw z P) ≤
      2 * |(s : ℝ) - (t : ℝ)| + 2 * ((s : ℝ) - (t : ℝ)) ^ 2 := by
  have hl := (hB.hasLaw_sub s t).comp
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).hasLaw
  have hb : Integrable (fun u : Bool × Ω => (B s u.2 - B t u.2) ^ 2)
      (scalarHiddenBrownianLaw z P) :=
    hl.integrable_comp (gaussianReal_integrable_pow 0 (nndist (s : ℝ) (t : ℝ)) 2)
  have hmoment : (∫ u : Bool × Ω, (B s u.2 - B t u.2) ^ 2 ∂scalarHiddenBrownianLaw z P) =
      |(s : ℝ) - (t : ℝ)| := by
    have he := hl.integral_comp (gaussianReal_integrable_pow 0 (nndist (s : ℝ) (t : ℝ)) 2).aestronglyMeasurable
    change (∫ u : Bool × Ω, (B s u.2 - B t u.2) ^ 2 ∂scalarHiddenBrownianLaw z P) = _ at he
    rw [he]
    have h := gaussianReal_integral_shift_sq 0 0 (nndist (s : ℝ) (t : ℝ))
    convert h using 1 <;> simp [coe_nndist, Real.dist_eq]
  have h := integral_mono (integrable_scalarHiddenContinuousField_increment_sq P z B hB s t)
    ((hb.const_mul 2).add (integrable_const (2 * ((s : ℝ) - (t : ℝ)) ^ 2))) (fun u => by
      have he : scalarHiddenContinuousField z B s u - scalarHiddenContinuousField z B t u =
          scalarHiddenSign u.1 * ((s : ℝ) - (t : ℝ)) + (B s u.2 - B t u.2) := by
        unfold scalarHiddenContinuousField
        ring
      rw [he]
      have hs : (scalarHiddenSign u.1 * ((s : ℝ) - (t : ℝ))) ^ 2 =
          ((s : ℝ) - (t : ℝ)) ^ 2 := by cases u.1 <;> norm_num [scalarHiddenSign] <;> ring
      simp only [Pi.add_apply] at *
      nlinarith [sq_nonneg (scalarHiddenSign u.1 * ((s : ℝ) - (t : ℝ)) - (B s u.2 - B t u.2))])
  simp only [Pi.add_apply] at h
  rw [integral_add (hb.const_mul 2) (integrable_const _), integral_const_mul, hmoment] at h
  simpa using h

lemma integrable_scalarLogCosh_increment_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    Integrable (fun u => (scalarLogCosh (scalarHiddenContinuousField z B s u) -
      scalarLogCosh (scalarHiddenContinuousField z B t u)) ^ 2) (scalarHiddenBrownianLaw z P) := by
  apply (integrable_scalarHiddenContinuousField_increment_sq P z B hB s t).mono'
  · exact (((continuous_scalarLogCosh.measurable.comp_aemeasurable
      (aemeasurable_scalarHiddenContinuousField P z B hB s)).sub
      (continuous_scalarLogCosh.measurable.comp_aemeasurable
        (aemeasurable_scalarHiddenContinuousField P z B hB t))).pow_const 2).aestronglyMeasurable
  · apply ae_of_all
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := scalarLogCosh_abs_sub_le (scalarHiddenContinuousField z B s u)
      (scalarHiddenContinuousField z B t u)
    nlinarith [sq_abs (scalarLogCosh (scalarHiddenContinuousField z B s u) -
      scalarLogCosh (scalarHiddenContinuousField z B t u)),
      sq_abs (scalarHiddenContinuousField z B s u - scalarHiddenContinuousField z B t u),
      abs_nonneg (scalarLogCosh (scalarHiddenContinuousField z B s u) -
        scalarLogCosh (scalarHiddenContinuousField z B t u)),
      abs_nonneg (scalarHiddenContinuousField z B s u - scalarHiddenContinuousField z B t u)]

theorem scalarUniformLogCoshEndpoint_tendsto_L2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    Tendsto (fun n => ∫ u, (scalarLogCosh (scalarHiddenContinuousField z B
        (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) -
      scalarLogCosh (scalarHiddenContinuousField z B T u)) ^ 2 ∂scalarHiddenBrownianLaw z P)
      atTop (𝓝 0) := by
  have hbound : ∀ n, (∫ u, (scalarLogCosh (scalarHiddenContinuousField z B
        (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) -
      scalarLogCosh (scalarHiddenContinuousField z B T u)) ^ 2 ∂scalarHiddenBrownianLaw z P) ≤
      2 * |(scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) - (T : ℝ)| +
      2 * ((scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) - (T : ℝ)) ^ 2 := by
    intro n
    apply le_trans (integral_mono
      (integrable_scalarLogCosh_increment_sq P z B hB _ T)
      (integrable_scalarHiddenContinuousField_increment_sq P z B hB _ T) ?_)
      (integral_scalarHiddenContinuousField_increment_sq_le P z B hB _ T)
    intro u
    have h := scalarLogCosh_abs_sub_le (scalarHiddenContinuousField z B
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) (scalarHiddenContinuousField z B T u)
    nlinarith [sq_abs (scalarLogCosh (scalarHiddenContinuousField z B
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) -
      scalarLogCosh (scalarHiddenContinuousField z B T u)),
      sq_abs (scalarHiddenContinuousField z B
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u - scalarHiddenContinuousField z B T u),
      abs_nonneg (scalarLogCosh (scalarHiddenContinuousField z B
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) -
      scalarLogCosh (scalarHiddenContinuousField z B T u)),
      abs_nonneg (scalarHiddenContinuousField z B
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u - scalarHiddenContinuousField z B T u)]
  have htime := NNReal.continuous_coe.tendsto T |>.comp (scalarUniformTime_floor_tendsto T)
  have hd : Tendsto (fun n => (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) - (T : ℝ))
      atTop (𝓝 0) := by simpa using htime.sub_const (T : ℝ)
  apply squeeze_zero (fun n => integral_nonneg (fun u => sq_nonneg _)) hbound
  simpa using (hd.abs.const_mul 2).add ((hd.pow 2).const_mul 2)

@[expose] def scalarContinuousPosteriorSquareDrift {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (u : Bool × Ω) : ℝ :=
  ∫ s in Set.Icc (0 : ℝ) (T : ℝ), Real.tanh (scalarHiddenFieldReal z B s u) ^ 2

@[expose] def scalarUniformPosteriorSquareDrift {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (T : ℝ≥0) (u : Bool × Ω) : ℝ :=
  ∑ k ∈ Finset.range ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊,
    (1 / ((n : ℝ) + 1)) * Real.tanh (scalarHiddenContinuousField z B (scalarUniformTime n k) u) ^ 2

lemma scalarPosteriorSquareTimeSum_sampled {Ω : Type*} (Y : ℕ → Ω → ℝ) (z : ℝ)
    (dt : ℕ → ℝ≥0) (n : ℕ) (u : Ω) (hzero : Y 0 u = z) :
    scalarPosteriorSquareTimeSum z dt n
      (scalarSampledFieldHistory (fun k => Y (k + 1)) n u) =
      ∑ k ∈ Finset.range n, (dt k : ℝ) * Real.tanh (Y k u) ^ 2 := by
  induction n with
  | zero => simp [scalarPosteriorSquareTimeSum]
  | succ n ih =>
    change scalarPosteriorSquareTimeSum z dt n
      (scalarSampledFieldHistory (fun k => Y (k + 1)) n u) +
      (dt n : ℝ) * Real.tanh (scalarLastField z n
        (scalarSampledFieldHistory (fun k => Y (k + 1)) n u)) ^ 2 = _
    rw [ih, scalarLastField_sampled Y z n u hzero, Finset.sum_range_succ]

lemma scalar_tanh_square_norm_le (y : ℝ) : ‖Real.tanh y ^ 2‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := scalar_tanh_abs_le_one y
  nlinarith [sq_abs (Real.tanh y), abs_nonneg (Real.tanh y)]

lemma scalarUniformPosteriorSquareDrift_eq_euler {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (T : ℝ≥0) (u : Bool × Ω) :
    scalarUniformPosteriorSquareDrift z B n T u =
      scalarEulerDrift (fun s => Real.tanh (scalarHiddenFieldReal z B s u) ^ 2)
        (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) n := by
  rw [scalarEulerDrift_eq_grid_sum _ n _ (fun s => scalar_tanh_square_norm_le _)]
  unfold scalarUniformPosteriorSquareDrift
  apply Finset.sum_congr rfl
  intro k hk
  simp only [scalarHiddenFieldReal, Real.toNNReal_coe, scalarHiddenContinuousField]

lemma scalarContinuousPosteriorSquareDrift_norm_le {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (u : Bool × Ω) :
    ‖scalarContinuousPosteriorSquareDrift z B T u‖ ≤ (T : ℝ) := by
  have h := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Set.Icc (0 : ℝ) (T : ℝ)))
    (f := fun s => Real.tanh (scalarHiddenFieldReal z B s u) ^ 2)
    (ae_of_all _ (fun s => scalar_tanh_square_norm_le _))
  simpa only [scalarContinuousPosteriorSquareDrift, Measure.real, Measure.restrict_apply_univ,
    Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal T.coe_nonneg, one_mul] using h

lemma scalarUniformPosteriorSquareDrift_norm_le {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (T : ℝ≥0) (u : Bool × Ω) :
    ‖scalarUniformPosteriorSquareDrift z B n T u‖ ≤ (T : ℝ) := by
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have ht : (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) ≤ (T : ℝ) := by
    rw [scalarUniformTime_coe]
    apply (div_le_iff₀ hN).2
    exact (Nat.floor_le (by positivity)).trans_eq (mul_comm _ _)
  rw [scalarUniformPosteriorSquareDrift_eq_euler]
  have h := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Set.Icc (0 : ℝ)
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ)))
    (f := fun s => Real.tanh (scalarHiddenFieldReal z B (scalarLeftMeshSample n s) u) ^ 2)
    (ae_of_all _ (fun s => scalar_tanh_square_norm_le _))
  have he : ‖scalarEulerDrift (fun s => Real.tanh (scalarHiddenFieldReal z B s u) ^ 2)
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) n‖ ≤
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) := by
    simpa only [scalarEulerDrift, Measure.real, Measure.restrict_apply_univ,
      Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal (scalarUniformTime n _).coe_nonneg,
      one_mul] using h
  exact he.trans ht

lemma aemeasurable_scalarUniformPosteriorSquareDrift {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (n : ℕ) (T : ℝ≥0) :
    AEMeasurable (scalarUniformPosteriorSquareDrift z B n T) (scalarHiddenBrownianLaw z P) := by
  unfold scalarUniformPosteriorSquareDrift
  apply Finset.aemeasurable_fun_sum
  intro k hk
  exact ((measurable_scalarTanh.comp_aemeasurable
    (aemeasurable_scalarHiddenContinuousField P z B hB _)).pow_const 2).const_mul _

lemma scalarUniformPosteriorSquareDrift_tendsto_path {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (u : Bool × Ω)
    (hB : Continuous (fun t => B t u.2)) :
    Tendsto (fun n => scalarUniformPosteriorSquareDrift z B n T u)
      atTop (𝓝 (scalarContinuousPosteriorSquareDrift z B T u)) := by
  let f : ℝ → ℝ := fun s => Real.tanh (scalarHiddenFieldReal z B s u) ^ 2
  have hf : Continuous f := (continuous_scalarTanh.comp
    (continuous_scalarHiddenFieldReal z B u hB)).pow 2
  have hb : ∀ s, ‖f s‖ ≤ 1 := fun s => scalar_tanh_square_norm_le _
  have ht := NNReal.continuous_coe.tendsto T |>.comp (scalarUniformTime_floor_tendsto T)
  have he : Tendsto (fun n => scalarEulerDrift f
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) n - scalarEulerDrift f (T : ℝ) n)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm
    · intro n
      exact scalarEulerDrift_lipschitz_endpoint f n hb _ _
        (scalarUniformTime n _).coe_nonneg T.coe_nonneg
    · simpa using (ht.sub_const (T : ℝ)).abs
  have hs := he.add (scalarEulerDrift_tendsto f (T : ℝ) hf hb)
  have heq : (fun n => (scalarEulerDrift f
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) n - scalarEulerDrift f (T : ℝ) n) +
      scalarEulerDrift f (T : ℝ) n) =
      (fun n => scalarUniformPosteriorSquareDrift z B n T u) := by
    funext n
    rw [scalarUniformPosteriorSquareDrift_eq_euler]
    ring
  rw [heq] at hs
  simpa only [zero_add, scalarContinuousPosteriorSquareDrift, f] using hs

lemma aestronglyMeasurable_scalarContinuousPosteriorSquareDrift {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (T : ℝ≥0) :
    AEStronglyMeasurable (scalarContinuousPosteriorSquareDrift z B T) (scalarHiddenBrownianLaw z P) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (aemeasurable_scalarUniformPosteriorSquareDrift P z B hB.toIsPreBrownianReal n T).aestronglyMeasurable)
  have hc : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hB.cont
  filter_upwards [hc] with u hu
  exact scalarUniformPosteriorSquareDrift_tendsto_path z B T u hu

lemma integrable_scalarUniformPosteriorSquareDrift_sq_error {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (T : ℝ≥0) (n : ℕ) :
    Integrable (fun u => (scalarUniformPosteriorSquareDrift z B n T u -
      scalarContinuousPosteriorSquareDrift z B T u) ^ 2) (scalarHiddenBrownianLaw z P) := by
  apply Integrable.of_bound
    (((aemeasurable_scalarUniformPosteriorSquareDrift P z B hB.toIsPreBrownianReal n T).aestronglyMeasurable.sub
      (aestronglyMeasurable_scalarContinuousPosteriorSquareDrift P z B hB T)).pow 2) (4 * (T : ℝ) ^ 2)
  apply ae_of_all
  intro u
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change (scalarUniformPosteriorSquareDrift z B n T u -
    scalarContinuousPosteriorSquareDrift z B T u) ^ 2 ≤ 4 * (T : ℝ) ^ 2
  have h := (norm_sub_le (scalarUniformPosteriorSquareDrift z B n T u)
    (scalarContinuousPosteriorSquareDrift z B T u)).trans
    (add_le_add (scalarUniformPosteriorSquareDrift_norm_le z B n T u)
      (scalarContinuousPosteriorSquareDrift_norm_le z B T u))
  rw [Real.norm_eq_abs] at h
  nlinarith [sq_abs (scalarUniformPosteriorSquareDrift z B n T u -
    scalarContinuousPosteriorSquareDrift z B T u), abs_nonneg (scalarUniformPosteriorSquareDrift z B n T u -
    scalarContinuousPosteriorSquareDrift z B T u)]

theorem scalarUniformPosteriorSquareDrift_tendsto_L2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    Tendsto (fun n => ∫ u, (scalarUniformPosteriorSquareDrift z B n T u -
      scalarContinuousPosteriorSquareDrift z B T u) ^ 2 ∂scalarHiddenBrownianLaw z P) atTop (𝓝 0) := by
  have hc : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hB.cont
  have hlim : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, Tendsto (fun n =>
      (scalarUniformPosteriorSquareDrift z B n T u -
        scalarContinuousPosteriorSquareDrift z B T u) ^ 2) atTop (𝓝 0) := by
    filter_upwards [hc] with u hu
    simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((scalarUniformPosteriorSquareDrift_tendsto_path z B T u hu).sub_const
        (scalarContinuousPosteriorSquareDrift z B T u)).pow 2
  have h := tendsto_integral_of_dominated_convergence (μ := scalarHiddenBrownianLaw z P)
    (fun _ => (4 * (T : ℝ) ^ 2))
    (F := fun n u => (scalarUniformPosteriorSquareDrift z B n T u -
      scalarContinuousPosteriorSquareDrift z B T u) ^ 2) (f := fun _ => (0 : ℝ))
    (fun n => (integrable_scalarUniformPosteriorSquareDrift_sq_error P z B hB T n).aestronglyMeasurable)
    (integrable_const _) (fun n => by
      apply ae_of_all
      intro u
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := (norm_sub_le (scalarUniformPosteriorSquareDrift z B n T u)
        (scalarContinuousPosteriorSquareDrift z B T u)).trans
        (add_le_add (scalarUniformPosteriorSquareDrift_norm_le z B n T u)
          (scalarContinuousPosteriorSquareDrift_norm_le z B T u))
      rw [Real.norm_eq_abs] at h
      nlinarith [sq_abs (scalarUniformPosteriorSquareDrift z B n T u -
        scalarContinuousPosteriorSquareDrift z B T u), abs_nonneg (scalarUniformPosteriorSquareDrift z B n T u -
        scalarContinuousPosteriorSquareDrift z B T u)]) hlim
  simpa only [integral_zero] using h

lemma scalarLogCoshIntegralSum_sampled {Ω : Type*} (Y : ℕ → Ω → ℝ) (z : ℝ)
    (dt : ℕ → ℝ≥0) (n : ℕ) (u : Ω) (hzero : Y 0 u = z) :
    scalarLogCoshIntegralSum z dt n
      (scalarSampledFieldHistory (fun k => Y (k + 1)) n u) =
      ∑ k ∈ Finset.range n, Real.tanh (Y k u) * scalarInnovation (Y k u) (dt k) (Y (k + 1) u) := by
  induction n with
  | zero => simp [scalarLogCoshIntegralSum]
  | succ n ih =>
    change scalarLogCoshIntegralSum z dt n
      (scalarSampledFieldHistory (fun k => Y (k + 1)) n u) +
      Real.tanh (scalarLastField z n
        (scalarSampledFieldHistory (fun k => Y (k + 1)) n u)) *
        scalarInnovation (scalarLastField z n
          (scalarSampledFieldHistory (fun k => Y (k + 1)) n u)) (dt n) (Y (n + 1) u) = _
    rw [ih, scalarLastField_sampled Y z n u hzero, Finset.sum_range_succ]

lemma scalarUniformLogCoshError_eq {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (T : ℝ≥0) (u : Bool × Ω) (hzero : B 0 u.2 = 0) :
    scalarUniformLogCoshError z B n T u =
      scalarLogCosh (scalarHiddenContinuousField z B
        (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) - scalarLogCosh z -
      (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) / 2 -
      scalarWeightedInnovationMeshSum Real.tanh z B n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u -
      scalarUniformPosteriorSquareDrift z B n T u / 2 := by
  let m := ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊
  let dt := brownianMeshVariance (scalarUniformTime n)
  have hz : scalarHiddenContinuousField z B (scalarUniformTime n 0) u = z := by
    simp [scalarHiddenContinuousField, scalarUniformTime, hzero]
  have hi := scalarLogCoshIntegralSum_sampled
    (fun k => scalarHiddenContinuousField z B (scalarUniformTime n k)) z dt m u hz
  have hp := scalarPosteriorSquareTimeSum_sampled
    (fun k => scalarHiddenContinuousField z B (scalarUniformTime n k)) z dt m u hz
  have hsum : (∑ k ∈ Finset.range m, (dt k : ℝ)) = (scalarUniformTime n m : ℝ) := by
    simp [dt, brownianMeshVariance_scalarUniformTime, scalarUniformTime_coe, div_eq_mul_inv]
  have hpow : (∑ k ∈ Finset.range m, (dt k : ℝ) *
      Real.tanh (scalarHiddenContinuousField z B (scalarUniformTime n k) u) ^ 2) =
      scalarUniformPosteriorSquareDrift z B n T u := by
    simp only [dt, brownianMeshVariance_scalarUniformTime, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_add, NNReal.coe_natCast]
    rfl
  unfold scalarUniformLogCoshError
  rw [scalarLogCoshHistoryError_telescope, scalarLastField_uniform z B n m u hzero]
  change scalarLogCosh (scalarHiddenContinuousField z B (scalarUniformTime n m) u) -
    scalarLogCosh z - (∑ k ∈ Finset.range m, (dt k : ℝ)) / 2 -
    scalarLogCoshIntegralSum z dt m
      (scalarSampledFieldHistory (fun k => scalarHiddenContinuousField z B (scalarUniformTime n (k + 1))) m u) -
    scalarPosteriorSquareTimeSum z dt m
      (scalarSampledFieldHistory (fun k => scalarHiddenContinuousField z B (scalarUniformTime n (k + 1))) m u) / 2 = _
  rw [hi, hp, hsum, hpow]
  rfl

@[expose] def scalarContinuousLogCoshInformation {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (u : Bool × Ω) : ℝ :=
  scalarLogCosh (scalarHiddenContinuousField z B T u) - scalarLogCosh z -
    (T : ℝ) / ((2 : ℕ) : ℝ) - scalarContinuousPosteriorSquareDrift z B T u / ((2 : ℕ) : ℝ)

lemma aestronglyMeasurable_scalarContinuousLogCoshInformation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    AEStronglyMeasurable (scalarContinuousLogCoshInformation z B T) (scalarHiddenBrownianLaw z P) :=
  (((continuous_scalarLogCosh.measurable.comp_aemeasurable
    (aemeasurable_scalarHiddenContinuousField P z B hB.toIsPreBrownianReal T)).sub_const
      (scalarLogCosh z)).sub_const ((T : ℝ) / 2)).sub
    ((aestronglyMeasurable_scalarContinuousPosteriorSquareDrift P z B hB T).aemeasurable.div_const 2)
    |>.aestronglyMeasurable

lemma integrable_scalarUniformLogCoshError_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) (n : ℕ) :
    Integrable (fun u => scalarUniformLogCoshError z B n T u ^ 2) (scalarHiddenBrownianLaw z P) :=
  (scalarUniformObservationHistory_hasLaw hB z n _).integrable_comp
    (integrable_scalarLogCoshHistoryError_sq z _ (scalarUniformMeshVariance_le_one n) _)

lemma scalar_square_sum_four_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
    sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d)]

theorem scalarWeightedLogCoshInnovation_L2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    (∀ n, Integrable (fun u => (scalarWeightedInnovationMeshSum Real.tanh z B n
        ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u - scalarContinuousLogCoshInformation z B T u) ^ 2)
      (scalarHiddenBrownianLaw z P)) ∧
    Tendsto (fun n => ∫ u, (scalarWeightedInnovationMeshSum Real.tanh z B n
        ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u - scalarContinuousLogCoshInformation z B T u) ^ 2
      ∂scalarHiddenBrownianLaw z P) atTop (𝓝 0) := by
  let S : ℕ → ℝ≥0 := fun n => scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊
  let A := fun n u => scalarLogCosh (scalarHiddenContinuousField z B (S n) u) -
    scalarLogCosh (scalarHiddenContinuousField z B T u)
  let D := fun n u => scalarUniformPosteriorSquareDrift z B n T u -
    scalarContinuousPosteriorSquareDrift z B T u
  let R := scalarUniformLogCoshError z B
  let X := fun n u => scalarWeightedInnovationMeshSum Real.tanh z B n
      ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u - scalarContinuousLogCoshInformation z B T u
  let C := fun n => (S n : ℝ) - (T : ℝ)
  have hzero : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, B 0 u.2 = 0 :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae
      hB.toIsPreBrownianReal.eval_zero_ae_eq_zero
  have hbound : ∀ n, ∀ᵐ u ∂scalarHiddenBrownianLaw z P,
      X n u ^ 2 ≤ 4 * A n u ^ 2 + C n ^ 2 + D n u ^ 2 + 4 * R n T u ^ 2 := by
    intro n
    filter_upwards [hzero] with u hu
    have he := scalarUniformLogCoshError_eq z B n T u hu
    have hx : X n u = A n u + (-C n / 2) + (-D n u / 2) + (-R n T u) := by
      dsimp [X, A, D, C, S, R, scalarContinuousLogCoshInformation] at *
      linarith [he]
    rw [hx]
    have h := scalar_square_sum_four_le (A n u) (-C n / 2) (-D n u / 2) (-R n T u)
    nlinarith
  have hA : ∀ n, Integrable (fun u => A n u ^ 2) (scalarHiddenBrownianLaw z P) :=
    fun n => integrable_scalarLogCosh_increment_sq P z B hB.toIsPreBrownianReal (S n) T
  have hD : ∀ n, Integrable (fun u => D n u ^ 2) (scalarHiddenBrownianLaw z P) :=
    fun n => integrable_scalarUniformPosteriorSquareDrift_sq_error P z B hB T n
  have hR : ∀ n, Integrable (fun u => R n T u ^ 2) (scalarHiddenBrownianLaw z P) :=
    fun n => integrable_scalarUniformLogCoshError_sq P z B hB.toIsPreBrownianReal T n
  have hi : ∀ n, Integrable (fun u => 4 * A n u ^ 2 + C n ^ 2 + D n u ^ 2 + 4 * R n T u ^ 2)
      (scalarHiddenBrownianLaw z P) :=
    fun n => (((hA n).const_mul 4 |>.add (integrable_const _)).add (hD n)).add ((hR n).const_mul 4)
  have hX : ∀ n, Integrable (fun u => X n u ^ 2) (scalarHiddenBrownianLaw z P) := by
    intro n
    apply (hi n).mono'
    · exact (((aemeasurable_scalarWeightedInnovationMeshSum P Real.tanh measurable_scalarTanh z B
        hB.toIsPreBrownianReal n _).aestronglyMeasurable.sub
        (aestronglyMeasurable_scalarContinuousLogCoshInformation P z B hB T)).pow 2)
    · filter_upwards [hbound n] with u hu
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hu
  have hint : ∀ n, (∫ u, X n u ^ 2 ∂scalarHiddenBrownianLaw z P) ≤
      4 * (∫ u, A n u ^ 2 ∂scalarHiddenBrownianLaw z P) + C n ^ 2 +
        (∫ u, D n u ^ 2 ∂scalarHiddenBrownianLaw z P) +
        4 * (∫ u, R n T u ^ 2 ∂scalarHiddenBrownianLaw z P) := by
    intro n
    have h := integral_mono_ae (hX n) (hi n) (hbound n)
    rw [integral_add
      (f := fun u => 4 * A n u ^ 2 + C n ^ 2 + D n u ^ 2)
      (g := fun u => 4 * R n T u ^ 2)
      (((hA n).const_mul 4 |>.add (integrable_const _)).add (hD n)) ((hR n).const_mul 4),
      integral_add (f := fun u => 4 * A n u ^ 2 + C n ^ 2)
        (g := fun u => D n u ^ 2) ((hA n).const_mul 4 |>.add (integrable_const _)) (hD n),
      integral_add (f := fun u => 4 * A n u ^ 2) (g := fun _ => C n ^ 2)
        ((hA n).const_mul 4) (integrable_const _), integral_const_mul, integral_const_mul] at h
    simpa using h
  have htime := NNReal.continuous_coe.tendsto T |>.comp (scalarUniformTime_floor_tendsto T)
  have hC : Tendsto (fun n => C n ^ 2) atTop (𝓝 0) := by
    simpa [C, S] using (htime.sub_const (T : ℝ)).pow 2
  have hlim := (((scalarUniformLogCoshEndpoint_tendsto_L2 P z B hB.toIsPreBrownianReal T).const_mul 4).add hC).add
    (scalarUniformPosteriorSquareDrift_tendsto_L2 P z B hB T) |>.add
    ((scalarUniformLogCoshError_tendsto_L2 P z B hB.toIsPreBrownianReal T).const_mul 4)
  refine ⟨hX, ?_⟩
  apply squeeze_zero (fun n => integral_nonneg (fun u => sq_nonneg _)) hint
  simpa only [mul_zero, zero_add] using hlim

lemma integrable_scalarWeightedLogCoshInnovation_sq_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) (n : ℕ) :
    Integrable (fun u => (scalarWeightedInnovationMeshSum Real.tanh z B n
        ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u - scalarContinuousLogCoshInformation z B T u) ^ 2)
      (scalarHiddenBrownianLaw z P) :=
  (scalarWeightedLogCoshInnovation_L2 P z B hB T).1 n

theorem scalarWeightedLogCoshInnovation_tendsto_L2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    Tendsto (fun n => ∫ u, (scalarWeightedInnovationMeshSum Real.tanh z B n
        ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u - scalarContinuousLogCoshInformation z B T u) ^ 2
      ∂scalarHiddenBrownianLaw z P) atTop (𝓝 0) :=
  (scalarWeightedLogCoshInnovation_L2 P z B hB T).2

theorem scalarWeightedLogCoshBrownian_L2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    (∀ n, Integrable (fun u => (scalarWeightedBrownianMeshSum Real.tanh z B n
        ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u - scalarContinuousLogCoshInformation z B T u) ^ 2)
      (scalarHiddenBrownianLaw z P)) ∧
    Tendsto (fun n => ∫ u, (scalarWeightedBrownianMeshSum Real.tanh z B n
        ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u - scalarContinuousLogCoshInformation z B T u) ^ 2
      ∂scalarHiddenBrownianLaw z P) atTop (𝓝 0) := by
  let m : ℕ → ℕ := fun n => ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊
  let A := fun n u => scalarWeightedInnovationMeshSum Real.tanh z B n (m n) u -
    scalarContinuousLogCoshInformation z B T u
  let D := fun n u => scalarWeightedInnovationMeshSum Real.tanh z B n (m n) u -
    scalarWeightedBrownianMeshSum Real.tanh z B n (m n) u
  let X := fun n u => scalarWeightedBrownianMeshSum Real.tanh z B n (m n) u -
    scalarContinuousLogCoshInformation z B T u
  have hbound : ∀ n u, X n u ^ 2 ≤ 2 * A n u ^ 2 + 2 * D n u ^ 2 := by
    intro n u
    have he : X n u = A n u - D n u := by dsimp [X, A, D]; ring
    rw [he]
    nlinarith [sq_nonneg (A n u + D n u)]
  have hA : ∀ n, Integrable (fun u => A n u ^ 2) (scalarHiddenBrownianLaw z P) :=
    fun n => integrable_scalarWeightedLogCoshInnovation_sq_error P z B hB T n
  have hD : ∀ n, Integrable (fun u => D n u ^ 2) (scalarHiddenBrownianLaw z P) :=
    fun n => integrable_scalarWeightedInnovationMeshSum_sub_sq P Real.tanh measurable_scalarTanh
      (fun y => norm_tanh_le_one y) z B hB n (m n)
  have hX : ∀ n, Integrable (fun u => X n u ^ 2) (scalarHiddenBrownianLaw z P) := by
    intro n
    apply (((hA n).const_mul 2).add ((hD n).const_mul 2)).mono'
    · exact (((aemeasurable_scalarWeightedBrownianMeshSum P Real.tanh measurable_scalarTanh z B hB n (m n)).aestronglyMeasurable.sub
        (aestronglyMeasurable_scalarContinuousLogCoshInformation P z B hB T)).pow 2)
    · apply ae_of_all
      intro u
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hbound n u
  have hint : ∀ n, (∫ u, X n u ^ 2 ∂scalarHiddenBrownianLaw z P) ≤
      2 * (∫ u, A n u ^ 2 ∂scalarHiddenBrownianLaw z P) +
      2 * (∫ u, D n u ^ 2 ∂scalarHiddenBrownianLaw z P) := by
    intro n
    have h := integral_mono (hX n) (((hA n).const_mul 2).add ((hD n).const_mul 2)) (hbound n)
    simp only [Pi.add_apply] at h
    rw [integral_add (f := fun u => 2 * A n u ^ 2) (g := fun u => 2 * D n u ^ 2)
      ((hA n).const_mul 2) ((hD n).const_mul 2), integral_const_mul, integral_const_mul] at h
    exact h
  refine ⟨hX, ?_⟩
  apply squeeze_zero (fun n => integral_nonneg (fun u => sq_nonneg _)) hint
  have h := ((scalarWeightedLogCoshInnovation_tendsto_L2 P z B hB T).const_mul 2).add
    ((scalarWeightedInnovationMeshSum_sub_tendsto_L2 P Real.tanh measurable_scalarTanh
      (fun y => norm_tanh_le_one y) z B hB T).const_mul 2)
  simpa only [mul_zero, zero_add] using h

lemma integrable_scalarWeightedLogCoshBrownian_sq_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) (n : ℕ) :
    Integrable (fun u => (scalarWeightedBrownianMeshSum Real.tanh z B n
        ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u - scalarContinuousLogCoshInformation z B T u) ^ 2)
      (scalarHiddenBrownianLaw z P) :=
  (scalarWeightedLogCoshBrownian_L2 P z B hB T).1 n

theorem scalarWeightedLogCoshBrownian_tendsto_L2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    Tendsto (fun n => ∫ u, (scalarWeightedBrownianMeshSum Real.tanh z B n
        ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u - scalarContinuousLogCoshInformation z B T u) ^ 2
      ∂scalarHiddenBrownianLaw z P) atTop (𝓝 0) :=
  (scalarWeightedLogCoshBrownian_L2 P z B hB T).2

#print axioms scalarUniformLogCoshEndpoint_tendsto_L2
#print axioms scalarUniformPosteriorSquareDrift_tendsto_L2
#print axioms scalarWeightedLogCoshBrownian_tendsto_L2
end SKConstants
