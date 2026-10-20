module

public import SKConstants.ScalarProcessLogCoshLimit
public import SKConstants.ParisiPostEndpointLaw

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace SKConstants.Completion.S33aA
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]
local instance logCosh_W_isProbability (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability

theorem logCoshHistoryError_sampled (Y : ℕ → ℝ) (z : ℝ) (dt : ℕ → ℝ≥0)
    (m : ℕ) (hzero : Y 0 = z) :
    scalarLogCoshHistoryError z dt m
        (scalarSampledFieldHistory (fun k (_ : Unit) => Y (k + 1)) m ()) =
      ∑ k ∈ Finset.range m, scalarLogCoshItoError (Y k) (dt k) (Y (k + 1)) := by
  induction m with
  | zero => simp [scalarLogCoshHistoryError]
  | succ m ih =>
    change scalarLogCoshHistoryError z dt m
      (scalarSampledFieldHistory (fun k (_ : Unit) => Y (k + 1)) m ()) +
      scalarLogCoshItoError
        (scalarLastField z m (scalarSampledFieldHistory (fun k (_ : Unit) => Y (k + 1)) m ()))
        (dt m) (Y (m + 1)) = _
    rw [ih, scalarLastField_sampled (fun k (_ : Unit) => Y k) z m () hzero, Finset.sum_range_succ]

def pathLogCoshError (T : ℝ≥0) (t : ℕ → ℝ≥0) (m : ℕ)
    (p : ScalarContinuousPath T) : ℝ :=
  ∑ k ∈ Finset.range m,
    scalarLogCoshItoError (IccExtend T.coe_nonneg p (t k)) (brownianMeshVariance t k)
      (IccExtend T.coe_nonneg p (t (k + 1)))

theorem continuous_pathLogCoshError (T : ℝ≥0) (t : ℕ → ℝ≥0) (m : ℕ) :
    Continuous (pathLogCoshError T t m) := by
  unfold pathLogCoshError
  apply continuous_finsetSum
  intro k _
  have h0 : Continuous (fun p : ScalarContinuousPath T => IccExtend T.coe_nonneg p (t k)) :=
    continuous_eval_const _
  have h1 : Continuous (fun p : ScalarContinuousPath T => IccExtend T.coe_nonneg p (t (k + 1))) :=
    continuous_eval_const _
  exact (continuous_scalarLogCoshItoError_uncurry (brownianMeshVariance t k)).comp (h0.prodMk h1)

theorem pathLogCoshError_hidden_eq (W : BrownianSystem Ω) (T : ℝ≥0)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0) (m : ℕ) (hm : t m ≤ T) (z : ℝ) :
    (fun u : Bool × Ω => pathLogCoshError T t m
      (scalarSeedHiddenFieldPath T (brownianFinitePath W T) (z, u))) =ᵐ[scalarHiddenBrownianLaw z W.law]
      (fun u => scalarLogCoshHistoryError z (brownianMeshVariance t) m
        (scalarSampledFieldHistory (fun k => scalarHiddenContinuousField z W.B (t (k + 1))) m u)) := by
  let := W.isProbability
  have hp := (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := W.law)).quasiMeasurePreserving.ae
    (brownianFinitePath_version W T)
  have hz := (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := W.law)).quasiMeasurePreserving.ae
    W.brownian.toIsPreBrownianReal.eval_zero_ae_eq_zero
  filter_upwards [hp, hz] with u hpu hzu
  have he (k : ℕ) (hk : k ≤ m) :
      IccExtend T.coe_nonneg (scalarSeedHiddenFieldPath T (brownianFinitePath W T) (z, u)) (t k) =
        scalarHiddenContinuousField z W.B (t k) u := by
    have hkT : (t k : ℝ) ≤ T := NNReal.coe_le_coe.mpr ((ht hk).trans hm)
    simp only [IccExtend, Function.comp_apply, projIcc_of_mem _ ⟨(t k).coe_nonneg, hkT⟩,
      scalarSeedHiddenFieldPath, ContinuousMap.coe_mk, hpu]
    rfl
  have hY0 : scalarHiddenContinuousField z W.B (t 0) u = z := by
    simp [scalarHiddenContinuousField, ht0, hzu]
  have hsample := logCoshHistoryError_sampled
    (fun k => scalarHiddenContinuousField z W.B (t k) u) z (brownianMeshVariance t) m hY0
  have hhist : scalarSampledFieldHistory
      (fun k (_ : Unit) => scalarHiddenContinuousField z W.B (t (k + 1)) u) m () =
      scalarSampledFieldHistory (fun k => scalarHiddenContinuousField z W.B (t (k + 1))) m u := by
    exact (scalarSampledFieldHistory_comp
      (fun k => scalarHiddenContinuousField z W.B (t (k + 1))) (fun (_ : Unit) => u) m ()).symm
  rw [hhist] at hsample
  rw [hsample]
  apply Finset.sum_congr rfl
  intro k hk
  rw [he k (Finset.mem_range.mp hk).le, he (k + 1) (Finset.mem_range.mp hk)]

theorem pathLogCoshError_hidden_bound (W : BrownianSystem Ω) (T : ℝ≥0)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0) (m : ℕ) (hm : t m ≤ T)
    (hdt : ∀ k, brownianMeshVariance t k ≤ 1) (z : ℝ) :
    Integrable (fun u : Bool × Ω => (pathLogCoshError T t m
      (scalarSeedHiddenFieldPath T (brownianFinitePath W T) (z, u))) ^ 2)
        (scalarHiddenBrownianLaw z W.law) ∧
    (∫ u : Bool × Ω, (pathLogCoshError T t m
      (scalarSeedHiddenFieldPath T (brownianFinitePath W T) (z, u))) ^ 2
        ∂scalarHiddenBrownianLaw z W.law) ≤
      12 * (∑ k ∈ Finset.range m, (brownianMeshVariance t k : ℝ) ^ 2) +
        18 * (∑ k ∈ Finset.range m, (brownianMeshVariance t k : ℝ) *
          Real.sqrt (brownianMeshVariance t k : ℝ)) ^ 2 := by
  let := W.isProbability
  have hlaw : HasLaw (scalarSampledFieldHistory
      (fun k => scalarHiddenContinuousField z W.B (t (k + 1))) m)
      (scalarObservationHistoryLaw z (brownianMeshVariance t) m)
      (scalarHiddenBrownianLaw z W.law) :=
    scalarBrownianPriorField_history_hasLaw W.brownian.toIsPreBrownianReal z t ht ht0 m
  have he := (pathLogCoshError_hidden_eq W T t ht ht0 m hm z).mono
    (fun u hu => congrArg (fun r : ℝ => r ^ 2) hu)
  constructor
  · exact (hlaw.integrable_comp
      (integrable_scalarLogCoshHistoryError_sq z _ hdt m)).congr (by
        filter_upwards [he] with u hu
        exact hu.symm)
  · rw [integral_congr_ae he]
    exact (hlaw.integral_comp
      ((measurable_scalarLogCoshHistoryError z _ m).pow_const 2).aestronglyMeasurable).trans_le
        (scalarLogCoshHistoryError_square_bound z _ hdt m)

theorem pathLogCoshError_seed_bound (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (W : BrownianSystem Ω) (T : ℝ≥0) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (ht0 : t 0 = 0) (m : ℕ) (hm : t m ≤ T)
    (hdt : ∀ k, brownianMeshVariance t k ≤ 1) :
    Integrable (fun u : ℝ × (Bool × Ω) => (pathLogCoshError T t m
      (scalarSeedHiddenFieldPath T (brownianFinitePath W T) u)) ^ 2)
        (scalarSeedHiddenBrownianLaw ν W.law) ∧
    (∫ u : ℝ × (Bool × Ω), (pathLogCoshError T t m
      (scalarSeedHiddenFieldPath T (brownianFinitePath W T) u)) ^ 2
        ∂scalarSeedHiddenBrownianLaw ν W.law) ≤
      12 * (∑ k ∈ Finset.range m, (brownianMeshVariance t k : ℝ) ^ 2) +
        18 * (∑ k ∈ Finset.range m, (brownianMeshVariance t k : ℝ) *
          Real.sqrt (brownianMeshVariance t k : ℝ)) ^ 2 := by
  let := W.isProbability
  let E : ℝ × (Bool × Ω) → ℝ := fun u => (pathLogCoshError T t m
    (scalarSeedHiddenFieldPath T (brownianFinitePath W T) u)) ^ 2
  let C := 12 * (∑ k ∈ Finset.range m, (brownianMeshVariance t k : ℝ) ^ 2) +
    18 * (∑ k ∈ Finset.range m, (brownianMeshVariance t k : ℝ) *
      Real.sqrt (brownianMeshVariance t k : ℝ)) ^ 2
  have hE : Measurable E := ((continuous_pathLogCoshError T t m).measurable.comp
    (measurable_scalarSeedHiddenFieldPath T _ (measurable_brownianFinitePath W T))).pow_const 2
  have hf (z : ℝ) : Integrable (fun u => E (z, u)) (scalarHiddenBrownianKernel W.law z) ∧
      (∫ u, E (z, u) ∂scalarHiddenBrownianKernel W.law z) ≤ C :=
    pathLogCoshError_hidden_bound W T t ht ht0 m hm hdt z
  have hinner : Integrable (fun z => ∫ u, E (z, u) ∂scalarHiddenBrownianKernel W.law z) ν := by
    apply Integrable.of_bound
      (hE.stronglyMeasurable.integral_kernel_prod_right').aestronglyMeasurable C
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun u => sq_nonneg _))]
      exact (hf z).2)
  have hi : Integrable E (scalarSeedHiddenBrownianLaw ν W.law) := by
    apply (Measure.integrable_compProd_iff hE.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun z => (hf z).1), ?_⟩
    simpa only [E, Real.norm_eq_abs, abs_pow, sq_abs] using hinner
  refine ⟨hi, ?_⟩
  change (∫ u, E u ∂ν ⊗ₘ scalarHiddenBrownianKernel W.law) ≤ C
  rw [Measure.integral_compProd hi]
  exact (integral_mono hinner (integrable_const C) (fun z => (hf z).2)).trans_eq (by simp)

theorem pathLogCoshError_actual_bound (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (T : ℝ≥0) (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0)
    (m : ℕ) (hm : t m ≤ T) (hdt : ∀ k, brownianMeshVariance t k ≤ 1) :
    Integrable (fun w => (pathLogCoshError T t m (actualParisiPostEndpointPath W β T w)) ^ 2)
      W.law ∧
    (∫ w, (pathLogCoshError T t m (actualParisiPostEndpointPath W β T w)) ^ 2 ∂W.law) ≤
      12 * (∑ k ∈ Finset.range m, (brownianMeshVariance t k : ℝ) ^ 2) +
        18 * (∑ k ∈ Finset.range m, (brownianMeshVariance t k : ℝ) *
          Real.sqrt (brownianMeshVariance t k : ℝ)) ^ 2 := by
  let := W.isProbability
  have hm0 : Measurable (fun w =>
      (actualParisiPreContinuationField W β (parisiEquilibriumPhysicalEndpoint β) w,
        actualParisiPostEndpointPath W β T w)) :=
    (measurable_actualParisiPreContinuationField W β _).prodMk
      (measurable_boundedDriftRestartPath W (actualParisiFullScalarDrift β) _ T)
  have hm1 : Measurable (fun u : ℝ × (Bool × Ω) =>
      (u.1, scalarSeedHiddenFieldPath T (brownianFinitePath W T) u)) :=
    measurable_fst.prodMk (measurable_scalarSeedHiddenFieldPath T _ (measurable_brownianFinitePath W T))
  have hid : IdentDistrib
      (fun w => (actualParisiPreContinuationField W β (parisiEquilibriumPhysicalEndpoint β) w,
        actualParisiPostEndpointPath W β T w))
      (fun u : ℝ × (Bool × Ω) => (u.1, scalarSeedHiddenFieldPath T (brownianFinitePath W T) u))
      W.law (actualParisiSeedContinuationLaw W β W.law) :=
    ⟨hm0.aemeasurable, hm1.aemeasurable, actualParisiEndpointSeed_post_hidden_jointLaw W β hβ T⟩
  have hfun : Measurable (fun p : ℝ × ScalarContinuousPath T => (pathLogCoshError T t m p.2) ^ 2) :=
    ((continuous_pathLogCoshError T t m).measurable.comp measurable_snd).pow_const 2
  have hid' := hid.comp hfun
  obtain ⟨hi, hb⟩ := pathLogCoshError_seed_bound (actualParisiEndpointSeedLaw W β) W T t ht ht0 m hm hdt
  exact ⟨hid'.integrable_iff.mpr hi, hid'.integral_eq.trans_le hb⟩

def postLogCoshError (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (m : ℕ)
    (w : Ω) : ℝ :=
  ∑ k ∈ Finset.range m, scalarLogCoshItoError
    (actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β + t k) w)
    (brownianMeshVariance t k)
    (actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β + t (k + 1)) w)

theorem pathLogCoshError_actual_eq (W : BrownianSystem Ω) (β : ℝ) (T : ℝ≥0)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (m : ℕ) (hm : t m ≤ T) :
    (fun w => pathLogCoshError T t m (actualParisiPostEndpointPath W β T w)) =ᵐ[W.law]
      postLogCoshError W β t m := by
  filter_upwards [actualParisiPostEndpointPath_version W β T] with w hw
  have he (k : ℕ) (hk : k ≤ m) :
      IccExtend T.coe_nonneg (actualParisiPostEndpointPath W β T w) (t k) =
        actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β + t k) w := by
    have hkT : (t k : ℝ) ≤ T := NNReal.coe_le_coe.mpr ((ht hk).trans hm)
    have htk : (⟨(t k : ℝ), (t k).coe_nonneg⟩ : ℝ≥0) = t k := NNReal.eq rfl
    simpa only [IccExtend, Function.comp_apply,
      projIcc_of_mem _ ⟨(t k).coe_nonneg, hkT⟩, htk] using hw ⟨t k, (t k).coe_nonneg, hkT⟩
  apply Finset.sum_congr rfl
  intro k hk
  rw [he k (Finset.mem_range.mp hk).le, he (k + 1) (Finset.mem_range.mp hk)]

theorem postLogCoshError_bound (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (T : ℝ≥0) (t : ℕ → ℝ≥0) (ht : Monotone t) (ht0 : t 0 = 0)
    (m : ℕ) (hm : t m ≤ T) (hdt : ∀ k, brownianMeshVariance t k ≤ 1) :
    Integrable (fun w => (postLogCoshError W β t m w) ^ 2) W.law ∧
    (∫ w, (postLogCoshError W β t m w) ^ 2 ∂W.law) ≤
      12 * (∑ k ∈ Finset.range m, (brownianMeshVariance t k : ℝ) ^ 2) +
        18 * (∑ k ∈ Finset.range m, (brownianMeshVariance t k : ℝ) *
          Real.sqrt (brownianMeshVariance t k : ℝ)) ^ 2 := by
  obtain ⟨hi, hb⟩ := pathLogCoshError_actual_bound W β hβ T t ht ht0 m hm hdt
  have he := (pathLogCoshError_actual_eq W β T t ht m hm).mono
    (fun w hw => congrArg (fun r : ℝ => r ^ 2) hw)
  refine ⟨hi.congr he, ?_⟩
  exact (integral_congr_ae he).symm.trans_le hb

theorem uniformLogCoshBudget_le (T : ℝ≥0) (n m : ℕ)
    (hm : scalarUniformTime n m ≤ T) :
    12 * (∑ k ∈ Finset.range m,
        (brownianMeshVariance (scalarUniformTime n) k : ℝ) ^ 2) +
      18 * (∑ k ∈ Finset.range m,
        (brownianMeshVariance (scalarUniformTime n) k : ℝ) *
          Real.sqrt (brownianMeshVariance (scalarUniformTime n) k : ℝ)) ^ 2 ≤
      (12 * (T : ℝ) + 18 * (T : ℝ) ^ 2) / ((n : ℝ) + 1) := by
  let q : ℝ := 1 / ((n : ℝ) + 1)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have heq : (∑ k ∈ Finset.range m,
      (brownianMeshVariance (scalarUniformTime n) k : ℝ) ^ 2) = (m : ℝ) * q ^ 2 := by
    simp [brownianMeshVariance_scalarUniformTime, q]
  have heq' : (∑ k ∈ Finset.range m,
      (brownianMeshVariance (scalarUniformTime n) k : ℝ) *
        Real.sqrt (brownianMeshVariance (scalarUniformTime n) k : ℝ)) =
      (m : ℝ) * q * Real.sqrt q := by
    simp [brownianMeshVariance_scalarUniformTime, q, mul_assoc]
  rw [heq, heq']
  have hx : (m : ℝ) * q ≤ T := by
    simpa only [scalarUniformTime_coe, q, mul_one_div] using NNReal.coe_le_coe.mpr hm
  have hx0 : 0 ≤ (m : ℝ) * q := mul_nonneg (Nat.cast_nonneg _) hq
  have hx2 := (sq_le_sq₀ hx0 T.coe_nonneg).2 hx
  calc
    _ = (12 * ((m : ℝ) * q) + 18 * ((m : ℝ) * q) ^ 2) * q := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hq]
      ring
    _ ≤ (12 * (T : ℝ) + 18 * (T : ℝ) ^ 2) * q :=
      mul_le_mul_of_nonneg_right (by linarith) hq
    _ = _ := by dsimp [q]; rw [mul_one_div]

theorem postUniformLogCoshError_tendsto_L2 (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (T : ℝ≥0) :
    (∀ n, Integrable (fun w =>
      (postLogCoshError W β (scalarUniformTime n) ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ w) ^ 2) W.law) ∧
    Tendsto (fun n => ∫ w,
      (postLogCoshError W β (scalarUniformTime n) ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ w) ^ 2 ∂W.law)
        atTop (𝓝 0) := by
  have hm (n : ℕ) : scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ ≤ T := by
    apply NNReal.coe_le_coe.mp
    rw [scalarUniformTime_coe]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    simpa only [mul_comm] using Nat.floor_le (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) * (T : ℝ))
  have hb (n : ℕ) := postLogCoshError_bound W β hβ T (scalarUniformTime n)
    (scalarUniformTime_monotone n) (scalarUniformTime_zero n) _ (hm n) (scalarUniformMeshVariance_le_one n)
  refine ⟨fun n => (hb n).1, ?_⟩
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => sq_nonneg _))
    (fun n => (hb n).2.trans (uniformLogCoshBudget_le T n _ (hm n)))
  simpa only [mul_zero, mul_one_div] using
    ((tendsto_const_nhds : Tendsto
      (fun _ : ℕ => 12 * (T : ℝ) + 18 * (T : ℝ) ^ 2) atTop
      (𝓝 (12 * (T : ℝ) + 18 * (T : ℝ) ^ 2))).mul
        tendsto_one_div_add_atTop_nhds_zero_nat)

theorem signedLogCosh_cell (b : Bool) (y z : ℝ) (dt : ℝ≥0) :
    (scalarHiddenSign b - Real.tanh y) * scalarInnovation y dt z -
        (dt : ℝ) / 2 * (scalarHiddenSign b - Real.tanh y) ^ 2 -
        ((scalarHiddenSign b * z - scalarLogCosh z) -
          (scalarHiddenSign b * y - scalarLogCosh y)) =
      scalarLogCoshItoError y dt z := by
  cases b <;> simp only [scalarHiddenSign, Bool.false_eq_true, ↓reduceIte] <;>
    dsimp only [scalarLogCoshItoError, scalarInnovation] <;> ring

theorem signedLogCosh_sum (b : Bool) (Y : ℕ → ℝ) (dt : ℕ → ℝ≥0) (m : ℕ) :
    (∑ k ∈ Finset.range m,
      ((scalarHiddenSign b - Real.tanh (Y k)) * scalarInnovation (Y k) (dt k) (Y (k + 1)) -
        (dt k : ℝ) / 2 * (scalarHiddenSign b - Real.tanh (Y k)) ^ 2)) -
      ((scalarHiddenSign b * Y m - scalarLogCosh (Y m)) -
        (scalarHiddenSign b * Y 0 - scalarLogCosh (Y 0))) =
      ∑ k ∈ Finset.range m, scalarLogCoshItoError (Y k) (dt k) (Y (k + 1)) := by
  have he := Finset.sum_congr (s₁ := Finset.range m) rfl
    (fun k _ => signedLogCosh_cell b (Y k) (Y (k + 1)) (dt k))
  rw [Finset.sum_sub_distrib,
    Finset.sum_range_sub (fun k => scalarHiddenSign b * Y k - scalarLogCosh (Y k)) m] at he
  exact he

def postSignedEulerSum (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (m : ℕ)
    (b : Bool) (w : Ω) : ℝ :=
  let Y := fun k => actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β + t k) w
  ∑ k ∈ Finset.range m,
    ((scalarHiddenSign b - Real.tanh (Y k)) * scalarInnovation (Y k) (brownianMeshVariance t k) (Y (k + 1)) -
      (brownianMeshVariance t k : ℝ) / 2 * (scalarHiddenSign b - Real.tanh (Y k)) ^ 2)

theorem postSignedEulerSum_error_eq (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (m : ℕ) (b : Bool) (w : Ω) :
    postSignedEulerSum W β t m b w -
      ((scalarHiddenSign b * actualParisiFullScalarProcess W β
          (parisiEquilibriumPhysicalEndpoint β + t m) w -
        scalarLogCosh (actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β + t m) w)) -
      (scalarHiddenSign b * actualParisiFullScalarProcess W β
          (parisiEquilibriumPhysicalEndpoint β + t 0) w -
        scalarLogCosh (actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β + t 0) w))) =
      postLogCoshError W β t m w :=
  signedLogCosh_sum b _ _ m

end SKConstants.Completion.S33aA
