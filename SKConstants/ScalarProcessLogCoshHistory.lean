module
public import SKConstants.ScalarProcessLogCosh
public import SKConstants.ScalarProcessPosteriorIntegral
import Mathlib.Tactic

public section
noncomputable section
namespace SKConstants
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators
set_option backward.isDefEq.respectTransparency false

def scalarLogCoshCenteredFamily (dt : ℕ → ℝ≥0) (ht : ∀ k, dt k ≤ 1) :
    ScalarCenteredIncrementFamily dt where
  value := fun k z y => scalarCenteredLogCoshItoError z (dt k) y
  bound := fun k => 6 * (dt k : ℝ) ^ 2
  measurable := fun k => measurable_scalarCenteredLogCoshItoError_uncurry (dt k)
  integrable := fun k z => integrable_scalarCenteredLogCoshItoError z (dt k)
  integrable_sq := fun k z => integrable_scalarCenteredLogCoshItoError_sq z (dt k)
  mean_zero := fun k z => integral_scalarCenteredLogCoshItoError_eq_zero z (dt k)
  second_le := fun k z => integral_scalarCenteredLogCoshItoError_sq_le z (dt k) (ht k)

@[expose] def scalarLogCoshHistoryError (z : ℝ) (dt : ℕ → ℝ≥0) :
    (n : ℕ) → ScalarObservationHistory n → ℝ :=
  Nat.rec (fun _ => 0) (fun n previous h => previous h.1 +
    scalarLogCoshItoError (scalarLastField z n h.1) (dt n) h.2)

@[expose] def scalarLogCoshHistoryBias (z : ℝ) (dt : ℕ → ℝ≥0) :
    (n : ℕ) → ScalarObservationHistory n → ℝ :=
  Nat.rec (fun _ => 0) (fun n previous h => previous h.1 +
    scalarLogCoshBias (dt n) (scalarLastField z n h.1))

@[expose] def scalarLogCoshIntegralSum (z : ℝ) (dt : ℕ → ℝ≥0) :
    (n : ℕ) → ScalarObservationHistory n → ℝ :=
  Nat.rec (fun _ => 0) (fun n previous h => previous h.1 +
    Real.tanh (scalarLastField z n h.1) *
      scalarInnovation (scalarLastField z n h.1) (dt n) h.2)

@[expose] def scalarPosteriorSquareTimeSum (z : ℝ) (dt : ℕ → ℝ≥0) :
    (n : ℕ) → ScalarObservationHistory n → ℝ :=
  Nat.rec (fun _ => 0) (fun n previous h => previous h.1 +
    (dt n : ℝ) * Real.tanh (scalarLastField z n h.1) ^ 2)

theorem measurable_scalarLogCoshHistoryError (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    Measurable (scalarLogCoshHistoryError z dt n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun h : ScalarObservationHistory n × ℝ =>
      scalarLogCoshHistoryError z dt n h.1 + scalarLogCoshItoError (scalarLastField z n h.1) (dt n) h.2)
    have hm : Measurable (fun zy : ℝ × ℝ => scalarLogCoshItoError zy.1 (dt n) zy.2) :=
      (continuous_scalarLogCoshItoError_uncurry (dt n)).measurable
    have hp : Measurable (fun h : ScalarObservationHistory n × ℝ => (scalarLastField z n h.1, h.2)) :=
      ((measurable_scalarLastField z n).comp measurable_fst).prodMk measurable_snd
    have hsum := (ih.comp measurable_fst).add (hm.comp hp)
    have hfun : ((scalarLogCoshHistoryError z dt n ∘ Prod.fst) +
        ((fun zy : ℝ × ℝ => scalarLogCoshItoError zy.1 (dt n) zy.2) ∘
          (fun h : ScalarObservationHistory n × ℝ => (scalarLastField z n h.1, h.2)))) =
        (fun h : ScalarObservationHistory n × ℝ => scalarLogCoshHistoryError z dt n h.1 +
          scalarLogCoshItoError (scalarLastField z n h.1) (dt n) h.2) := by
      funext h
      rfl
    rw [hfun] at hsum
    exact hsum

theorem measurable_scalarLogCoshHistoryBias (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    Measurable (scalarLogCoshHistoryBias z dt n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp measurable_fst).add ((measurable_scalarLogCoshBias (dt n)).comp
      ((measurable_scalarLastField z n).comp measurable_fst))

theorem scalarCenteredHistorySum_logCosh_eq (z : ℝ) (dt : ℕ → ℝ≥0)
    (ht : ∀ k, dt k ≤ 1) (n : ℕ) (h : ScalarObservationHistory n) :
    scalarCenteredHistorySum z dt (scalarLogCoshCenteredFamily dt ht) n h =
      scalarLogCoshHistoryError z dt n h - scalarLogCoshHistoryBias z dt n h := by
  induction n with
  | zero => simp [scalarCenteredHistorySum, scalarLogCoshHistoryError, scalarLogCoshHistoryBias]
  | succ n ih =>
    change scalarCenteredHistorySum z dt (scalarLogCoshCenteredFamily dt ht) n h.1 +
      scalarCenteredLogCoshItoError (scalarLastField z n h.1) (dt n) h.2 = _
    rw [ih h.1]
    unfold scalarCenteredLogCoshItoError
    change _ = (scalarLogCoshHistoryError z dt n h.1 +
      scalarLogCoshItoError (scalarLastField z n h.1) (dt n) h.2) -
      (scalarLogCoshHistoryBias z dt n h.1 + scalarLogCoshBias (dt n) (scalarLastField z n h.1))
    ring

theorem scalarLogCoshHistoryBias_abs_le (z : ℝ) (dt : ℕ → ℝ≥0)
    (ht : ∀ k, dt k ≤ 1) (n : ℕ) (h : ScalarObservationHistory n) :
    |scalarLogCoshHistoryBias z dt n h| ≤
      3 * ∑ k ∈ Finset.range n, (dt k : ℝ) * Real.sqrt (dt k : ℝ) := by
  induction n with
  | zero => simp [scalarLogCoshHistoryBias]
  | succ n ih =>
    change |scalarLogCoshHistoryBias z dt n h.1 +
      scalarLogCoshBias (dt n) (scalarLastField z n h.1)| ≤ _
    rw [Finset.sum_range_succ]
    have hh := abs_add_le (scalarLogCoshHistoryBias z dt n h.1)
      (scalarLogCoshBias (dt n) (scalarLastField z n h.1))
    have hb := integral_scalarLogCoshItoError_abs_le (scalarLastField z n h.1) (dt n) (ht n)
    change |scalarLogCoshBias (dt n) (scalarLastField z n h.1)| ≤ _ at hb
    linarith [ih h.1]

theorem integrable_scalarLogCoshHistoryBias_sq (z : ℝ) (dt : ℕ → ℝ≥0)
    (ht : ∀ k, dt k ≤ 1) (n : ℕ) :
    Integrable (fun h => scalarLogCoshHistoryBias z dt n h ^ 2)
      (scalarObservationHistoryLaw z dt n) := by
  apply Integrable.of_bound ((measurable_scalarLogCoshHistoryBias z dt n).pow_const 2).aestronglyMeasurable
    ((3 * ∑ k ∈ Finset.range n, (dt k : ℝ) * Real.sqrt (dt k : ℝ)) ^ 2)
  apply ae_of_all
  intro h
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg (scalarLogCoshHistoryBias z dt n h)) (by positivity)).2
      (scalarLogCoshHistoryBias_abs_le z dt ht n h)

theorem integrable_scalarLogCoshHistoryError_sq (z : ℝ) (dt : ℕ → ℝ≥0)
    (ht : ∀ k, dt k ≤ 1) (n : ℕ) :
    Integrable (fun h => scalarLogCoshHistoryError z dt n h ^ 2)
      (scalarObservationHistoryLaw z dt n) := by
  let F := scalarLogCoshCenteredFamily dt ht
  have hic := integrable_scalarCenteredHistorySum_sq z dt F n
  have hib := integrable_scalarLogCoshHistoryBias_sq z dt ht n
  apply ((hic.const_mul 2).add (hib.const_mul 2)).mono'
    ((measurable_scalarLogCoshHistoryError z dt n).pow_const 2).aestronglyMeasurable
  apply ae_of_all
  intro h
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have he := scalarCenteredHistorySum_logCosh_eq z dt ht n h
  change scalarCenteredHistorySum z dt F n h = _ at he
  simp only [Pi.add_apply]
  have hexp : scalarLogCoshHistoryError z dt n h =
      scalarCenteredHistorySum z dt F n h + scalarLogCoshHistoryBias z dt n h := by linarith
  rw [hexp]
  nlinarith [sq_nonneg (scalarCenteredHistorySum z dt F n h - scalarLogCoshHistoryBias z dt n h)]

theorem scalarLogCoshHistoryError_square_bound (z : ℝ) (dt : ℕ → ℝ≥0)
    (ht : ∀ k, dt k ≤ 1) (n : ℕ) :
    (∫ h, scalarLogCoshHistoryError z dt n h ^ 2 ∂scalarObservationHistoryLaw z dt n) ≤
      12 * (∑ k ∈ Finset.range n, (dt k : ℝ) ^ 2) +
        18 * (∑ k ∈ Finset.range n, (dt k : ℝ) * Real.sqrt (dt k : ℝ)) ^ 2 := by
  let F := scalarLogCoshCenteredFamily dt ht
  have hic := integrable_scalarCenteredHistorySum_sq z dt F n
  have hib := integrable_scalarLogCoshHistoryBias_sq z dt ht n
  have hpoint (h : ScalarObservationHistory n) : scalarLogCoshHistoryError z dt n h ^ 2 ≤
      2 * scalarCenteredHistorySum z dt F n h ^ 2 + 2 * scalarLogCoshHistoryBias z dt n h ^ 2 := by
    have he := scalarCenteredHistorySum_logCosh_eq z dt ht n h
    change scalarCenteredHistorySum z dt F n h = _ at he
    have hexp : scalarLogCoshHistoryError z dt n h =
        scalarCenteredHistorySum z dt F n h + scalarLogCoshHistoryBias z dt n h := by linarith
    rw [hexp]
    nlinarith [sq_nonneg (scalarCenteredHistorySum z dt F n h - scalarLogCoshHistoryBias z dt n h)]
  have hh := integral_mono (integrable_scalarLogCoshHistoryError_sq z dt ht n)
    ((hic.const_mul 2).add (hib.const_mul 2)) hpoint
  change (∫ h, scalarLogCoshHistoryError z dt n h ^ 2 ∂scalarObservationHistoryLaw z dt n) ≤
    (∫ h, (2 * scalarCenteredHistorySum z dt F n h ^ 2 +
      2 * scalarLogCoshHistoryBias z dt n h ^ 2) ∂scalarObservationHistoryLaw z dt n) at hh
  rw [integral_add (hic.const_mul 2) (hib.const_mul 2), integral_const_mul, integral_const_mul] at hh
  have hc := integral_scalarCenteredHistorySum_sq_le z dt F n
  change (∫ h, scalarCenteredHistorySum z dt F n h ^ 2 ∂scalarObservationHistoryLaw z dt n) ≤
    ∑ k ∈ Finset.range n, 6 * (dt k : ℝ) ^ 2 at hc
  rw [← Finset.mul_sum] at hc
  have hb : (∫ h, scalarLogCoshHistoryBias z dt n h ^ 2 ∂scalarObservationHistoryLaw z dt n) ≤
      9 * (∑ k ∈ Finset.range n, (dt k : ℝ) * Real.sqrt (dt k : ℝ)) ^ 2 := by
    have hpt (h : ScalarObservationHistory n) : scalarLogCoshHistoryBias z dt n h ^ 2 ≤
        9 * (∑ k ∈ Finset.range n, (dt k : ℝ) * Real.sqrt (dt k : ℝ)) ^ 2 := by
      have hs := (sq_le_sq₀ (abs_nonneg (scalarLogCoshHistoryBias z dt n h)) (by positivity)).2
        (scalarLogCoshHistoryBias_abs_le z dt ht n h)
      rw [sq_abs] at hs
      nlinarith
    exact (integral_mono hib (integrable_const _) hpt).trans_eq (by simp)
  linarith

theorem scalarLogCoshHistoryError_telescope (z : ℝ) (dt : ℕ → ℝ≥0)
    (n : ℕ) (h : ScalarObservationHistory n) :
    scalarLogCoshHistoryError z dt n h = scalarLogCosh (scalarLastField z n h) - scalarLogCosh z -
      (∑ k ∈ Finset.range n, (dt k : ℝ)) / 2 - scalarLogCoshIntegralSum z dt n h -
      scalarPosteriorSquareTimeSum z dt n h / 2 := by
  induction n with
  | zero => simp [scalarLogCoshHistoryError, scalarLastField, scalarLogCoshIntegralSum,
      scalarPosteriorSquareTimeSum]
  | succ n ih =>
    change scalarLogCoshHistoryError z dt n h.1 +
      scalarLogCoshItoError (scalarLastField z n h.1) (dt n) h.2 = _
    rw [ih h.1, Finset.sum_range_succ]
    dsimp [scalarLogCoshItoError]
    change _ = scalarLogCosh h.2 - scalarLogCosh z -
      ((∑ k ∈ Finset.range n, (dt k : ℝ)) + (dt n : ℝ)) / 2 -
      (scalarLogCoshIntegralSum z dt n h.1 + Real.tanh (scalarLastField z n h.1) *
        scalarInnovation (scalarLastField z n h.1) (dt n) h.2) -
      (scalarPosteriorSquareTimeSum z dt n h.1 +
        (dt n : ℝ) * Real.tanh (scalarLastField z n h.1) ^ 2) / 2
    ring

@[expose] def scalarUniformLogCoshError {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (T : ℝ≥0) (u : Bool × Ω) : ℝ :=
  scalarLogCoshHistoryError z (brownianMeshVariance (scalarUniformTime n))
    ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊
    (scalarUniformObservationHistory z B n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u)

theorem scalarUniformLogCoshError_square_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) (n : ℕ) :
    (∫ u, scalarUniformLogCoshError z B n T u ^ 2 ∂scalarHiddenBrownianLaw z P) ≤
      (12 * (T : ℝ) + 18 * (T : ℝ) ^ 2) / ((n : ℝ) + 1) := by
  let m := ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊
  let dt := brownianMeshVariance (scalarUniformTime n)
  let q : ℝ := 1 / ((n : ℝ) + 1)
  have hdt : ∀ k, dt k ≤ 1 := scalarUniformMeshVariance_le_one n
  have hlaw := scalarUniformObservationHistory_hasLaw hB z n m
  have he : (∫ u, scalarUniformLogCoshError z B n T u ^ 2 ∂scalarHiddenBrownianLaw z P) =
      ∫ h, scalarLogCoshHistoryError z dt m h ^ 2 ∂scalarObservationHistoryLaw z dt m := by
    have hh := hlaw.integral_comp (f := fun h => scalarLogCoshHistoryError z dt m h ^ 2)
      ((measurable_scalarLogCoshHistoryError z dt m).pow_const 2).aestronglyMeasurable
    exact hh
  rw [he]
  apply (scalarLogCoshHistoryError_square_bound z dt hdt m).trans
  have hsum2 : (∑ k ∈ Finset.range m, (dt k : ℝ) ^ 2) = (m : ℝ) * q ^ 2 := by
    simp only [dt, brownianMeshVariance_scalarUniformTime, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_add, NNReal.coe_natCast]
    simp [q]
  have hsum3 : (∑ k ∈ Finset.range m, (dt k : ℝ) * Real.sqrt (dt k : ℝ)) =
      (m : ℝ) * q * Real.sqrt q := by
    simp only [dt, brownianMeshVariance_scalarUniformTime, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_add, NNReal.coe_natCast]
    simp [q, mul_assoc]
  rw [hsum2, hsum3]
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hfloor : (m : ℝ) ≤ ((n : ℝ) + 1) * (T : ℝ) := Nat.floor_le (by positivity)
  have hx : (m : ℝ) * q ≤ (T : ℝ) := by
    dsimp [q]
    rw [mul_one_div]
    exact (div_le_iff₀ hN).2 (by nlinarith [hfloor])
  have hx0 : 0 ≤ (m : ℝ) * q := mul_nonneg (Nat.cast_nonneg _) hq
  have hx2 := (sq_le_sq₀ hx0 T.coe_nonneg).2 hx
  calc
    _ = (12 * ((m : ℝ) * q) + 18 * ((m : ℝ) * q) ^ 2) * q := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hq]
      ring
    _ ≤ (12 * (T : ℝ) + 18 * (T : ℝ) ^ 2) * q :=
      mul_le_mul_of_nonneg_right (by linarith) hq
    _ = _ := by dsimp [q]; rw [mul_one_div]

theorem scalarUniformLogCoshError_tendsto_L2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    Tendsto (fun n => ∫ u, scalarUniformLogCoshError z B n T u ^ 2
      ∂scalarHiddenBrownianLaw z P) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => integral_nonneg fun _ => sq_nonneg _)
    (fun n => scalarUniformLogCoshError_square_bound P z B hB T n)
  simpa only [mul_zero, mul_one_div] using
    ((tendsto_const_nhds : Tendsto
      (fun _ : ℕ => 12 * (T : ℝ) + 18 * (T : ℝ) ^ 2) atTop
      (𝓝 (12 * (T : ℝ) + 18 * (T : ℝ) ^ 2))).mul
      tendsto_one_div_add_atTop_nhds_zero_nat)

end SKConstants
#print axioms SKConstants.scalarLogCoshHistoryError_square_bound
#print axioms SKConstants.scalarLogCoshHistoryError_telescope
#print axioms SKConstants.scalarUniformLogCoshError_tendsto_L2
