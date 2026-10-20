module

public import SKConstants.ScalarProcessCenteredHistory
public import SKConstants.ScalarProcessUniformMesh

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

theorem measurable_uncurry_scalarPosteriorItoError (t : ℝ≥0) :
    Measurable (fun p : ℝ × ℝ => scalarPosteriorItoError p.1 t p.2) := by
  unfold scalarPosteriorItoError scalarPosteriorIncrement
  exact ((measurable_scalarTanh.comp measurable_snd).sub
    (measurable_scalarTanh.comp measurable_fst)).sub
      ((measurable_scalarDefect.comp measurable_fst).mul (measurable_scalarInnovation t))

def scalarPosteriorItoIncrementFamily (dt : ℕ → ℝ≥0) (ht : ∀ k, dt k ≤ 1) :
    ScalarCenteredIncrementFamily dt where
  value := fun k z y => scalarPosteriorItoError z (dt k) y
  bound := fun k => 82 * (dt k : ℝ) ^ 2
  measurable := fun k => measurable_uncurry_scalarPosteriorItoError (dt k)
  integrable := fun k z => integrable_scalarPosteriorItoError z (dt k)
  integrable_sq := fun k z => integrable_scalarPosteriorItoError_sq z (dt k)
  mean_zero := fun k z => integral_scalarPosteriorItoError_eq_zero z (dt k)
  second_le := fun k z => integral_scalarPosteriorItoError_sq_le z (dt k) (ht k)

def scalarPosteriorIntegralSum (z : ℝ) (dt : ℕ → ℝ≥0) :
    (n : ℕ) → ScalarObservationHistory n → ℝ :=
  Nat.rec (fun _ => 0) (fun n previous h => previous h.1 +
    scalarDefect (scalarLastField z n h.1) * scalarInnovation (scalarLastField z n h.1) (dt n) h.2)

theorem measurable_scalarPosteriorIntegralSum (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    Measurable (scalarPosteriorIntegralSum z dt n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp measurable_fst).add
      (((measurable_scalarDefect.comp (measurable_scalarLastField z n)).comp measurable_fst).mul
        (measurable_scalarHistoryInnovationStep z (dt n) n))

theorem scalarCenteredHistorySum_posteriorIto_eq (z : ℝ) (dt : ℕ → ℝ≥0)
    (ht : ∀ k, dt k ≤ 1) (n : ℕ) (h : ScalarObservationHistory n) :
    scalarCenteredHistorySum z dt (scalarPosteriorItoIncrementFamily dt ht) n h =
      Real.tanh (scalarLastField z n h) - Real.tanh z - scalarPosteriorIntegralSum z dt n h := by
  induction n with
  | zero => simp [scalarCenteredHistorySum, scalarLastField, scalarPosteriorIntegralSum]
  | succ n ih =>
    change scalarCenteredHistorySum z dt (scalarPosteriorItoIncrementFamily dt ht) n h.1 +
      scalarPosteriorItoError (scalarLastField z n h.1) (dt n) h.2 = _
    rw [ih h.1]
    unfold scalarPosteriorItoError scalarPosteriorIncrement
    change _ = Real.tanh h.2 - Real.tanh z -
      (scalarPosteriorIntegralSum z dt n h.1 +
        scalarDefect (scalarLastField z n h.1) * scalarInnovation (scalarLastField z n h.1) (dt n) h.2)
    ring

theorem scalarPosteriorIntegralSum_square_error (z : ℝ) (dt : ℕ → ℝ≥0)
    (ht : ∀ k, dt k ≤ 1) (n : ℕ) :
    (∫ h, (Real.tanh (scalarLastField z n h) - Real.tanh z - scalarPosteriorIntegralSum z dt n h) ^ 2
      ∂scalarObservationHistoryLaw z dt n) ≤ 82 * ∑ k ∈ Finset.range n, (dt k : ℝ) ^ 2 := by
  have h := integral_scalarCenteredHistorySum_sq_le z dt (scalarPosteriorItoIncrementFamily dt ht) n
  simp_rw [scalarCenteredHistorySum_posteriorIto_eq] at h
  simpa only [scalarPosteriorItoIncrementFamily, Finset.mul_sum] using h

theorem integrable_scalarPosteriorIntegralSum_square_error (z : ℝ) (dt : ℕ → ℝ≥0)
    (ht : ∀ k, dt k ≤ 1) (n : ℕ) :
    Integrable (fun h =>
      (Real.tanh (scalarLastField z n h) - Real.tanh z - scalarPosteriorIntegralSum z dt n h) ^ 2)
      (scalarObservationHistoryLaw z dt n) := by
  have h := integrable_scalarCenteredHistorySum_sq z dt (scalarPosteriorItoIncrementFamily dt ht) n
  simpa only [scalarCenteredHistorySum_posteriorIto_eq] using h

def scalarUniformPosteriorIntegral {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (T : ℝ≥0) (u : Bool × Ω) : ℝ :=
  scalarPosteriorIntegralSum z (brownianMeshVariance (scalarUniformTime n))
    ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊
    (scalarUniformObservationHistory z B n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ u)

theorem scalarUniformMeshVariance_le_one (n k : ℕ) :
    brownianMeshVariance (scalarUniformTime n) k ≤ 1 := by
  rw [brownianMeshVariance_scalarUniformTime]
  exact (div_le_one (by positivity)).2 (by simp)

theorem scalarLastField_uniform {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (n m : ℕ) (u : Bool × Ω) (hzero : B 0 u.2 = 0) :
    scalarLastField z m (scalarUniformObservationHistory z B n m u) =
      scalarHiddenContinuousField z B (scalarUniformTime n m) u := by
  unfold scalarUniformObservationHistory
  exact scalarLastField_sampled
    (fun k u => scalarHiddenContinuousField z B (scalarUniformTime n k) u) z m u
    (by simp [scalarHiddenContinuousField, scalarUniformTime_zero, hzero])

theorem scalarUniformPosteriorIntegral_square_error {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) (n : ℕ) :
    (∫ u, (Real.tanh (scalarHiddenContinuousField z B
        (scalarUniformTime n ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊) u) - Real.tanh z -
        scalarUniformPosteriorIntegral z B n T u) ^ 2 ∂scalarHiddenBrownianLaw z P) ≤
      82 * (T : ℝ) / ((n : ℝ) + 1) := by
  let m := ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊
  let dt := brownianMeshVariance (scalarUniformTime n)
  have hdt : ∀ k, dt k ≤ 1 := scalarUniformMeshVariance_le_one n
  have hlaw := scalarUniformObservationHistory_hasLaw hB z n m
  have hz : ∀ᵐ u ∂scalarHiddenBrownianLaw z P, B 0 u.2 = 0 :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae
      hB.eval_zero_ae_eq_zero
  have he : (∫ u, (Real.tanh (scalarHiddenContinuousField z B (scalarUniformTime n m) u) -
      Real.tanh z - scalarUniformPosteriorIntegral z B n T u) ^ 2 ∂scalarHiddenBrownianLaw z P) =
      ∫ h, (Real.tanh (scalarLastField z m h) - Real.tanh z - scalarPosteriorIntegralSum z dt m h) ^ 2
        ∂scalarObservationHistoryLaw z dt m := by
    have hcomp := hlaw.integral_comp
      (f := fun h => (Real.tanh (scalarLastField z m h) - Real.tanh z -
        scalarPosteriorIntegralSum z dt m h) ^ 2)
      (by exact (((measurable_scalarTanh.comp (measurable_scalarLastField z m)).sub_const
        (Real.tanh z)).sub (measurable_scalarPosteriorIntegralSum z dt m) |>.pow_const 2).aestronglyMeasurable)
    rw [← hcomp]
    apply integral_congr_ae
    filter_upwards [hz] with u hu
    simp only [Function.comp_def, scalarLastField_uniform z B n m u hu]
    rfl
  change (∫ u, (Real.tanh (scalarHiddenContinuousField z B (scalarUniformTime n m) u) -
    Real.tanh z - scalarUniformPosteriorIntegral z B n T u) ^ 2 ∂scalarHiddenBrownianLaw z P) ≤ _
  rw [he]
  apply (scalarPosteriorIntegralSum_square_error z dt hdt m).trans
  have hfloor : (m : ℝ) ≤ ((n : ℝ) + 1) * (T : ℝ) := Nat.floor_le (by positivity)
  have hp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsum : (∑ k ∈ Finset.range m, (dt k : ℝ) ^ 2) = (m : ℝ) * (1 / ((n : ℝ) + 1)) ^ 2 := by
    simp only [dt, brownianMeshVariance_scalarUniformTime, NNReal.coe_div, NNReal.coe_one,
      NNReal.coe_add, NNReal.coe_natCast]
    simp
  rw [hsum]
  calc
    _ = 82 * (m : ℝ) * (1 / ((n : ℝ) + 1)) ^ 2 := by ring
    _ ≤ 82 * (((n : ℝ) + 1) * (T : ℝ)) * (1 / ((n : ℝ) + 1)) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfloor (by norm_num)) (sq_nonneg _)
    _ = _ := by field_simp

end SKConstants
