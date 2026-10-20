module

public import SKConstants.ScalarProcessHistory
public import SKConstants.ScalarProcessItoApproximation

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

structure ScalarCenteredIncrementFamily (dt : ℕ → ℝ≥0) where
  value : ℕ → ℝ → ℝ → ℝ
  bound : ℕ → ℝ
  measurable : ∀ k, Measurable (fun p : ℝ × ℝ => value k p.1 p.2)
  integrable : ∀ k z, Integrable (value k z) (scalarTransitionKernel (dt k) z)
  integrable_sq : ∀ k z, Integrable (fun y => value k z y ^ 2)
    (scalarTransitionKernel (dt k) z)
  mean_zero : ∀ k z, (∫ y, value k z y ∂scalarTransitionKernel (dt k) z) = 0
  second_le : ∀ k z, (∫ y, value k z y ^ 2 ∂scalarTransitionKernel (dt k) z) ≤ bound k

def scalarCenteredHistorySum (z : ℝ) (dt : ℕ → ℝ≥0)
    (F : ScalarCenteredIncrementFamily dt) : (n : ℕ) → ScalarObservationHistory n → ℝ :=
  Nat.rec (fun _ => 0) (fun n previous h => previous h.1 +
      F.value n (scalarLastField z n h.1) h.2)

def scalarCenteredHistoryStep (z : ℝ) (dt : ℕ → ℝ≥0)
    (F : ScalarCenteredIncrementFamily dt) (n : ℕ) (h : ScalarObservationHistory (n + 1)) : ℝ :=
  F.value n (scalarLastField z n h.1) h.2

theorem measurable_scalarCenteredHistoryStep (z : ℝ) (dt : ℕ → ℝ≥0)
    (F : ScalarCenteredIncrementFamily dt) (n : ℕ) :
    Measurable (scalarCenteredHistoryStep z dt F n) :=
  (F.measurable n).comp
    (((measurable_scalarLastField z n).comp measurable_fst).prodMk measurable_snd)

theorem measurable_scalarCenteredHistorySum (z : ℝ) (dt : ℕ → ℝ≥0)
    (F : ScalarCenteredIncrementFamily dt) (n : ℕ) :
    Measurable (scalarCenteredHistorySum z dt F n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (ih.comp measurable_fst).add (measurable_scalarCenteredHistoryStep z dt F n)

theorem integrable_scalarCenteredHistoryStep_sq (z : ℝ) (dt : ℕ → ℝ≥0)
    (F : ScalarCenteredIncrementFamily dt) (n : ℕ) :
    Integrable (fun h => scalarCenteredHistoryStep z dt F n h ^ 2)
      (scalarObservationHistoryLaw z dt (n + 1)) := by
  change Integrable _
    (scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n)
  apply (Measure.integrable_compProd_iff
    (f := fun h : ScalarObservationHistory n × ℝ => scalarCenteredHistoryStep z dt F n h ^ 2)
    ((measurable_scalarCenteredHistoryStep z dt F n).pow_const 2).aestronglyMeasurable).2
  constructor
  · exact ae_of_all _ (fun h => F.integrable_sq n (scalarLastField z n h))
  · have hm : StronglyMeasurable (fun h : ScalarObservationHistory n =>
        ∫ y, ‖scalarCenteredHistoryStep z dt F n (h, y) ^ 2‖
          ∂scalarObservationStepKernel z (dt n) n h) :=
      ((measurable_scalarCenteredHistoryStep z dt F n).pow_const 2).norm.stronglyMeasurable
        |>.integral_kernel_prod_right'
    apply (integrable_const (F.bound n)).mono' hm.aestronglyMeasurable
    apply ae_of_all
    intro h
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    have he : (fun y => ‖scalarCenteredHistoryStep z dt F n (h, y) ^ 2‖) =
        fun y => F.value n (scalarLastField z n h) y ^ 2 := by
      funext y
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rfl
    rw [he, scalarObservationStepKernel_apply]
    exact F.second_le n (scalarLastField z n h)

theorem integrable_scalarCenteredHistoryStep (z : ℝ) (dt : ℕ → ℝ≥0)
    (F : ScalarCenteredIncrementFamily dt) (n : ℕ) :
    Integrable (scalarCenteredHistoryStep z dt F n) (scalarObservationHistoryLaw z dt (n + 1)) := by
  apply ((integrable_scalarCenteredHistoryStep_sq z dt F n).add (integrable_const 1)).mono'
    (measurable_scalarCenteredHistoryStep z dt F n).aestronglyMeasurable
  apply ae_of_all
  intro h
  rw [Real.norm_eq_abs]
  change |scalarCenteredHistoryStep z dt F n h| ≤ scalarCenteredHistoryStep z dt F n h ^ 2 + 1
  nlinarith [sq_nonneg (|scalarCenteredHistoryStep z dt F n h| - 1),
    sq_abs (scalarCenteredHistoryStep z dt F n h)]

theorem integrable_scalarCenteredHistorySum (z : ℝ) (dt : ℕ → ℝ≥0)
    (F : ScalarCenteredIncrementFamily dt) (n : ℕ) :
    Integrable (scalarCenteredHistorySum z dt F n) (scalarObservationHistoryLaw z dt n) := by
  induction n with
  | zero => exact integrable_const 0
  | succ n ih =>
    exact (integrable_scalarHistoryLift z dt n _ (measurable_scalarCenteredHistorySum z dt F n)
      ih).add (integrable_scalarCenteredHistoryStep z dt F n)

theorem integrable_scalarCenteredHistorySum_sq (z : ℝ) (dt : ℕ → ℝ≥0)
    (F : ScalarCenteredIncrementFamily dt) (n : ℕ) :
    Integrable (fun h => scalarCenteredHistorySum z dt F n h ^ 2)
      (scalarObservationHistoryLaw z dt n) := by
  induction n with
  | zero => simp [scalarCenteredHistorySum]
  | succ n ih =>
    have hp := integrable_scalarHistoryLift z dt n _
      ((measurable_scalarCenteredHistorySum z dt F n).pow_const 2) ih
    have hj := integrable_scalarCenteredHistoryStep_sq z dt F n
    have hb : Integrable (fun h : ScalarObservationHistory (n + 1) =>
        2 * scalarCenteredHistorySum z dt F n h.1 ^ 2 +
          2 * scalarCenteredHistoryStep z dt F n h ^ 2)
        (scalarObservationHistoryLaw z dt (n + 1)) := (hp.const_mul 2).add (hj.const_mul 2)
    apply hb.mono' ((measurable_scalarCenteredHistorySum z dt F (n + 1)).pow_const 2).aestronglyMeasurable
    apply ae_of_all
    intro h
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (scalarCenteredHistorySum z dt F n h.1 + scalarCenteredHistoryStep z dt F n h) ^ 2 ≤ _
    nlinarith [sq_nonneg (scalarCenteredHistorySum z dt F n h.1 - scalarCenteredHistoryStep z dt F n h)]

theorem integrable_scalarCenteredHistoryCross (z : ℝ) (dt : ℕ → ℝ≥0)
    (F : ScalarCenteredIncrementFamily dt) (n : ℕ) :
    Integrable (fun h : ScalarObservationHistory (n + 1) =>
      scalarCenteredHistorySum z dt F n h.1 * scalarCenteredHistoryStep z dt F n h)
      (scalarObservationHistoryLaw z dt (n + 1)) := by
  have hp := integrable_scalarHistoryLift z dt n _
    ((measurable_scalarCenteredHistorySum z dt F n).pow_const 2)
    (integrable_scalarCenteredHistorySum_sq z dt F n)
  have hj := integrable_scalarCenteredHistoryStep_sq z dt F n
  apply (hp.add hj).mono'
    (((measurable_scalarCenteredHistorySum z dt F n).comp measurable_fst).mul
      (measurable_scalarCenteredHistoryStep z dt F n)).aestronglyMeasurable
  apply ae_of_all
  intro h
  rw [Real.norm_eq_abs]
  change |scalarCenteredHistorySum z dt F n h.1 * scalarCenteredHistoryStep z dt F n h| ≤
    scalarCenteredHistorySum z dt F n h.1 ^ 2 + scalarCenteredHistoryStep z dt F n h ^ 2
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg
    (scalarCenteredHistorySum z dt F n h.1 - scalarCenteredHistoryStep z dt F n h),
    sq_nonneg (scalarCenteredHistorySum z dt F n h.1 + scalarCenteredHistoryStep z dt F n h)]

theorem integral_scalarCenteredHistoryCross_eq_zero (z : ℝ) (dt : ℕ → ℝ≥0)
    (F : ScalarCenteredIncrementFamily dt) (n : ℕ) :
    (∫ h : ScalarObservationHistory (n + 1),
      scalarCenteredHistorySum z dt F n h.1 * scalarCenteredHistoryStep z dt F n h
      ∂scalarObservationHistoryLaw z dt (n + 1)) = 0 := by
  change (∫ h : ScalarObservationHistory n × ℝ,
    scalarCenteredHistorySum z dt F n h.1 * scalarCenteredHistoryStep z dt F n h
    ∂scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n) = 0
  rw [Measure.integral_compProd (integrable_scalarCenteredHistoryCross z dt F n)]
  simp only [scalarCenteredHistoryStep, scalarObservationStepKernel_apply, integral_const_mul, F.mean_zero, mul_zero, integral_zero]

theorem integral_scalarCenteredHistoryStep_sq_le (z : ℝ) (dt : ℕ → ℝ≥0)
    (F : ScalarCenteredIncrementFamily dt) (n : ℕ) :
    (∫ h, scalarCenteredHistoryStep z dt F n h ^ 2
      ∂scalarObservationHistoryLaw z dt (n + 1)) ≤ F.bound n := by
  change (∫ h : ScalarObservationHistory n × ℝ,
    scalarCenteredHistoryStep z dt F n h ^ 2
    ∂scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n) ≤ _
  rw [Measure.integral_compProd (integrable_scalarCenteredHistoryStep_sq z dt F n)]
  simp only [scalarCenteredHistoryStep, scalarObservationStepKernel_apply]
  have hb : ∀ᵐ h ∂scalarObservationHistoryLaw z dt n,
      ‖∫ y, F.value n (scalarLastField z n h) y ^ 2
        ∂scalarTransitionKernel (dt n) (scalarLastField z n h)‖ ≤ F.bound n := by
    apply ae_of_all
    intro h
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => sq_nonneg _))]
    exact F.second_le n (scalarLastField z n h)
  have hn := norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs] at hn
  exact (le_abs_self _).trans (by simpa using hn)

theorem integral_scalarCenteredHistorySum_sq_le (z : ℝ) (dt : ℕ → ℝ≥0)
    (F : ScalarCenteredIncrementFamily dt) (n : ℕ) :
    (∫ h, scalarCenteredHistorySum z dt F n h ^ 2
      ∂scalarObservationHistoryLaw z dt n) ≤ ∑ k ∈ Finset.range n, F.bound k := by
  induction n with
  | zero => simp [scalarCenteredHistorySum]
  | succ n ih =>
    have hp := integrable_scalarHistoryLift z dt n _
      ((measurable_scalarCenteredHistorySum z dt F n).pow_const 2)
      (integrable_scalarCenteredHistorySum_sq z dt F n)
    have hc := (integrable_scalarCenteredHistoryCross z dt F n).const_mul 2
    have hj := integrable_scalarCenteredHistoryStep_sq z dt F n
    have he : (fun h : ScalarObservationHistory (n + 1) => scalarCenteredHistorySum z dt F (n + 1) h ^ 2) =
        fun h => scalarCenteredHistorySum z dt F n h.1 ^ 2 +
          2 * (scalarCenteredHistorySum z dt F n h.1 * scalarCenteredHistoryStep z dt F n h) +
          scalarCenteredHistoryStep z dt F n h ^ 2 := by
      funext h
      change (_ + _) ^ 2 = _
      simp only [scalarCenteredHistoryStep, scalarCenteredHistorySum]
      ring
    rw [he, integral_add
      (f := fun h : ScalarObservationHistory (n + 1) => scalarCenteredHistorySum z dt F n h.1 ^ 2 +
        2 * (scalarCenteredHistorySum z dt F n h.1 * scalarCenteredHistoryStep z dt F n h))
      (g := fun h : ScalarObservationHistory (n + 1) => scalarCenteredHistoryStep z dt F n h ^ 2)
      (hp.add hc) hj, integral_add
      (f := fun h : ScalarObservationHistory (n + 1) => scalarCenteredHistorySum z dt F n h.1 ^ 2)
      (g := fun h : ScalarObservationHistory (n + 1) =>
        2 * (scalarCenteredHistorySum z dt F n h.1 * scalarCenteredHistoryStep z dt F n h))
      hp hc, integral_const_mul,
      integral_scalarCenteredHistoryCross_eq_zero, mul_zero, add_zero,
      integral_scalarHistoryLift z dt n _ ((measurable_scalarCenteredHistorySum z dt F n).pow_const 2)
        (integrable_scalarCenteredHistorySum_sq z dt F n), Finset.sum_range_succ]
    exact add_le_add ih (integral_scalarCenteredHistoryStep_sq_le z dt F n)

end SKConstants
