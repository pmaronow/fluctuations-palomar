module

public import SKConstants.ScalarProcessInnovation
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.MapComap

@[expose] public section
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def ScalarObservationHistory : ℕ → Type
  | 0 => PUnit
  | n + 1 => ScalarObservationHistory n × ℝ

instance scalarObservationHistoryMeasurableSpace (n : ℕ) :
    MeasurableSpace (ScalarObservationHistory n) := by
  induction n with
  | zero => exact (inferInstance : MeasurableSpace PUnit)
  | succ n ih => exact @MeasurableSpace.prod (ScalarObservationHistory n) ℝ ih inferInstance

def scalarLastField (z : ℝ) : (n : ℕ) → ScalarObservationHistory n → ℝ
  | 0, _ => z
  | _ + 1, h => h.2

theorem measurable_scalarLastField (z : ℝ) (n : ℕ) :
    Measurable (scalarLastField z n) := by
  cases n with
  | zero => exact measurable_const
  | succ n => exact measurable_snd

def scalarObservationStepKernel (z : ℝ) (t : ℝ≥0) (n : ℕ) :
    Kernel (ScalarObservationHistory n) ℝ :=
  (scalarTransitionKernel t).comap (scalarLastField z n) (measurable_scalarLastField z n)

instance scalarObservationStepKernel_isMarkov (z : ℝ) (t : ℝ≥0) (n : ℕ) :
    IsMarkovKernel (scalarObservationStepKernel z t n) := by
  unfold scalarObservationStepKernel
  infer_instance

theorem scalarObservationStepKernel_apply (z : ℝ) (t : ℝ≥0) (n : ℕ)
    (h : ScalarObservationHistory n) :
    scalarObservationStepKernel z t n h = scalarTransitionKernel t (scalarLastField z n h) :=
  rfl

def scalarObservationHistoryLaw (z : ℝ) (dt : ℕ → ℝ≥0) :
    (n : ℕ) → Measure (ScalarObservationHistory n)
  | 0 => Measure.dirac PUnit.unit
  | n + 1 => scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n

instance scalarObservationHistoryLaw_isProbability (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (scalarObservationHistoryLaw z dt n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac PUnit.unit); infer_instance
  | succ n ih =>
    change IsProbabilityMeasure
      (scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n)
    infer_instance

def scalarHistoryInnovationSum (z : ℝ) (dt : ℕ → ℝ≥0) :
    (n : ℕ) → ScalarObservationHistory n → ℝ
  | 0, _ => 0
  | n + 1, h => scalarHistoryInnovationSum z dt n h.1 +
      scalarInnovation (scalarLastField z n h.1) (dt n) h.2

theorem measurable_scalarInnovation (t : ℝ≥0) :
    Measurable (fun p : ℝ × ℝ => scalarInnovation p.1 t p.2) := by
  have hm : Measurable (fun p : ℝ × ℝ => Real.tanh p.1) := by
    have he : (fun p : ℝ × ℝ => Real.tanh p.1) =
        (Real.sinh ∘ Prod.fst) / (Real.cosh ∘ Prod.fst) := by
      funext p
      exact Real.tanh_eq_sinh_div_cosh p.1
    rw [he]
    exact (Real.measurable_sinh.comp measurable_fst).div
      (Real.measurable_cosh.comp measurable_fst)
  exact (measurable_snd.sub measurable_fst).sub (hm.const_mul (t : ℝ))

theorem measurable_scalarHistoryInnovationStep (z : ℝ) (t : ℝ≥0) (n : ℕ) :
    Measurable (fun h : ScalarObservationHistory (n + 1) =>
      scalarInnovation (scalarLastField z n h.1) t h.2) :=
  (measurable_scalarInnovation t).comp
    (((measurable_scalarLastField z n).comp measurable_fst).prodMk measurable_snd)

theorem measurable_scalarHistoryInnovationSum (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    Measurable (scalarHistoryInnovationSum z dt n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp measurable_fst).add
      (measurable_scalarHistoryInnovationStep z (dt n) n)

theorem integrable_scalarHistoryInnovationStep (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    Integrable (fun h : ScalarObservationHistory (n + 1) =>
      scalarInnovation (scalarLastField z n h.1) (dt n) h.2)
      (scalarObservationHistoryLaw z dt (n + 1)) := by
  change Integrable _
    (scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n)
  apply (Measure.integrable_compProd_iff
    (measurable_scalarHistoryInnovationStep z (dt n) n).aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall (fun h =>
      integrable_scalarInnovation_transition (scalarLastField z n h) (dt n))
  · have hm : StronglyMeasurable (fun h : ScalarObservationHistory n =>
        ∫ y, ‖scalarInnovation (scalarLastField z n h) (dt n) y‖
          ∂scalarObservationStepKernel z (dt n) n h) :=
      (measurable_scalarHistoryInnovationStep z (dt n) n).norm.stronglyMeasurable
        |>.integral_kernel_prod_right'
    apply (integrable_const (1 + (dt n : ℝ) + (dt n : ℝ) ^ 2)).mono'
      hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro h
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact integral_norm_scalarInnovation_transition (scalarLastField z n h) (dt n)

theorem integrable_scalarHistoryLift (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ)
    (f : ScalarObservationHistory n → ℝ) (hf : Measurable f)
    (hi : Integrable f (scalarObservationHistoryLaw z dt n)) :
    Integrable (fun h : ScalarObservationHistory (n + 1) => f h.1)
      (scalarObservationHistoryLaw z dt (n + 1)) := by
  change Integrable _
    (scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n)
  apply (Measure.integrable_compProd_iff
    (f := fun h : ScalarObservationHistory n × ℝ => f h.1)
    (hf.comp measurable_fst).aestronglyMeasurable).2
  constructor
  · apply Filter.Eventually.of_forall
    intro h
    change Integrable (fun _ : ℝ => f h) (scalarObservationStepKernel z (dt n) n h)
    exact integrable_const (f h)
  · simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
      one_smul] using hi.norm

theorem integrable_scalarHistoryInnovationSum (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    Integrable (scalarHistoryInnovationSum z dt n) (scalarObservationHistoryLaw z dt n) := by
  induction n with
  | zero => exact integrable_const 0
  | succ n ih =>
    exact (integrable_scalarHistoryLift z dt n _ (measurable_scalarHistoryInnovationSum z dt n)
      ih).add (integrable_scalarHistoryInnovationStep z dt n)

theorem integral_scalarHistoryInnovationStep (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    (∫ h : ScalarObservationHistory (n + 1),
      scalarInnovation (scalarLastField z n h.1) (dt n) h.2
      ∂scalarObservationHistoryLaw z dt (n + 1)) = 0 := by
  change (∫ h : ScalarObservationHistory n × ℝ,
    scalarInnovation (scalarLastField z n h.1) (dt n) h.2
    ∂scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n) = 0
  rw [Measure.integral_compProd (integrable_scalarHistoryInnovationStep z dt n)]
  simp only [scalarObservationStepKernel_apply, integral_scalarInnovation_transition,
    integral_zero]

theorem integral_scalarHistoryLift (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ)
    (f : ScalarObservationHistory n → ℝ) (hf : Measurable f)
    (hi : Integrable f (scalarObservationHistoryLaw z dt n)) :
    (∫ h : ScalarObservationHistory (n + 1), f h.1
      ∂scalarObservationHistoryLaw z dt (n + 1)) =
      ∫ h, f h ∂scalarObservationHistoryLaw z dt n := by
  change (∫ h : ScalarObservationHistory n × ℝ, f h.1
    ∂scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n) = _
  rw [Measure.integral_compProd (integrable_scalarHistoryLift z dt n f hf hi)]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

theorem integral_scalarHistoryInnovationSum_eq_zero (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    (∫ h, scalarHistoryInnovationSum z dt n h
      ∂scalarObservationHistoryLaw z dt n) = 0 := by
  induction n with
  | zero => simp [scalarHistoryInnovationSum]
  | succ n ih =>
    change (∫ h : ScalarObservationHistory (n + 1),
      scalarHistoryInnovationSum z dt n h.1 +
        scalarInnovation (scalarLastField z n h.1) (dt n) h.2
      ∂scalarObservationHistoryLaw z dt (n + 1)) = 0
    rw [integral_add
      (integrable_scalarHistoryLift z dt n _ (measurable_scalarHistoryInnovationSum z dt n)
        (integrable_scalarHistoryInnovationSum z dt n))
      (integrable_scalarHistoryInnovationStep z dt n),
      integral_scalarHistoryLift z dt n _ (measurable_scalarHistoryInnovationSum z dt n)
        (integrable_scalarHistoryInnovationSum z dt n),
      integral_scalarHistoryInnovationStep, ih, add_zero]

theorem integrable_scalarHistoryInnovationStep_sq (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    Integrable (fun h : ScalarObservationHistory (n + 1) =>
      (scalarInnovation (scalarLastField z n h.1) (dt n) h.2) ^ 2)
      (scalarObservationHistoryLaw z dt (n + 1)) := by
  change Integrable _
    (scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n)
  apply (Measure.integrable_compProd_iff
    (f := fun h : ScalarObservationHistory n × ℝ =>
      (scalarInnovation (scalarLastField z n h.1) (dt n) h.2) ^ 2)
    ((measurable_scalarHistoryInnovationStep z (dt n) n).pow_const 2).aestronglyMeasurable).2
  constructor
  · exact Filter.Eventually.of_forall (fun h =>
      integrable_scalarInnovation_sq_transition (scalarLastField z n h) (dt n))
  · have hm : StronglyMeasurable (fun h : ScalarObservationHistory n =>
        ∫ y, ‖(scalarInnovation (scalarLastField z n h) (dt n) y) ^ 2‖
          ∂scalarObservationStepKernel z (dt n) n h) :=
      ((measurable_scalarHistoryInnovationStep z (dt n) n).pow_const 2).norm.stronglyMeasurable
        |>.integral_kernel_prod_right'
    apply (integrable_const ((dt n : ℝ) + (dt n : ℝ) ^ 2)).mono'
      hm.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro h
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    have he : (fun y => ‖(scalarInnovation (scalarLastField z n h) (dt n) y) ^ 2‖) =
        (fun y => (scalarInnovation (scalarLastField z n h) (dt n) y) ^ 2) := by
      funext y
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [he]
    rw [scalarObservationStepKernel_apply, integral_scalarInnovation_sq_transition]
    have hd := mul_le_mul_of_nonneg_left
      (scalarDefect_le_one (scalarLastField z n h)) (sq_nonneg (dt n : ℝ))
    nlinarith

theorem integrable_scalarHistoryInnovationSum_sq (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    Integrable (fun h => (scalarHistoryInnovationSum z dt n h) ^ 2)
      (scalarObservationHistoryLaw z dt n) := by
  induction n with
  | zero => simp [scalarHistoryInnovationSum]
  | succ n ih =>
    have hp := integrable_scalarHistoryLift z dt n _
      ((measurable_scalarHistoryInnovationSum z dt n).pow_const 2) ih
    have hj := integrable_scalarHistoryInnovationStep_sq z dt n
    have hb : Integrable (fun h : ScalarObservationHistory (n + 1) =>
        2 * (scalarHistoryInnovationSum z dt n h.1) ^ 2 +
          2 * (scalarInnovation (scalarLastField z n h.1) (dt n) h.2) ^ 2)
        (scalarObservationHistoryLaw z dt (n + 1)) :=
      (hp.const_mul 2).add (hj.const_mul 2)
    apply hb.mono'
      ((measurable_scalarHistoryInnovationSum z dt (n + 1)).pow_const 2).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro h
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [scalarHistoryInnovationSum]
    nlinarith [sq_nonneg (scalarHistoryInnovationSum z dt n h.1 -
      scalarInnovation (scalarLastField z n h.1) (dt n) h.2)]

theorem integrable_scalarHistoryInnovationCross (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    Integrable (fun h : ScalarObservationHistory (n + 1) =>
      scalarHistoryInnovationSum z dt n h.1 *
        scalarInnovation (scalarLastField z n h.1) (dt n) h.2)
      (scalarObservationHistoryLaw z dt (n + 1)) := by
  have hp := integrable_scalarHistoryLift z dt n _
    ((measurable_scalarHistoryInnovationSum z dt n).pow_const 2)
    (integrable_scalarHistoryInnovationSum_sq z dt n)
  have hj := integrable_scalarHistoryInnovationStep_sq z dt n
  have hb : Integrable (fun h : ScalarObservationHistory (n + 1) =>
      (scalarHistoryInnovationSum z dt n h.1) ^ 2 +
        (scalarInnovation (scalarLastField z n h.1) (dt n) h.2) ^ 2)
      (scalarObservationHistoryLaw z dt (n + 1)) := hp.add hj
  apply hb.mono'
    (((measurable_scalarHistoryInnovationSum z dt n).comp measurable_fst).mul
      (measurable_scalarHistoryInnovationStep z (dt n) n)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro h
  rw [Real.norm_eq_abs]
  change |scalarHistoryInnovationSum z dt n h.1 *
    scalarInnovation (scalarLastField z n h.1) (dt n) h.2| ≤
    (scalarHistoryInnovationSum z dt n h.1) ^ 2 +
      (scalarInnovation (scalarLastField z n h.1) (dt n) h.2) ^ 2
  apply abs_le.mpr
  constructor <;>
    nlinarith [sq_nonneg (scalarHistoryInnovationSum z dt n h.1 -
      scalarInnovation (scalarLastField z n h.1) (dt n) h.2),
      sq_nonneg (scalarHistoryInnovationSum z dt n h.1 +
      scalarInnovation (scalarLastField z n h.1) (dt n) h.2)]

theorem integral_scalarHistoryInnovationCross_eq_zero (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    (∫ h : ScalarObservationHistory (n + 1),
      scalarHistoryInnovationSum z dt n h.1 *
        scalarInnovation (scalarLastField z n h.1) (dt n) h.2
      ∂scalarObservationHistoryLaw z dt (n + 1)) = 0 := by
  change (∫ h : ScalarObservationHistory n × ℝ,
    scalarHistoryInnovationSum z dt n h.1 *
      scalarInnovation (scalarLastField z n h.1) (dt n) h.2
    ∂scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n) = 0
  rw [Measure.integral_compProd (integrable_scalarHistoryInnovationCross z dt n)]
  simp only [scalarObservationStepKernel_apply, integral_const_mul,
    integral_scalarInnovation_transition, mul_zero, integral_zero]

theorem integral_scalarHistoryInnovationStep_sq (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    (∫ h : ScalarObservationHistory (n + 1),
      (scalarInnovation (scalarLastField z n h.1) (dt n) h.2) ^ 2
      ∂scalarObservationHistoryLaw z dt (n + 1)) =
      (dt n : ℝ) + (dt n : ℝ) ^ 2 *
        (∫ h, scalarDefect (scalarLastField z n h) ∂scalarObservationHistoryLaw z dt n) := by
  change (∫ h : ScalarObservationHistory n × ℝ,
    (scalarInnovation (scalarLastField z n h.1) (dt n) h.2) ^ 2
    ∂scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n) = _
  rw [Measure.integral_compProd (integrable_scalarHistoryInnovationStep_sq z dt n)]
  simp only [scalarObservationStepKernel_apply, integral_scalarInnovation_sq_transition]
  have hi : Integrable (fun h => scalarDefect (scalarLastField z n h))
      (scalarObservationHistoryLaw z dt n) := by
    apply (integrable_const (1 : ℝ)).mono'
      ((measurable_scalarDefect.comp (measurable_scalarLastField z n)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun h => by
      change ‖scalarDefect (scalarLastField z n h)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_pos (scalarDefect_pos _)]
      exact scalarDefect_le_one _)
  rw [integral_add (integrable_const _) (hi.const_mul _), integral_const_mul]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]

theorem integral_scalarHistoryInnovationSum_sq_succ (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    (∫ h, (scalarHistoryInnovationSum z dt (n + 1) h) ^ 2
      ∂scalarObservationHistoryLaw z dt (n + 1)) =
      (∫ h, (scalarHistoryInnovationSum z dt n h) ^ 2
        ∂scalarObservationHistoryLaw z dt n) + (dt n : ℝ) + (dt n : ℝ) ^ 2 *
          (∫ h, scalarDefect (scalarLastField z n h) ∂scalarObservationHistoryLaw z dt n) := by
  have he : (fun h : ScalarObservationHistory (n + 1) =>
      (scalarHistoryInnovationSum z dt (n + 1) h) ^ 2) =
      (fun h => (scalarHistoryInnovationSum z dt n h.1) ^ 2 +
        2 * (scalarHistoryInnovationSum z dt n h.1 *
          scalarInnovation (scalarLastField z n h.1) (dt n) h.2) +
        (scalarInnovation (scalarLastField z n h.1) (dt n) h.2) ^ 2) := by
    funext h
    simp only [scalarHistoryInnovationSum]
    ring
  have hp := integrable_scalarHistoryLift z dt n _
    ((measurable_scalarHistoryInnovationSum z dt n).pow_const 2)
    (integrable_scalarHistoryInnovationSum_sq z dt n)
  have hc := (integrable_scalarHistoryInnovationCross z dt n).const_mul 2
  have hj := integrable_scalarHistoryInnovationStep_sq z dt n
  rw [he, integral_add
    (f := fun h : ScalarObservationHistory (n + 1) =>
      (scalarHistoryInnovationSum z dt n h.1) ^ 2 +
        2 * (scalarHistoryInnovationSum z dt n h.1 *
          scalarInnovation (scalarLastField z n h.1) (dt n) h.2))
    (g := fun h : ScalarObservationHistory (n + 1) =>
      (scalarInnovation (scalarLastField z n h.1) (dt n) h.2) ^ 2)
    (hp.add hc) hj, integral_add
    (f := fun h : ScalarObservationHistory (n + 1) =>
      (scalarHistoryInnovationSum z dt n h.1) ^ 2)
    (g := fun h : ScalarObservationHistory (n + 1) =>
      2 * (scalarHistoryInnovationSum z dt n h.1 *
        scalarInnovation (scalarLastField z n h.1) (dt n) h.2))
    hp hc, integral_const_mul,
    integral_scalarHistoryInnovationCross_eq_zero, mul_zero, add_zero,
    integral_scalarHistoryLift z dt n _ ((measurable_scalarHistoryInnovationSum z dt n).pow_const 2)
      (integrable_scalarHistoryInnovationSum_sq z dt n),
    integral_scalarHistoryInnovationStep_sq]
  ring

theorem integral_scalarHistoryDefect_mem_unit (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    (∫ h, scalarDefect (scalarLastField z n h) ∂scalarObservationHistoryLaw z dt n) ∈
      Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact integral_nonneg (fun h => (scalarDefect_pos _).le)
  · have hi : Integrable (fun h => scalarDefect (scalarLastField z n h))
        (scalarObservationHistoryLaw z dt n) := by
      apply (integrable_const (1 : ℝ)).mono'
        ((measurable_scalarDefect.comp (measurable_scalarLastField z n)).aestronglyMeasurable)
      exact Filter.Eventually.of_forall (fun h => by
        change ‖scalarDefect (scalarLastField z n h)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_pos (scalarDefect_pos _)]
        exact scalarDefect_le_one _)
    have hh := integral_mono hi (integrable_const (1 : ℝ)) (fun _ => scalarDefect_le_one _)
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      using hh

theorem scalarHistoryInnovation_variance_error (z : ℝ) (dt : ℕ → ℝ≥0) (n : ℕ) :
    0 ≤ (∫ h, (scalarHistoryInnovationSum z dt n h) ^ 2
      ∂scalarObservationHistoryLaw z dt n) - ∑ k ∈ Finset.range n, (dt k : ℝ) ∧
    (∫ h, (scalarHistoryInnovationSum z dt n h) ^ 2
      ∂scalarObservationHistoryLaw z dt n) - ∑ k ∈ Finset.range n, (dt k : ℝ) ≤
      ∑ k ∈ Finset.range n, (dt k : ℝ) ^ 2 := by
  induction n with
  | zero => simp [scalarHistoryInnovationSum]
  | succ n ih =>
    rw [integral_scalarHistoryInnovationSum_sq_succ, Finset.sum_range_succ,
      Finset.sum_range_succ]
    have hd := integral_scalarHistoryDefect_mem_unit z dt n
    constructor <;> nlinarith [sq_nonneg (dt n : ℝ),
      mul_nonneg (sq_nonneg (dt n : ℝ)) hd.1,
      mul_le_mul_of_nonneg_left hd.2 (sq_nonneg (dt n : ℝ))]

theorem scalarHistoryInnovation_variance_error_le_mesh (z : ℝ) (dt : ℕ → ℝ≥0)
    (n : ℕ) (h : ℝ) (hh : ∀ k < n, (dt k : ℝ) ≤ h) :
    |(∫ a, (scalarHistoryInnovationSum z dt n a) ^ 2
      ∂scalarObservationHistoryLaw z dt n) - ∑ k ∈ Finset.range n, (dt k : ℝ)| ≤
      h * ∑ k ∈ Finset.range n, (dt k : ℝ) := by
  rw [abs_of_nonneg (scalarHistoryInnovation_variance_error z dt n).1]
  apply (scalarHistoryInnovation_variance_error z dt n).2.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hhk := hh k (Finset.mem_range.mp hk)
  nlinarith [(dt k).coe_nonneg,
    mul_le_mul_of_nonneg_right hhk (dt k).coe_nonneg]

end SKConstants
