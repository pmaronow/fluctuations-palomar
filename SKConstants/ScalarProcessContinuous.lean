module

public import SKConstants.ScalarProcessHiddenChannel
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def scalarLeftMeshSample (n : ℕ) (s : ℝ) : ℝ :=
  (⌊((n : ℝ) + 1) * s⌋₊ : ℝ) / ((n : ℝ) + 1)

theorem measurable_scalarLeftMeshSample (n : ℕ) : Measurable (scalarLeftMeshSample n) := by
  unfold scalarLeftMeshSample
  have hm : Measurable (fun s : ℝ => ⌊((n : ℝ) + 1) * s⌋₊) :=
    (measurable_id.const_mul _).nat_floor
  exact ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hm).div_const _

theorem scalarLeftMeshSample_nonneg (n : ℕ) (s : ℝ) : 0 ≤ scalarLeftMeshSample n s := by
  unfold scalarLeftMeshSample
  positivity

theorem scalarLeftMeshSample_error (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    |scalarLeftMeshSample n s - s| ≤ 1 / ((n : ℝ) + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hfl := Nat.floor_le (show 0 ≤ ((n : ℝ) + 1) * s from mul_nonneg hn.le hs)
  have hfu := Nat.lt_floor_add_one (((n : ℝ) + 1) * s)
  unfold scalarLeftMeshSample
  rw [abs_sub_comm, abs_of_nonneg (by
    apply sub_nonneg.mpr
    exact (div_le_iff₀ hn).2 (by nlinarith))]
  apply (le_div_iff₀ hn).2
  have hdiv : (((⌊((n : ℝ) + 1) * s⌋₊ : ℝ) / ((n : ℝ) + 1))) *
      ((n : ℝ) + 1) = (⌊((n : ℝ) + 1) * s⌋₊ : ℝ) :=
    div_mul_cancel₀ _ hn.ne'
  nlinarith

theorem scalarLeftMeshSample_tendsto (s : ℝ) (hs : 0 ≤ s) :
    Tendsto (fun n => scalarLeftMeshSample n s) atTop (𝓝 s) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => by simpa only [Real.norm_eq_abs] using scalarLeftMeshSample_error n s hs)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

def scalarEulerDrift (f : ℝ → ℝ) (T : ℝ) (n : ℕ) : ℝ :=
  ∫ s in Set.Icc 0 T, f (scalarLeftMeshSample n s)

theorem scalarEulerDrift_tendsto (f : ℝ → ℝ) (T : ℝ) (hf : Continuous f)
    (hb : ∀ s, ‖f s‖ ≤ 1) :
    Tendsto (scalarEulerDrift f T) atTop (𝓝 (∫ s in Set.Icc 0 T, f s)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => (1 : ℝ))
  · intro n
    exact (hf.measurable.comp (measurable_scalarLeftMeshSample n)).aestronglyMeasurable
  · exact integrable_const 1
  · exact fun n => Filter.Eventually.of_forall (fun s => hb _)
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hf.continuousAt.tendsto.comp (scalarLeftMeshSample_tendsto s hs.1)

def scalarHiddenPriorBool (z : ℝ) : Measure Bool :=
  letI : IsScalarTower ENNReal ENNReal ENNReal := Semigroup.isScalarTower
  ENNReal.ofReal (scalarPlusWeight z) • Measure.dirac true +
    ENNReal.ofReal (scalarMinusWeight z) • Measure.dirac false

instance scalarHiddenPriorBool_isProbability (z : ℝ) : IsProbabilityMeasure (scalarHiddenPriorBool z) where
  measure_univ := by
    simp only [scalarHiddenPriorBool, Measure.add_apply, Measure.smul_apply, measure_univ,
      smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (scalarPlusWeight_pos _).le (scalarMinusWeight_pos _).le,
      scalarWeight_sum, ENNReal.ofReal_one]

def scalarHiddenBrownianLaw {Ω : Type*} [MeasurableSpace Ω] (z : ℝ) (P : Measure Ω) :
    Measure (Bool × Ω) := (scalarHiddenPriorBool z).prod P

instance scalarHiddenBrownianLaw_isProbability {Ω : Type*} [MeasurableSpace Ω]
    (z : ℝ) (P : Measure Ω) [IsProbabilityMeasure P] : IsProbabilityMeasure (scalarHiddenBrownianLaw z P) := by
  unfold scalarHiddenBrownianLaw
  infer_instance

def scalarHiddenContinuousField {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (u : Bool × Ω) : ℝ := z + scalarHiddenSign u.1 * (t : ℝ) + B t u.2

def scalarHiddenFieldReal {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (s : ℝ) (u : Bool × Ω) : ℝ := z + scalarHiddenSign u.1 * s + B s.toNNReal u.2

def scalarContinuousDrift {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (u : Bool × Ω) : ℝ :=
  ∫ s in Set.Icc 0 (T : ℝ), Real.tanh (scalarHiddenFieldReal z B s u)

def scalarContinuousInnovation {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (u : Bool × Ω) : ℝ :=
  scalarHiddenContinuousField z B T u - z - scalarContinuousDrift z B T u

def scalarEulerInnovation {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (n : ℕ) (u : Bool × Ω) : ℝ :=
  scalarHiddenContinuousField z B T u - z -
    scalarEulerDrift (fun s => Real.tanh (scalarHiddenFieldReal z B s u)) (T : ℝ) n

theorem norm_tanh_le_one (x : ℝ) : ‖Real.tanh x‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  nlinarith [Real.tanh_sq_lt_one x, sq_abs (Real.tanh x), sq_nonneg (|Real.tanh x| - 1)]

theorem continuous_scalarHiddenFieldReal {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (u : Bool × Ω) (hB : Continuous (fun t => B t u.2)) :
    Continuous (fun s => scalarHiddenFieldReal z B s u) := by
  exact (continuous_const.add (continuous_const.mul continuous_id)).add
    (hB.comp continuous_real_toNNReal)

theorem scalarEulerInnovation_tendsto_path {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (u : Bool × Ω) (hB : Continuous (fun t => B t u.2)) :
    Tendsto (fun n => scalarEulerInnovation z B T n u) atTop
      (𝓝 (scalarContinuousInnovation z B T u)) := by
  have hf : Continuous (fun s => Real.tanh (scalarHiddenFieldReal z B s u)) := by
    have ht : Continuous Real.tanh := by
      have he : Real.tanh = Real.sinh / Real.cosh := by funext s; exact Real.tanh_eq_sinh_div_cosh s
      rw [he]
      exact Real.continuous_sinh.div Real.continuous_cosh (fun s => (Real.cosh_pos s).ne')
    exact ht.comp (continuous_scalarHiddenFieldReal z B u hB)
  exact tendsto_const_nhds.sub (scalarEulerDrift_tendsto _ (T : ℝ) hf
    (fun s => norm_tanh_le_one _))

theorem scalarContinuousDrift_norm_le {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (u : Bool × Ω) : ‖scalarContinuousDrift z B T u‖ ≤ (T : ℝ) := by
  have hh := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Set.Icc 0 (T : ℝ)))
    (f := fun s => Real.tanh (scalarHiddenFieldReal z B s u))
    (Filter.Eventually.of_forall (fun s => norm_tanh_le_one _))
  simpa only [scalarContinuousDrift, Measure.real, Measure.restrict_apply_univ,
    Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal T.coe_nonneg, one_mul] using hh

theorem scalarEulerDrift_norm_le {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (n : ℕ) (u : Bool × Ω) :
    ‖scalarEulerDrift (fun s => Real.tanh (scalarHiddenFieldReal z B s u)) (T : ℝ) n‖ ≤
      (T : ℝ) := by
  have hh := norm_integral_le_of_norm_le_const
    (μ := volume.restrict (Set.Icc 0 (T : ℝ)))
    (f := fun s => Real.tanh (scalarHiddenFieldReal z B (scalarLeftMeshSample n s) u))
    (Filter.Eventually.of_forall (fun s => norm_tanh_le_one _))
  simpa only [scalarEulerDrift, Measure.real, Measure.restrict_apply_univ,
    Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal T.coe_nonneg, one_mul] using hh

theorem scalarEulerInnovation_error_norm_le {Ω : Type*} (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (n : ℕ) (u : Bool × Ω) :
    ‖scalarEulerInnovation z B T n u - scalarContinuousInnovation z B T u‖ ≤ 2 * (T : ℝ) := by
  have he : scalarEulerInnovation z B T n u - scalarContinuousInnovation z B T u =
      scalarContinuousDrift z B T u -
        scalarEulerDrift (fun s => Real.tanh (scalarHiddenFieldReal z B s u)) (T : ℝ) n := by
    unfold scalarEulerInnovation scalarContinuousInnovation
    ring
  rw [he]
  apply (norm_sub_le _ _).trans
  linarith [scalarContinuousDrift_norm_le z B T u, scalarEulerDrift_norm_le z B T n u]

theorem measurable_scalarTanh : Measurable Real.tanh := by
  have he : Real.tanh = Real.sinh / Real.cosh := by
    funext s
    exact Real.tanh_eq_sinh_div_cosh s
  rw [he]
  exact Real.measurable_sinh.div Real.measurable_cosh

theorem measurable_scalarHiddenFieldReal {Ω : Type*} [MeasurableSpace Ω] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : Measurable (Function.uncurry B)) :
    Measurable (Function.uncurry (scalarHiddenFieldReal z B)) := by
  have hs : Measurable (fun p : ℝ × (Bool × Ω) => scalarHiddenSign p.2.1) :=
    (measurable_of_finite scalarHiddenSign).comp (measurable_fst.comp measurable_snd)
  have hb : Measurable (fun p : ℝ × (Bool × Ω) => B p.1.toNNReal p.2.2) :=
    hB.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd))
  exact (measurable_const.add (hs.mul measurable_fst)).add hb

theorem measurable_scalarContinuousDrift {Ω : Type*} [MeasurableSpace Ω] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : Measurable (Function.uncurry B)) (T : ℝ≥0) :
    Measurable (scalarContinuousDrift z B T) := by
  have hm : StronglyMeasurable (fun p : (Bool × Ω) × ℝ =>
      Real.tanh (scalarHiddenFieldReal z B p.2 p.1)) :=
    (measurable_scalarTanh.comp ((measurable_scalarHiddenFieldReal z B hB).comp
      measurable_swap)).stronglyMeasurable
  exact (hm.integral_prod_right' (ν := volume.restrict (Set.Icc 0 (T : ℝ)))).measurable

theorem measurable_scalarEulerDrift {Ω : Type*} [MeasurableSpace Ω] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : Measurable (Function.uncurry B)) (T : ℝ≥0) (n : ℕ) :
    Measurable (fun u => scalarEulerDrift
      (fun s => Real.tanh (scalarHiddenFieldReal z B s u)) (T : ℝ) n) := by
  have hm : StronglyMeasurable (fun p : (Bool × Ω) × ℝ =>
      Real.tanh (scalarHiddenFieldReal z B (scalarLeftMeshSample n p.2) p.1)) :=
    (measurable_scalarTanh.comp ((measurable_scalarHiddenFieldReal z B hB).comp
      (((measurable_scalarLeftMeshSample n).comp measurable_snd).prodMk
        measurable_fst))).stronglyMeasurable
  exact (hm.integral_prod_right' (ν := volume.restrict (Set.Icc 0 (T : ℝ)))).measurable

theorem measurable_scalarEulerInnovation_error {Ω : Type*} [MeasurableSpace Ω] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : Measurable (Function.uncurry B)) (T : ℝ≥0) (n : ℕ) :
    Measurable (fun u => scalarEulerInnovation z B T n u - scalarContinuousInnovation z B T u) := by
  have he : (fun u => scalarEulerInnovation z B T n u - scalarContinuousInnovation z B T u) =
      fun u => scalarContinuousDrift z B T u -
        scalarEulerDrift (fun s => Real.tanh (scalarHiddenFieldReal z B s u)) (T : ℝ) n := by
    funext u
    unfold scalarEulerInnovation scalarContinuousInnovation
    ring
  rw [he]
  exact (measurable_scalarContinuousDrift z B hB T).sub
    (measurable_scalarEulerDrift z B hB T n)

theorem scalarEulerInnovation_tendsto_L2_of_joint_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hBrownian : IsBrownianReal B P) (hBmeas : Measurable (Function.uncurry B)) (T : ℝ≥0) :
    Tendsto (fun n => ∫ u,
      (scalarEulerInnovation z B T n u - scalarContinuousInnovation z B T u) ^ 2
      ∂scalarHiddenBrownianLaw z P) atTop (𝓝 0) := by
  have hcont : ∀ᵐ u : Bool × Ω ∂scalarHiddenBrownianLaw z P,
      Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae
      hBrownian.cont
  have hh := tendsto_integral_of_dominated_convergence
    (μ := scalarHiddenBrownianLaw z P)
    (F := fun n u => (scalarEulerInnovation z B T n u - scalarContinuousInnovation z B T u) ^ 2)
    (f := fun _ => (0 : ℝ)) (fun _ => (2 * (T : ℝ)) ^ 2)
    (fun n => ((measurable_scalarEulerInnovation_error z B hBmeas T n).pow_const 2).aestronglyMeasurable)
    (integrable_const _) (fun n => Filter.Eventually.of_forall (fun u => by
      change ‖(scalarEulerInnovation z B T n u - scalarContinuousInnovation z B T u) ^ 2‖ ≤
        (2 * (T : ℝ)) ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb := scalarEulerInnovation_error_norm_le z B T n u
      rw [Real.norm_eq_abs] at hb
      calc
        _ = |scalarEulerInnovation z B T n u - scalarContinuousInnovation z B T u| ^ 2 :=
          (sq_abs _).symm
        _ ≤ (2 * (T : ℝ)) ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hb))
    (by
      filter_upwards [hcont] with u hu
      have ht := (scalarEulerInnovation_tendsto_path z B T u hu).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => scalarContinuousInnovation z B T u) atTop
          (𝓝 (scalarContinuousInnovation z B T u)))
      simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using ht.pow 2)
  simpa only [integral_zero] using hh

theorem scalarLeftMeshSample_eq_on_cell (n k : ℕ) (s : ℝ)
    (hs : s ∈ Set.Ico ((k : ℝ) / ((n : ℝ) + 1))
      (((k : ℝ) + 1) / ((n : ℝ) + 1))) :
    scalarLeftMeshSample n s = (k : ℝ) / ((n : ℝ) + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hsl : (k : ℝ) ≤ ((n : ℝ) + 1) * s := by
    have hh := (div_le_iff₀ hn).1 hs.1
    nlinarith
  have hsu : ((n : ℝ) + 1) * s < (k : ℝ) + 1 := by
    have hh := (lt_div_iff₀ hn).1 hs.2
    nlinarith
  have he := (Nat.floor_eq_iff (show 0 ≤ ((n : ℝ) + 1) * s from
    (Nat.cast_nonneg k).trans hsl)).2 ⟨hsl, hsu⟩
  simp only [scalarLeftMeshSample, he]

theorem scalarEulerDrift_cell_integral (f : ℝ → ℝ) (n k : ℕ) (b : ℝ)
    (hb : (k : ℝ) / ((n : ℝ) + 1) ≤ b)
    (hbu : b ≤ ((k : ℝ) + 1) / ((n : ℝ) + 1)) :
    (∫ s in ((k : ℝ) / ((n : ℝ) + 1))..b, f (scalarLeftMeshSample n s)) =
      (b - (k : ℝ) / ((n : ℝ) + 1)) * f ((k : ℝ) / ((n : ℝ) + 1)) := by
  have he : (∫ s in ((k : ℝ) / ((n : ℝ) + 1))..b, f (scalarLeftMeshSample n s)) =
      ∫ _ in ((k : ℝ) / ((n : ℝ) + 1))..b, f ((k : ℝ) / ((n : ℝ) + 1)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hb
    intro s hs
    change f (scalarLeftMeshSample n s) = f ((k : ℝ) / ((n : ℝ) + 1))
    rw [scalarLeftMeshSample_eq_on_cell n k s ⟨hs.1.le, hs.2.trans_le hbu⟩]
  rw [he, intervalIntegral.integral_const, smul_eq_mul]

theorem measurable_scalarMeshComposite (f : ℝ → ℝ) (n : ℕ) :
    Measurable (fun s => f (scalarLeftMeshSample n s)) := by
  have hm : Measurable (fun s : ℝ => ⌊((n : ℝ) + 1) * s⌋₊) :=
    (measurable_id.const_mul _).nat_floor
  exact (measurable_of_countable
    (fun k : ℕ => f ((k : ℝ) / ((n : ℝ) + 1)))).comp hm

theorem intervalIntegrable_scalarMeshComposite (f : ℝ → ℝ) (n : ℕ)
    (hb : ∀ s, ‖f s‖ ≤ 1) (a b : ℝ) :
    IntervalIntegrable (fun s => f (scalarLeftMeshSample n s)) volume a b := by
  apply (intervalIntegrable_iff' (by finiteness)).2
  change IntegrableOn (fun s => f (scalarLeftMeshSample n s))
    (Set.Icc (min a b) (max a b)) volume
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_scalarMeshComposite f n).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun s => hb _)

theorem scalarEulerDrift_eq_finite_sum (f : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (n : ℕ) (hb : ∀ s, ‖f s‖ ≤ 1) :
    scalarEulerDrift f T n =
      (∑ k ∈ Finset.range ⌊((n : ℝ) + 1) * T⌋₊,
        (1 / ((n : ℝ) + 1)) * f ((k : ℝ) / ((n : ℝ) + 1))) +
      (T - (⌊((n : ℝ) + 1) * T⌋₊ : ℝ) / ((n : ℝ) + 1)) *
        f ((⌊((n : ℝ) + 1) * T⌋₊ : ℝ) / ((n : ℝ) + 1)) := by
  let m := ⌊((n : ℝ) + 1) * T⌋₊
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hl : (m : ℝ) / ((n : ℝ) + 1) ≤ T := by
    apply (div_le_iff₀ hn).2
    change (⌊((n : ℝ) + 1) * T⌋₊ : ℝ) ≤ T * ((n : ℝ) + 1)
    exact (Nat.floor_le (mul_nonneg hn.le hT)).trans_eq (mul_comm _ _)
  have hu : T ≤ ((m : ℝ) + 1) / ((n : ℝ) + 1) := by
    apply (le_div_iff₀ hn).2
    change T * ((n : ℝ) + 1) ≤ (⌊((n : ℝ) + 1) * T⌋₊ : ℝ) + 1
    have hh := Nat.lt_floor_add_one (((n : ℝ) + 1) * T)
    nlinarith
  have hi := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun k : ℕ => (k : ℝ) / ((n : ℝ) + 1)) (n := m)
    (fun k _ => intervalIntegrable_scalarMeshComposite f n hb _ _)
  simp only [Nat.cast_zero, zero_div] at hi
  have he : (∑ k ∈ Finset.range m,
      ∫ s in ((k : ℝ) / ((n : ℝ) + 1))..((↑(k + 1) : ℝ) / ((n : ℝ) + 1)),
        f (scalarLeftMeshSample n s)) =
      ∑ k ∈ Finset.range m,
        (1 / ((n : ℝ) + 1)) * f ((k : ℝ) / ((n : ℝ) + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [scalarEulerDrift_cell_integral f n k _]
    · congr 1
      push_cast
      ring
    · apply (div_le_div_iff_of_pos_right hn).2
      exact_mod_cast Nat.le_succ k
    · simp only [Nat.cast_add, Nat.cast_one]
      exact le_rfl
  rw [he] at hi
  have hc := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_scalarMeshComposite f n hb 0 ((m : ℝ) / ((n : ℝ) + 1)))
    (intervalIntegrable_scalarMeshComposite f n hb ((m : ℝ) / ((n : ℝ) + 1)) T)
  rw [← hi, scalarEulerDrift_cell_integral f n m T hl hu] at hc
  unfold scalarEulerDrift
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
  exact hc.symm

theorem aemeasurable_scalarHiddenFieldReal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (s : ℝ) :
    AEMeasurable (scalarHiddenFieldReal z B s) (scalarHiddenBrownianLaw z P) := by
  have hs : AEMeasurable (fun u : Bool × Ω => scalarHiddenSign u.1)
      (scalarHiddenBrownianLaw z P) :=
    ((measurable_of_finite scalarHiddenSign).comp measurable_fst).aemeasurable
  have hb : AEMeasurable (fun u : Bool × Ω => B s.toNNReal u.2)
      (scalarHiddenBrownianLaw z P) := (hB.aemeasurable s.toNNReal).comp_snd
  exact (aemeasurable_const.add (hs.mul_const s)).add hb

theorem aemeasurable_scalarEulerDrift {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) (n : ℕ) :
    AEMeasurable (fun u => scalarEulerDrift
      (fun s => Real.tanh (scalarHiddenFieldReal z B s u)) (T : ℝ) n)
      (scalarHiddenBrownianLaw z P) := by
  have hm (s : ℝ) : AEMeasurable (fun u => Real.tanh (scalarHiddenFieldReal z B s u))
      (scalarHiddenBrownianLaw z P) :=
    measurable_scalarTanh.comp_aemeasurable (aemeasurable_scalarHiddenFieldReal P z B hB s)
  have hsum (m : ℕ) : AEMeasurable (fun u : Bool × Ω =>
      ∑ k ∈ Finset.range m, (1 / ((n : ℝ) + 1)) *
        Real.tanh (scalarHiddenFieldReal z B ((k : ℝ) / ((n : ℝ) + 1)) u))
      (scalarHiddenBrownianLaw z P) := by
    induction m with
    | zero => simpa only [Finset.range_zero, Finset.sum_empty] using
        (aemeasurable_const : AEMeasurable (fun _ : Bool × Ω => (0 : ℝ))
          (scalarHiddenBrownianLaw z P))
    | succ m ih =>
      simp only [Finset.sum_range_succ]
      exact ih.add ((hm _).const_mul _)
  have he : (fun u => scalarEulerDrift
      (fun s => Real.tanh (scalarHiddenFieldReal z B s u)) (T : ℝ) n) =
      (fun u : Bool × Ω =>
        (∑ k ∈ Finset.range ⌊((n : ℝ) + 1) * (T : ℝ)⌋₊,
          (1 / ((n : ℝ) + 1)) * Real.tanh
            (scalarHiddenFieldReal z B ((k : ℝ) / ((n : ℝ) + 1)) u)) +
        ((T : ℝ) - (⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) / ((n : ℝ) + 1)) *
          Real.tanh (scalarHiddenFieldReal z B
            ((⌊((n : ℝ) + 1) * (T : ℝ)⌋₊ : ℝ) / ((n : ℝ) + 1)) u)) := by
    funext u
    exact scalarEulerDrift_eq_finite_sum _ (T : ℝ) T.coe_nonneg n (fun s => norm_tanh_le_one _)
  rw [he]
  exact (hsum _).add ((hm _).const_mul _)

theorem aemeasurable_scalarEulerInnovation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) (T : ℝ≥0) (n : ℕ) :
    AEMeasurable (scalarEulerInnovation z B T n) (scalarHiddenBrownianLaw z P) := by
  have hs : AEMeasurable (fun u : Bool × Ω => scalarHiddenSign u.1)
      (scalarHiddenBrownianLaw z P) :=
    ((measurable_of_finite scalarHiddenSign).comp measurable_fst).aemeasurable
  have hb : AEMeasurable (fun u : Bool × Ω => B T u.2)
      (scalarHiddenBrownianLaw z P) := (hB.aemeasurable T).comp_snd
  exact (((aemeasurable_const.add (hs.mul_const (T : ℝ))).add hb).sub_const z).sub
    (aemeasurable_scalarEulerDrift P z B hB T n)

theorem aestronglyMeasurable_scalarContinuousInnovation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    AEStronglyMeasurable (scalarContinuousInnovation z B T) (scalarHiddenBrownianLaw z P) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (aemeasurable_scalarEulerInnovation P z B hB.toIsPreBrownianReal T n).aestronglyMeasurable)
  have hcont : ∀ᵐ u : Bool × Ω ∂scalarHiddenBrownianLaw z P,
      Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hB.cont
  filter_upwards [hcont] with u hu
  exact scalarEulerInnovation_tendsto_path z B T u hu

theorem scalarEulerInnovation_tendsto_L2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    Tendsto (fun n => ∫ u,
      (scalarEulerInnovation z B T n u - scalarContinuousInnovation z B T u) ^ 2
      ∂scalarHiddenBrownianLaw z P) atTop (𝓝 0) := by
  have hcont : ∀ᵐ u : Bool × Ω ∂scalarHiddenBrownianLaw z P,
      Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hB.cont
  have hc := aestronglyMeasurable_scalarContinuousInnovation P z B hB T
  have hh := tendsto_integral_of_dominated_convergence
    (μ := scalarHiddenBrownianLaw z P)
    (F := fun n u => (scalarEulerInnovation z B T n u - scalarContinuousInnovation z B T u) ^ 2)
    (f := fun _ => (0 : ℝ)) (fun _ => (2 * (T : ℝ)) ^ 2)
    (fun n => (((aemeasurable_scalarEulerInnovation P z B hB.toIsPreBrownianReal T n).aestronglyMeasurable.sub
      hc).pow 2))
    (integrable_const _) (fun n => Filter.Eventually.of_forall (fun u => by
      change ‖(scalarEulerInnovation z B T n u - scalarContinuousInnovation z B T u) ^ 2‖ ≤
        (2 * (T : ℝ)) ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hb := scalarEulerInnovation_error_norm_le z B T n u
      rw [Real.norm_eq_abs] at hb
      calc
        _ = |scalarEulerInnovation z B T n u - scalarContinuousInnovation z B T u| ^ 2 :=
          (sq_abs _).symm
        _ ≤ (2 * (T : ℝ)) ^ 2 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hb))
    (by
      filter_upwards [hcont] with u hu
      have ht := (scalarEulerInnovation_tendsto_path z B T u hu).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => scalarContinuousInnovation z B T u) atTop
          (𝓝 (scalarContinuousInnovation z B T u)))
      simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using ht.pow 2)
  simpa only [integral_zero] using hh

theorem continuous_scalarTanh : Continuous Real.tanh := by
  have he : Real.tanh = Real.sinh / Real.cosh := by
    funext s
    exact Real.tanh_eq_sinh_div_cosh s
  rw [he]
  exact Real.continuous_sinh.div Real.continuous_cosh (fun s => (Real.cosh_pos s).ne')

theorem continuous_scalarContinuousInnovation_path {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (u : Bool × Ω) (hB : Continuous (fun t => B t u.2)) :
    Continuous (fun T => scalarContinuousInnovation z B T u) := by
  have hf : Continuous (fun s => Real.tanh (scalarHiddenFieldReal z B s u)) :=
    continuous_scalarTanh.comp (continuous_scalarHiddenFieldReal z B u hB)
  have hi : Continuous (fun T : ℝ≥0 => ∫ s in (0 : ℝ)..(T : ℝ),
      Real.tanh (scalarHiddenFieldReal z B s u)) :=
    (intervalIntegral.differentiable_integral_of_continuous hf).continuous.comp NNReal.continuous_coe
  have he : (fun T : ℝ≥0 => scalarContinuousDrift z B T u) =
      (fun T : ℝ≥0 => ∫ s in (0 : ℝ)..(T : ℝ),
        Real.tanh (scalarHiddenFieldReal z B s u)) := by
    funext T
    unfold scalarContinuousDrift
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le T.coe_nonneg]
  have hd : Continuous (fun T : ℝ≥0 => scalarContinuousDrift z B T u) := he ▸ hi
  exact (((continuous_const.add (continuous_const.mul NNReal.continuous_coe)).add hB).sub
    continuous_const).sub hd

theorem scalarContinuousInnovation_ae_continuous {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) :
    ∀ᵐ u ∂scalarHiddenBrownianLaw z P, Continuous (fun T => scalarContinuousInnovation z B T u) := by
  have hcont : ∀ᵐ u : Bool × Ω ∂scalarHiddenBrownianLaw z P,
      Continuous (fun t => B t u.2) :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae hB.cont
  filter_upwards [hcont] with u hu
  exact continuous_scalarContinuousInnovation_path z B u hu

theorem scalarContinuousInnovation_zero_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsPreBrownianReal B P) :
    ∀ᵐ u ∂scalarHiddenBrownianLaw z P, scalarContinuousInnovation z B 0 u = 0 := by
  have hz : ∀ᵐ u : Bool × Ω ∂scalarHiddenBrownianLaw z P, B 0 u.2 = 0 :=
    (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P)).quasiMeasurePreserving.ae
      hB.eval_zero_ae_eq_zero
  filter_upwards [hz] with u hu
  simp [scalarContinuousInnovation, scalarHiddenContinuousField, scalarContinuousDrift, hu,
    Set.Icc_self]

theorem memLp_scalarContinuousInnovation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (hB : IsBrownianReal B P) (T : ℝ≥0) :
    MemLp (scalarContinuousInnovation z B T) 2 (scalarHiddenBrownianLaw z P) := by
  have hb : MemLp (fun u : Bool × Ω => B T u.2) 2 (scalarHiddenBrownianLaw z P) :=
    ((hB.toIsPreBrownianReal.hasLaw_eval T).memLp (memLp_id_gaussianReal 2)).comp_measurePreserving
      (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := P))
  have hr : MemLp (fun u => scalarContinuousInnovation z B T u - B T u.2) 2
      (scalarHiddenBrownianLaw z P) := by
    apply MemLp.of_bound
      ((aestronglyMeasurable_scalarContinuousInnovation P z B hB T).sub hb.aestronglyMeasurable)
      (2 * (T : ℝ))
    apply Filter.Eventually.of_forall
    intro u
    have he : scalarContinuousInnovation z B T u - B T u.2 =
        scalarHiddenSign u.1 * (T : ℝ) - scalarContinuousDrift z B T u := by
      unfold scalarContinuousInnovation scalarHiddenContinuousField
      ring
    change ‖scalarContinuousInnovation z B T u - B T u.2‖ ≤ 2 * (T : ℝ)
    rw [he]
    have hs : ‖scalarHiddenSign u.1 * (T : ℝ)‖ = (T : ℝ) := by
      cases u.1 <;> simp [scalarHiddenSign, Real.norm_eq_abs, abs_of_nonneg T.coe_nonneg]
    apply (norm_sub_le _ _).trans
    rw [hs]
    linarith [scalarContinuousDrift_norm_le z B T u]
  have he : (fun u : Bool × Ω => B T u.2 +
      (scalarContinuousInnovation z B T u - B T u.2)) = scalarContinuousInnovation z B T := by
    funext u
    ring
  rw [← he]
  exact hb.add hr

theorem scalarEulerDrift_lipschitz_endpoint (f : ℝ → ℝ) (n : ℕ) (hb : ∀ s, ‖f s‖ ≤ 1)
    (S T : ℝ) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    ‖scalarEulerDrift f S n - scalarEulerDrift f T n‖ ≤ |S - T| := by
  have hs : scalarEulerDrift f S n = ∫ s in (0 : ℝ)..S, f (scalarLeftMeshSample n s) := by
    unfold scalarEulerDrift
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hS]
  have ht : scalarEulerDrift f T n = ∫ s in (0 : ℝ)..T, f (scalarLeftMeshSample n s) := by
    unfold scalarEulerDrift
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT]
  rw [hs, ht, intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_scalarMeshComposite f n hb 0 S)
    (intervalIntegrable_scalarMeshComposite f n hb 0 T)]
  simpa only [one_mul] using intervalIntegral.norm_integral_le_of_norm_le_const
    (a := T) (b := S) (fun s _ => hb (scalarLeftMeshSample n s))

theorem scalarEulerInnovation_prefix_tendsto_path {Ω : Type*} (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (u : Bool × Ω)
    (hB : Continuous (fun t => B t u.2)) :
    Tendsto (fun n => scalarEulerInnovation z B
      (scalarLeftMeshSample n (T : ℝ)).toNNReal n u) atTop
      (𝓝 (scalarContinuousInnovation z B T u)) := by
  let f : ℝ → ℝ := fun s => Real.tanh (scalarHiddenFieldReal z B s u)
  have hf : Continuous f := continuous_scalarTanh.comp (continuous_scalarHiddenFieldReal z B u hB)
  have ht : Tendsto (fun n => scalarLeftMeshSample n (T : ℝ)) atTop (𝓝 (T : ℝ)) :=
    scalarLeftMeshSample_tendsto _ T.coe_nonneg
  have hnn : Tendsto (fun n => (scalarLeftMeshSample n (T : ℝ)).toNNReal) atTop (𝓝 T) := by
    simpa only [Real.toNNReal_coe] using tendsto_real_toNNReal ht
  have hfield : Tendsto (fun n => scalarHiddenContinuousField z B
      (scalarLeftMeshSample n (T : ℝ)).toNNReal u) atTop
      (𝓝 (scalarHiddenContinuousField z B T u)) :=
    (((continuous_const.add (continuous_const.mul NNReal.continuous_coe)).add hB).tendsto T).comp hnn
  have he : Tendsto (fun n => scalarEulerDrift f (scalarLeftMeshSample n (T : ℝ)) n -
      scalarEulerDrift f (T : ℝ) n) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simp only [sub_zero]
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => (scalarEulerDrift_lipschitz_endpoint f n (fun s => norm_tanh_le_one _)
        (scalarLeftMeshSample n (T : ℝ)) (T : ℝ)
        (scalarLeftMeshSample_nonneg _ _) T.coe_nonneg).trans
          (scalarLeftMeshSample_error n (T : ℝ) T.coe_nonneg))
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hd : Tendsto (fun n => scalarEulerDrift f (scalarLeftMeshSample n (T : ℝ)) n)
      atTop (𝓝 (scalarContinuousDrift z B T u)) := by
    have hsum := he.add (scalarEulerDrift_tendsto f (T : ℝ) hf (fun s => norm_tanh_le_one _))
    have hfun : (fun n => (scalarEulerDrift f (scalarLeftMeshSample n (T : ℝ)) n -
        scalarEulerDrift f (T : ℝ) n) + scalarEulerDrift f (T : ℝ) n) =
        (fun n => scalarEulerDrift f (scalarLeftMeshSample n (T : ℝ)) n) := by
      funext n
      ring
    rw [hfun, zero_add] at hsum
    exact hsum
  have hfin := (hfield.sub_const z).sub hd
  convert hfin using 1
  · funext n
    simp only [scalarEulerInnovation, Real.coe_toNNReal',
      max_eq_left (scalarLeftMeshSample_nonneg _ _)]
    rfl
  · rfl

end SKConstants
