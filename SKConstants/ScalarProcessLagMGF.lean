module
public import SKConstants.ScalarProcessInnovationMGF
public import SKConstants.ScalarProcessHistory
public import SKConstants.ConcentrationMGF
public import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

abbrev ScalarFiniteHistoryCoefficient := (k : ℕ) → ScalarObservationHistory k → ℝ

def scalarPredictableInnovationSum (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) : (n : ℕ) → ScalarObservationHistory n → ℝ :=
  Nat.rec (fun _ => 0) (fun n prev p => prev p.1 + H n p.1 *
    scalarInnovation (scalarLastField z n p.1) (dt n) p.2)

def scalarPredictableInnovationProxy (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) : (n : ℕ) → ScalarObservationHistory n → ℝ :=
  Nat.rec (fun _ => 0) (fun n prev p => prev p.1 + (H n p.1) ^ 2 *
    ((dt n : ℝ) + (dt n : ℝ) ^ 2))

def scalarPredictableInnovationExponential (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (theta : ℝ) (n : ℕ)
    (p : ScalarObservationHistory n) : ℝ :=
  Real.exp (theta * scalarPredictableInnovationSum z dt H n p -
    theta ^ 2 * scalarPredictableInnovationProxy dt H n p / 2)

@[simp] lemma scalarPredictableInnovationSum_zero (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (p : ScalarObservationHistory 0) :
    scalarPredictableInnovationSum z dt H 0 p = 0 := rfl
@[simp] lemma scalarPredictableInnovationSum_succ (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (n : ℕ) (p : ScalarObservationHistory n) (y : ℝ) :
    scalarPredictableInnovationSum z dt H (n + 1) (p, y) =
      scalarPredictableInnovationSum z dt H n p + H n p *
        scalarInnovation (scalarLastField z n p) (dt n) y := rfl
@[simp] lemma scalarPredictableInnovationProxy_zero (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (p : ScalarObservationHistory 0) :
    scalarPredictableInnovationProxy dt H 0 p = 0 := rfl
@[simp] lemma scalarPredictableInnovationProxy_succ (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (n : ℕ) (p : ScalarObservationHistory n) (y : ℝ) :
    scalarPredictableInnovationProxy dt H (n + 1) (p, y) =
      scalarPredictableInnovationProxy dt H n p + (H n p) ^ 2 *
        ((dt n : ℝ) + (dt n : ℝ) ^ 2) := rfl

lemma measurable_scalarPredictableInnovationSum (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    Measurable (scalarPredictableInnovationSum z dt H n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp measurable_fst).add (((hH n).comp measurable_fst).mul
      (measurable_scalarHistoryInnovationStep z (dt n) n))

lemma measurable_scalarPredictableInnovationProxy (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    Measurable (scalarPredictableInnovationProxy dt H n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp measurable_fst).add
      ((((hH n).comp measurable_fst).pow_const 2).mul_const _)

lemma measurable_scalarPredictableInnovationExponential (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (hH : ∀ k, Measurable (H k))
    (theta : ℝ) (n : ℕ) : Measurable (scalarPredictableInnovationExponential z dt H theta n) := by
  exact ((measurable_scalarPredictableInnovationSum z dt H hH n).const_mul theta |>.sub
    ((measurable_scalarPredictableInnovationProxy dt H hH n).const_mul (theta ^ 2)
      |>.div_const 2)).exp

lemma integrable_scalarInnovation_compensated_exp (z theta : ℝ) (t : ℝ≥0) :
    Integrable (fun y => Real.exp (theta * scalarInnovation z t y -
      theta ^ 2 * ((t : ℝ) + (t : ℝ) ^ 2) / 2)) (scalarTransitionKernel t z) := by
  simp_rw [Real.exp_sub]
  exact (integrable_exp_scalarInnovation z theta t).div_const _

lemma integral_scalarInnovation_compensated_exp_le (z theta : ℝ) (t : ℝ≥0) :
    (∫ y, Real.exp (theta * scalarInnovation z t y -
      theta ^ 2 * ((t : ℝ) + (t : ℝ) ^ 2) / 2) ∂scalarTransitionKernel t z) ≤ 1 := by
  simp_rw [Real.exp_sub]
  rw [integral_div]
  exact (div_le_one (Real.exp_pos _)).mpr (mgf_scalarInnovation_le z theta t)

lemma scalarPredictableInnovationExponential_succ (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (theta : ℝ) (n : ℕ)
    (p : ScalarObservationHistory n) (y : ℝ) :
    scalarPredictableInnovationExponential z dt H theta (n + 1) (p, y) =
      scalarPredictableInnovationExponential z dt H theta n p *
        Real.exp ((theta * H n p) * scalarInnovation (scalarLastField z n p) (dt n) y -
          (theta * H n p) ^ 2 * ((dt n : ℝ) + (dt n : ℝ) ^ 2) / 2) := by
  unfold scalarPredictableInnovationExponential
  rw [← Real.exp_add]
  congr 1
  simp only [scalarPredictableInnovationSum_succ, scalarPredictableInnovationProxy_succ]
  ring

lemma integrable_scalarPredictableInnovationExponential_fiber (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (theta : ℝ) (n : ℕ)
    (p : ScalarObservationHistory n) :
    Integrable (fun y => scalarPredictableInnovationExponential z dt H theta (n + 1) (p, y))
      (scalarObservationStepKernel z (dt n) n p) := by
  simp only [scalarPredictableInnovationExponential_succ, scalarObservationStepKernel_apply]
  exact (integrable_scalarInnovation_compensated_exp _ _ _).const_mul _

lemma integral_scalarPredictableInnovationExponential_fiber_le (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (theta : ℝ) (n : ℕ)
    (p : ScalarObservationHistory n) :
    (∫ y, scalarPredictableInnovationExponential z dt H theta (n + 1) (p, y)
      ∂scalarObservationStepKernel z (dt n) n p) ≤
        scalarPredictableInnovationExponential z dt H theta n p := by
  simp only [scalarPredictableInnovationExponential_succ, scalarObservationStepKernel_apply]
  rw [integral_const_mul]
  exact (mul_le_mul_of_nonneg_left (integral_scalarInnovation_compensated_exp_le _ _ _)
    (Real.exp_pos _).le).trans_eq (mul_one _)

lemma integrable_scalarPredictableInnovationExponential (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (hH : ∀ k, Measurable (H k))
    (theta : ℝ) (n : ℕ) :
    Integrable (scalarPredictableInnovationExponential z dt H theta n)
      (scalarObservationHistoryLaw z dt n) := by
  induction n with
  | zero =>
    have he : scalarPredictableInnovationExponential z dt H theta 0 =
        fun _ : ScalarObservationHistory 0 => (1 : ℝ) := by
      funext p
      simp only [scalarPredictableInnovationExponential, scalarPredictableInnovationSum_zero,
        scalarPredictableInnovationProxy_zero, mul_zero, zero_sub, zero_div, neg_zero, Real.exp_zero]
    rw [he]
    exact integrable_const 1
  | succ n ih =>
    change Integrable (scalarPredictableInnovationExponential z dt H theta (n + 1))
      (scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n)
    apply (Measure.integrable_compProd_iff
      (measurable_scalarPredictableInnovationExponential z dt H hH theta (n + 1)).aestronglyMeasurable).2
    refine ⟨Eventually.of_forall (integrable_scalarPredictableInnovationExponential_fiber z dt H theta n), ?_⟩
    have hm : StronglyMeasurable (fun p : ScalarObservationHistory n => ∫ y,
        ‖scalarPredictableInnovationExponential z dt H theta (n + 1) (p, y)‖
        ∂scalarObservationStepKernel z (dt n) n p) :=
      (measurable_scalarPredictableInnovationExponential z dt H hH theta (n + 1)).norm.stronglyMeasurable
        |>.integral_kernel_prod_right'
    apply ih.mono' hm.aestronglyMeasurable
    apply ae_of_all
    intro p
    have he : (fun y => ‖scalarPredictableInnovationExponential z dt H theta (n + 1) (p, y)‖) =
        fun y => scalarPredictableInnovationExponential z dt H theta (n + 1) (p, y) := by
      funext y
      exact Real.norm_of_nonneg (Real.exp_pos _).le
    rw [he]
    have hn : 0 ≤ ∫ y, scalarPredictableInnovationExponential z dt H theta (n + 1) (p, y)
        ∂scalarObservationStepKernel z (dt n) n p :=
      integral_nonneg (fun y => (Real.exp_pos _).le)
    rw [Real.norm_of_nonneg hn]
    exact integral_scalarPredictableInnovationExponential_fiber_le z dt H theta n p

lemma integral_scalarPredictableInnovationExponential_le_one (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (hH : ∀ k, Measurable (H k))
    (theta : ℝ) (n : ℕ) :
    (∫ p, scalarPredictableInnovationExponential z dt H theta n p
      ∂scalarObservationHistoryLaw z dt n) ≤ 1 := by
  induction n with
  | zero =>
    simp only [scalarPredictableInnovationExponential, scalarPredictableInnovationSum_zero,
      scalarPredictableInnovationProxy_zero, mul_zero, zero_sub, zero_div, neg_zero,
      Real.exp_zero, integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact le_rfl
  | succ n ih =>
    have hi := integrable_scalarPredictableInnovationExponential z dt H hH theta (n + 1)
    change Integrable (scalarPredictableInnovationExponential z dt H theta (n + 1))
      (scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n) at hi
    have hinner := ((Measure.integrable_compProd_iff hi.aestronglyMeasurable).1 hi).2
    have he : (fun p : ScalarObservationHistory n => ∫ y,
        ‖scalarPredictableInnovationExponential z dt H theta (n + 1) (p, y)‖
        ∂scalarObservationStepKernel z (dt n) n p) = fun p => ∫ y,
        scalarPredictableInnovationExponential z dt H theta (n + 1) (p, y)
        ∂scalarObservationStepKernel z (dt n) n p := by
      funext p
      congr 1
      funext y
      exact Real.norm_of_nonneg (Real.exp_pos _).le
    rw [he] at hinner
    change (∫ p, scalarPredictableInnovationExponential z dt H theta (n + 1) p
      ∂scalarObservationHistoryLaw z dt n ⊗ₘ scalarObservationStepKernel z (dt n) n) ≤ 1
    rw [Measure.integral_compProd hi]
    exact (integral_mono_ae hinner
      (integrable_scalarPredictableInnovationExponential z dt H hH theta n)
      (ae_of_all _ (integral_scalarPredictableInnovationExponential_fiber_le z dt H theta n))).trans ih

lemma scalarPredictableInnovation_exp_le_of_proxy_le (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (theta V : ℝ) (n : ℕ)
    (p : ScalarObservationHistory n) (hV : scalarPredictableInnovationProxy dt H n p ≤ V) :
    Real.exp (theta * scalarPredictableInnovationSum z dt H n p) ≤
      Real.exp (theta ^ 2 * V / 2) * scalarPredictableInnovationExponential z dt H theta n p := by
  unfold scalarPredictableInnovationExponential
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hV (sq_nonneg theta)]

lemma integrable_exp_scalarPredictableInnovationSum (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ) (hV : ∀ᵐ p ∂scalarObservationHistoryLaw z dt n,
      scalarPredictableInnovationProxy dt H n p ≤ V) (theta : ℝ) :
    Integrable (fun p => Real.exp (theta * scalarPredictableInnovationSum z dt H n p))
      (scalarObservationHistoryLaw z dt n) := by
  refine ((integrable_scalarPredictableInnovationExponential z dt H hH theta n).const_mul
    (Real.exp (theta ^ 2 * V / 2))).mono'
    ((measurable_scalarPredictableInnovationSum z dt H hH n).const_mul theta).exp.aestronglyMeasurable ?_
  filter_upwards [hV] with p hp
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact scalarPredictableInnovation_exp_le_of_proxy_le z dt H theta V n p hp

lemma mgf_scalarPredictableInnovationSum_le (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ) (hV : ∀ᵐ p ∂scalarObservationHistoryLaw z dt n,
      scalarPredictableInnovationProxy dt H n p ≤ V) (theta : ℝ) :
    mgf (scalarPredictableInnovationSum z dt H n) (scalarObservationHistoryLaw z dt n) theta ≤
      Real.exp (theta ^ 2 * V / 2) := by
  calc
    _ ≤ ∫ p, Real.exp (theta ^ 2 * V / 2) *
        scalarPredictableInnovationExponential z dt H theta n p ∂scalarObservationHistoryLaw z dt n := by
      apply integral_mono_ae (integrable_exp_scalarPredictableInnovationSum z dt H hH n V hV theta)
        ((integrable_scalarPredictableInnovationExponential z dt H hH theta n).const_mul _)
      filter_upwards [hV] with p hp
      exact scalarPredictableInnovation_exp_le_of_proxy_le z dt H theta V n p hp
    _ ≤ _ := by
      rw [integral_const_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (integral_scalarPredictableInnovationExponential_le_one z dt H hH theta n) (Real.exp_pos _).le

lemma scalarPredictableInnovationSum_subgaussian (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ≥0) (hV : ∀ᵐ p ∂scalarObservationHistoryLaw z dt n,
      scalarPredictableInnovationProxy dt H n p ≤ V) :
    HasSubgaussianMGF (scalarPredictableInnovationSum z dt H n) V (scalarObservationHistoryLaw z dt n) where
  integrable_exp_mul theta := integrable_exp_scalarPredictableInnovationSum z dt H hH n V hV theta
  mgf_le theta := by
    simpa only [mul_comm] using mgf_scalarPredictableInnovationSum_le z dt H hH n V hV theta

lemma scalarPredictableInnovationProxy_le_sum (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (b : ℕ → ℝ) (n : ℕ)
    (hstep : ∀ k < n, ∀ p : ScalarObservationHistory k,
      (H k p) ^ 2 * ((dt k : ℝ) + (dt k : ℝ) ^ 2) ≤ b k) (p : ScalarObservationHistory n) :
    scalarPredictableInnovationProxy dt H n p ≤ ∑ k ∈ Finset.range n, b k := by
  induction n with
  | zero => simp only [scalarPredictableInnovationProxy_zero, Finset.sum_range_zero, le_refl]
  | succ n ih =>
    change scalarPredictableInnovationProxy dt H n p.1 +
      (H n p.1) ^ 2 * ((dt n : ℝ) + (dt n : ℝ) ^ 2) ≤ _
    rw [Finset.sum_range_succ]
    exact add_le_add (ih (fun k hk => hstep k (by omega)) p.1) (hstep n (by omega) p.1)

lemma scalarPredictableInnovationProxy_le_duration (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (n : ℕ) (b h : ℝ)
    (hcoef : ∀ k < n, ∀ p : ScalarObservationHistory k, (H k p) ^ 2 ≤ b ^ 2)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1) (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h)
    (p : ScalarObservationHistory n) : scalarPredictableInnovationProxy dt H n p ≤ 2 * b ^ 2 * h := by
  have hstep (k : ℕ) (hk : k < n) (q : ScalarObservationHistory k) :
      (H k q) ^ 2 * ((dt k : ℝ) + (dt k : ℝ) ^ 2) ≤ (2 * b ^ 2) * (dt k : ℝ) := by
    have ht := (dt k).coe_nonneg
    have hsq : (dt k : ℝ) ^ 2 ≤ (dt k : ℝ) := by nlinarith [hdt k hk]
    calc
      _ ≤ b ^ 2 * ((dt k : ℝ) + (dt k : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right (hcoef k hk q) (by positivity)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg b)]
  calc
    _ ≤ ∑ k ∈ Finset.range n, (2 * b ^ 2) * (dt k : ℝ) :=
      scalarPredictableInnovationProxy_le_sum dt H _ n hstep p
    _ = (2 * b ^ 2) * ∑ k ∈ Finset.range n, (dt k : ℝ) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hduration (by positivity)

lemma scalarPredictableInnovationSum_upper_chernoff (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ) (hV : ∀ᵐ p ∂scalarObservationHistoryLaw z dt n,
      scalarPredictableInnovationProxy dt H n p ≤ V) (theta u : ℝ) (htheta : 0 ≤ theta) :
    (scalarObservationHistoryLaw z dt n).real {p | u ≤ scalarPredictableInnovationSum z dt H n p} ≤
      Real.exp (-theta * u + theta ^ 2 * V / 2) := by
  calc
    _ ≤ Real.exp (-theta * u) * mgf (scalarPredictableInnovationSum z dt H n)
        (scalarObservationHistoryLaw z dt n) theta :=
      measure_ge_le_exp_mul_mgf u htheta
        (integrable_exp_scalarPredictableInnovationSum z dt H hH n V hV theta)
    _ ≤ Real.exp (-theta * u) * Real.exp (theta ^ 2 * V / 2) :=
      mul_le_mul_of_nonneg_left (mgf_scalarPredictableInnovationSum_le z dt H hH n V hV theta)
        (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

lemma scalarPredictableInnovationSum_lower_chernoff (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ) (hV : ∀ᵐ p ∂scalarObservationHistoryLaw z dt n,
      scalarPredictableInnovationProxy dt H n p ≤ V) (theta u : ℝ) (htheta : theta ≤ 0) :
    (scalarObservationHistoryLaw z dt n).real {p | scalarPredictableInnovationSum z dt H n p ≤ u} ≤
      Real.exp (-theta * u + theta ^ 2 * V / 2) := by
  calc
    _ ≤ Real.exp (-theta * u) * mgf (scalarPredictableInnovationSum z dt H n)
        (scalarObservationHistoryLaw z dt n) theta :=
      measure_le_le_exp_mul_mgf u htheta
        (integrable_exp_scalarPredictableInnovationSum z dt H hH n V hV theta)
    _ ≤ Real.exp (-theta * u) * Real.exp (theta ^ 2 * V / 2) :=
      mul_le_mul_of_nonneg_left (mgf_scalarPredictableInnovationSum_le z dt H hH n V hV theta)
        (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

lemma scalarPredictableInnovationSum_two_sided_tail (z : ℝ) (dt : ℕ → ℝ≥0)
    (H : ScalarFiniteHistoryCoefficient) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ) (hV : ∀ᵐ p ∂scalarObservationHistoryLaw z dt n,
      scalarPredictableInnovationProxy dt H n p ≤ V) (hVp : 0 < V) (u : ℝ) (hu : 0 ≤ u) :
    (scalarObservationHistoryLaw z dt n).real {p | u ≤ |scalarPredictableInnovationSum z dt H n p|} ≤
      2 * Real.exp (-(u ^ 2 / (2 * V))) := by
  have hup := scalarPredictableInnovationSum_upper_chernoff z dt H hH n V hV (u / V) u
    (div_nonneg hu hVp.le)
  have hdown := scalarPredictableInnovationSum_lower_chernoff z dt H hH n V hV (-u / V) (-u)
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) hVp.le)
  have heup : -(u / V) * u + (u / V) ^ 2 * V / 2 = -(u ^ 2 / (2 * V)) := by field_simp; ring
  have hedown : -(-u / V) * (-u) + (-u / V) ^ 2 * V / 2 = -(u ^ 2 / (2 * V)) := by field_simp; ring
  rw [heup] at hup
  rw [hedown] at hdown
  have hevent : {p : ScalarObservationHistory n | u ≤ |scalarPredictableInnovationSum z dt H n p|} =
      {p | u ≤ scalarPredictableInnovationSum z dt H n p} ∪
        {p | scalarPredictableInnovationSum z dt H n p ≤ -u} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
    constructor <;> intro hp <;> rcases hp with hp | hp
    · exact Or.inl hp
    · exact Or.inr (by linarith)
    · exact Or.inl hp
    · exact Or.inr (by linarith)
  rw [hevent]
  exact (measureReal_union_le _ _).trans (by linarith)

end SKConstants
