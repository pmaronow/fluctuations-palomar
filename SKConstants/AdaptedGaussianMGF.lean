module

public import SKConstants.ConcentrationMGF
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def GaussianHistory : ℕ → Type :=
  Nat.rec (motive := fun _ => Type) PUnit (fun _ history => history × ℝ)

instance gaussianHistoryMeasurableSpace (n : ℕ) : MeasurableSpace (GaussianHistory n) := by
  induction n with
  | zero => exact (inferInstance : MeasurableSpace PUnit)
  | succ n ih => exact @MeasurableSpace.prod (GaussianHistory n) ℝ ih inferInstance

def gaussianHistoryLaw (dt : ℕ → ℝ≥0) : (n : ℕ) → Measure (GaussianHistory n) :=
  Nat.rec (motive := fun n => Measure (GaussianHistory n)) (Measure.dirac PUnit.unit)
    (fun n law => law.prod (gaussianReal 0 (dt n)))

instance gaussianHistoryLaw_isProbability (dt : ℕ → ℝ≥0) (n : ℕ) :
    IsProbabilityMeasure (gaussianHistoryLaw dt n) := by
  induction n with
  | zero => change IsProbabilityMeasure (Measure.dirac PUnit.unit); infer_instance
  | succ n ih =>
    change IsProbabilityMeasure ((gaussianHistoryLaw dt n).prod (gaussianReal 0 (dt n)))
    infer_instance

theorem gaussianHistoryLaw_next_hasLaw (dt : ℕ → ℝ≥0) (n : ℕ) :
    HasLaw (fun z : GaussianHistory (n + 1) => z.2) (gaussianReal 0 (dt n))
      (gaussianHistoryLaw dt (n + 1)) := by
  constructor
  · exact measurable_snd.aemeasurable
  · exact (measurePreserving_snd (μ := gaussianHistoryLaw dt n)
      (ν := gaussianReal 0 (dt n))).map_eq

theorem gaussianHistoryLaw_past_indep_next (dt : ℕ → ℝ≥0) (n : ℕ) :
    IndepFun (β := GaussianHistory n) (γ := ℝ)
      (fun z : GaussianHistory (n + 1) => z.1)
      (fun z : GaussianHistory (n + 1) => z.2) (gaussianHistoryLaw dt (n + 1)) :=
  indepFun_prod (Ω := GaussianHistory n) (Ω' := ℝ)
    (μ := gaussianHistoryLaw dt n) (ν := gaussianReal 0 (dt n)) measurable_id measurable_id

abbrev GaussianPredictableCoefficient := (k : ℕ) → GaussianHistory k → ℝ

def adaptedGaussianSum (H : GaussianPredictableCoefficient) :
    (n : ℕ) → GaussianHistory n → ℝ
  | 0, _ => 0
  | n + 1, z => adaptedGaussianSum H n z.1 + H n z.1 * z.2

def adaptedGaussianQuadraticVariation (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) : (n : ℕ) → GaussianHistory n → ℝ
  | 0, _ => 0
  | n + 1, z => adaptedGaussianQuadraticVariation dt H n z.1 +
      (H n z.1) ^ 2 * (dt n : ℝ)

def adaptedGaussianExponential (dt : ℕ → ℝ≥0) (H : GaussianPredictableCoefficient)
    (theta : ℝ) (n : ℕ) (z : GaussianHistory n) : ℝ :=
  Real.exp (theta * adaptedGaussianSum H n z -
    theta ^ 2 * adaptedGaussianQuadraticVariation dt H n z / 2)

theorem measurable_adaptedGaussianSum (H : GaussianPredictableCoefficient)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) : Measurable (adaptedGaussianSum H n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp measurable_fst).add ((hH n).comp measurable_fst |>.mul measurable_snd)

theorem measurable_adaptedGaussianQuadraticVariation (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    Measurable (adaptedGaussianQuadraticVariation dt H n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact (ih.comp measurable_fst).add
      (((hH n).comp measurable_fst).pow_const 2 |>.mul_const (dt n : ℝ))

theorem measurable_adaptedGaussianExponential (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (hH : ∀ k, Measurable (H k))
    (theta : ℝ) (n : ℕ) : Measurable (adaptedGaussianExponential dt H theta n) := by
  exact ((measurable_adaptedGaussianSum H hH n).const_mul theta |>.sub
    ((measurable_adaptedGaussianQuadraticVariation dt H hH n).const_mul
      (theta ^ 2) |>.div_const 2)).exp

theorem adaptedGaussianQuadraticVariation_nonneg (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (n : ℕ) (z : GaussianHistory n) :
    0 ≤ adaptedGaussianQuadraticVariation dt H n z := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact add_nonneg (ih z.1) (mul_nonneg (sq_nonneg _) (dt n).coe_nonneg)

theorem integrable_gaussian_compensated_exp (v : ℝ≥0) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x - (v : ℝ) * t ^ 2 / 2))
      (gaussianReal 0 v) := by
  have he : (fun x : ℝ => Real.exp (t * x - (v : ℝ) * t ^ 2 / 2)) =
      fun x => Real.exp (-((v : ℝ) * t ^ 2 / 2)) * Real.exp (t * x) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact (integrable_exp_mul_gaussianReal (μ := 0) (v := v) t).const_mul _

theorem integral_gaussian_compensated_exp (v : ℝ≥0) (t : ℝ) :
    (∫ x : ℝ, Real.exp (t * x - (v : ℝ) * t ^ 2 / 2) ∂gaussianReal 0 v) = 1 := by
  simp_rw [Real.exp_sub]
  rw [integral_div]
  have hm : (∫ x : ℝ, Real.exp (t * x) ∂gaussianReal 0 v) =
      Real.exp ((v : ℝ) * t ^ 2 / 2) := by
    simpa only [mgf, zero_mul, zero_add] using
      congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := v)) t
  rw [hm, div_self (Real.exp_pos _).ne']

theorem adaptedGaussianExponential_succ (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (theta : ℝ) (n : ℕ)
    (z : GaussianHistory n) (x : ℝ) :
    adaptedGaussianExponential dt H theta (n + 1) (z, x) =
      adaptedGaussianExponential dt H theta n z *
        Real.exp ((theta * H n z) * x - (dt n : ℝ) * (theta * H n z) ^ 2 / 2) := by
  unfold adaptedGaussianExponential
  rw [← Real.exp_add]
  congr 1
  simp only [adaptedGaussianSum, adaptedGaussianQuadraticVariation]
  ring

theorem integrable_adaptedGaussianExponential_fiber (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (theta : ℝ) (n : ℕ) (z : GaussianHistory n) :
    Integrable (fun x : ℝ => adaptedGaussianExponential dt H theta (n + 1) (z, x))
      (gaussianReal 0 (dt n)) := by
  simp only [adaptedGaussianExponential_succ]
  exact (integrable_gaussian_compensated_exp (dt n) (theta * H n z)).const_mul _

theorem integral_adaptedGaussianExponential_fiber (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (theta : ℝ) (n : ℕ) (z : GaussianHistory n) :
    (∫ x : ℝ, adaptedGaussianExponential dt H theta (n + 1) (z, x)
      ∂gaussianReal 0 (dt n)) = adaptedGaussianExponential dt H theta n z := by
  simp only [adaptedGaussianExponential_succ]
  rw [integral_const_mul, integral_gaussian_compensated_exp, mul_one]

theorem integrable_adaptedGaussianExponential (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (hH : ∀ k, Measurable (H k))
    (theta : ℝ) (n : ℕ) :
    Integrable (adaptedGaussianExponential dt H theta n) (gaussianHistoryLaw dt n) := by
  induction n with
  | zero =>
    have he : adaptedGaussianExponential dt H theta 0 =
        fun _ : GaussianHistory 0 => (1 : ℝ) := by
      funext z
      simp [adaptedGaussianExponential, adaptedGaussianSum, adaptedGaussianQuadraticVariation]
    rw [he]
    exact integrable_const 1
  | succ n ih =>
    change Integrable (adaptedGaussianExponential dt H theta (n + 1))
      ((gaussianHistoryLaw dt n).prod (gaussianReal 0 (dt n)))
    apply (integrable_prod_iff (α := GaussianHistory n) (β := ℝ)
      (μ := gaussianHistoryLaw dt n) (ν := gaussianReal 0 (dt n))
      (measurable_adaptedGaussianExponential dt H hH theta (n + 1)).aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall (integrable_adaptedGaussianExponential_fiber dt H theta n)
    · have he : (fun z : GaussianHistory n => ∫ x : ℝ,
          ‖adaptedGaussianExponential dt H theta (n + 1) (z, x)‖
          ∂gaussianReal 0 (dt n)) = adaptedGaussianExponential dt H theta n := by
        funext z
        simp only [Real.norm_eq_abs, adaptedGaussianExponential, abs_of_pos (Real.exp_pos _)]
        exact integral_adaptedGaussianExponential_fiber dt H theta n z
      rw [he]
      exact ih

theorem integral_adaptedGaussianExponential_eq_one (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (hH : ∀ k, Measurable (H k))
    (theta : ℝ) (n : ℕ) :
    (∫ z, adaptedGaussianExponential dt H theta n z ∂gaussianHistoryLaw dt n) = 1 := by
  induction n with
  | zero => simp [adaptedGaussianExponential, adaptedGaussianSum,
      adaptedGaussianQuadraticVariation]
  | succ n ih =>
    change (∫ z, adaptedGaussianExponential dt H theta (n + 1) z
      ∂(gaussianHistoryLaw dt n).prod (gaussianReal 0 (dt n))) = 1
    rw [integral_prod (α := GaussianHistory n) (β := ℝ)
      (μ := gaussianHistoryLaw dt n) (ν := gaussianReal 0 (dt n)) _
      (integrable_adaptedGaussianExponential dt H hH theta (n + 1))]
    simp_rw [integral_adaptedGaussianExponential_fiber]
    exact ih

theorem adaptedGaussian_exp_le_of_quadraticVariation_le (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (theta V : ℝ) (n : ℕ)
    (z : GaussianHistory n) (hV : adaptedGaussianQuadraticVariation dt H n z ≤ V) :
    Real.exp (theta * adaptedGaussianSum H n z) ≤
      Real.exp (theta ^ 2 * V / 2) * adaptedGaussianExponential dt H theta n z := by
  unfold adaptedGaussianExponential
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hV (sq_nonneg theta)]

theorem integrable_exp_adaptedGaussianSum (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ)
    (hV : ∀ᵐ z ∂gaussianHistoryLaw dt n,
      adaptedGaussianQuadraticVariation dt H n z ≤ V) (theta : ℝ) :
    Integrable (fun z => Real.exp (theta * adaptedGaussianSum H n z))
      (gaussianHistoryLaw dt n) := by
  refine ((integrable_adaptedGaussianExponential dt H hH theta n).const_mul
    (Real.exp (theta ^ 2 * V / 2))).mono'
    ((measurable_adaptedGaussianSum H hH n).const_mul theta).exp.aestronglyMeasurable ?_
  filter_upwards [hV] with z hz
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact adaptedGaussian_exp_le_of_quadraticVariation_le dt H theta V n z hz

theorem mgf_adaptedGaussianSum_le (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ)
    (hV : ∀ᵐ z ∂gaussianHistoryLaw dt n,
      adaptedGaussianQuadraticVariation dt H n z ≤ V) (theta : ℝ) :
    mgf (adaptedGaussianSum H n) (gaussianHistoryLaw dt n) theta ≤
      Real.exp (theta ^ 2 * V / 2) := by
  calc
    _ ≤ ∫ z, Real.exp (theta ^ 2 * V / 2) *
        adaptedGaussianExponential dt H theta n z ∂gaussianHistoryLaw dt n := by
      apply integral_mono_ae (integrable_exp_adaptedGaussianSum dt H hH n V hV theta)
        ((integrable_adaptedGaussianExponential dt H hH theta n).const_mul _)
      filter_upwards [hV] with z hz
      exact adaptedGaussian_exp_le_of_quadraticVariation_le dt H theta V n z hz
    _ = _ := by
      rw [integral_const_mul, integral_adaptedGaussianExponential_eq_one dt H hH, mul_one]

theorem localQuadraticMGF_adaptedGaussianSum (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V radius : ℝ)
    (hV : ∀ᵐ z ∂gaussianHistoryLaw dt n,
      adaptedGaussianQuadraticVariation dt H n z ≤ V) :
    Concentration.LocalQuadraticMGF (adaptedGaussianSum H n) (gaussianHistoryLaw dt n)
      (V / 2) radius where
  integrable_exp_mul theta _ := integrable_exp_adaptedGaussianSum dt H hH n V hV theta
  mgf_le theta _ := by
    convert mgf_adaptedGaussianSum_le dt H hH n V hV theta using 1
    congr 1
    ring

theorem adaptedGaussianSum_upper_chernoff (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ)
    (hV : ∀ᵐ z ∂gaussianHistoryLaw dt n,
      adaptedGaussianQuadraticVariation dt H n z ≤ V)
    (theta u : ℝ) (htheta : 0 ≤ theta) :
    (gaussianHistoryLaw dt n).real {z | u ≤ adaptedGaussianSum H n z} ≤
      Real.exp (-theta * u + theta ^ 2 * V / 2) := by
  calc
    _ ≤ Real.exp (-theta * u) * mgf (adaptedGaussianSum H n) (gaussianHistoryLaw dt n) theta :=
      measure_ge_le_exp_mul_mgf u htheta
        (integrable_exp_adaptedGaussianSum dt H hH n V hV theta)
    _ ≤ Real.exp (-theta * u) * Real.exp (theta ^ 2 * V / 2) :=
      mul_le_mul_of_nonneg_left (mgf_adaptedGaussianSum_le dt H hH n V hV theta)
        (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

theorem adaptedGaussianSum_lower_chernoff (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ)
    (hV : ∀ᵐ z ∂gaussianHistoryLaw dt n,
      adaptedGaussianQuadraticVariation dt H n z ≤ V)
    (theta u : ℝ) (htheta : theta ≤ 0) :
    (gaussianHistoryLaw dt n).real {z | adaptedGaussianSum H n z ≤ u} ≤
      Real.exp (-theta * u + theta ^ 2 * V / 2) := by
  calc
    _ ≤ Real.exp (-theta * u) * mgf (adaptedGaussianSum H n) (gaussianHistoryLaw dt n) theta :=
      measure_le_le_exp_mul_mgf u htheta
        (integrable_exp_adaptedGaussianSum dt H hH n V hV theta)
    _ ≤ Real.exp (-theta * u) * Real.exp (theta ^ 2 * V / 2) :=
      mul_le_mul_of_nonneg_left (mgf_adaptedGaussianSum_le dt H hH n V hV theta)
        (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

theorem adaptedGaussianSum_upper_tail (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ)
    (hV : ∀ᵐ z ∂gaussianHistoryLaw dt n,
      adaptedGaussianQuadraticVariation dt H n z ≤ V)
    (hVp : 0 < V) (u : ℝ) (hu : 0 ≤ u) :
    (gaussianHistoryLaw dt n).real {z | u ≤ adaptedGaussianSum H n z} ≤
      Real.exp (-(u ^ 2 / (2 * V))) := by
  have ht := adaptedGaussianSum_upper_chernoff dt H hH n V hV (u / V) u
    (div_nonneg hu hVp.le)
  convert ht using 1
  congr 1
  field_simp
  ring

theorem adaptedGaussianSum_two_sided_tail (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (hH : ∀ k, Measurable (H k))
    (n : ℕ) (V : ℝ)
    (hV : ∀ᵐ z ∂gaussianHistoryLaw dt n,
      adaptedGaussianQuadraticVariation dt H n z ≤ V)
    (hVp : 0 < V) (u : ℝ) (hu : 0 ≤ u) :
    (gaussianHistoryLaw dt n).real {z | u ≤ |adaptedGaussianSum H n z|} ≤
      2 * Real.exp (-(u ^ 2 / (2 * V))) := by
  have hup := adaptedGaussianSum_upper_tail dt H hH n V hV hVp u hu
  have hdown := adaptedGaussianSum_lower_chernoff dt H hH n V hV (-u / V) (-u)
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hu) hVp.le)
  have he : -(-u / V) * (-u) + (-u / V) ^ 2 * V / 2 = -(u ^ 2 / (2 * V)) := by
    field_simp
    ring
  rw [he] at hdown
  have hevent : {z : GaussianHistory n | u ≤ |adaptedGaussianSum H n z|} =
      {z | u ≤ adaptedGaussianSum H n z} ∪ {z | adaptedGaussianSum H n z ≤ -u} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
    constructor <;> intro hz
    · rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (by linarith)
    · rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (by linarith)
  rw [hevent]
  exact (measureReal_union_le _ _).trans (by linarith)

theorem adaptedGaussianQuadraticVariation_le_sum (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (b : ℕ → ℝ) (n : ℕ)
    (hstep : ∀ k < n, ∀ z : GaussianHistory k, (H k z) ^ 2 * (dt k : ℝ) ≤ b k)
    (z : GaussianHistory n) :
    adaptedGaussianQuadraticVariation dt H n z ≤ ∑ k ∈ Finset.range n, b k := by
  induction n with
  | zero => simp [adaptedGaussianQuadraticVariation]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    exact add_le_add (ih (fun k hk => hstep k (by omega)) z.1) (hstep n (by omega) z.1)

theorem mgf_adaptedGaussianSum_le_of_step_budget (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (hH : ∀ k, Measurable (H k))
    (b : ℕ → ℝ) (n : ℕ)
    (hstep : ∀ k < n, ∀ z : GaussianHistory k, (H k z) ^ 2 * (dt k : ℝ) ≤ b k)
    (theta : ℝ) :
    mgf (adaptedGaussianSum H n) (gaussianHistoryLaw dt n) theta ≤
      Real.exp (theta ^ 2 * (∑ k ∈ Finset.range n, b k) / 2) :=
  mgf_adaptedGaussianSum_le dt H hH n _
    (Filter.Eventually.of_forall (adaptedGaussianQuadraticVariation_le_sum dt H b n hstep)) theta

theorem mgf_adaptedGaussianSum_le_of_coefficient_bound (dt : ℕ → ℝ≥0)
    (H : GaussianPredictableCoefficient) (hH : ∀ k, Measurable (H k))
    (a : ℕ → ℝ) (n : ℕ)
    (hbound : ∀ k < n, ∀ z : GaussianHistory k, |H k z| ≤ a k) (theta : ℝ) :
    mgf (adaptedGaussianSum H n) (gaussianHistoryLaw dt n) theta ≤
      Real.exp (theta ^ 2 * (∑ k ∈ Finset.range n, (a k) ^ 2 * (dt k : ℝ)) / 2) := by
  apply mgf_adaptedGaussianSum_le_of_step_budget dt H hH _ n _ theta
  intro k hk z
  have hs := pow_le_pow_left₀ (abs_nonneg (H k z)) (hbound k hk z) 2
  rw [sq_abs] at hs
  exact mul_le_mul_of_nonneg_right hs (dt k).coe_nonneg

end SKConstants
