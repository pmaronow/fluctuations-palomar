module
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

public section
noncomputable section

namespace SKConstants
open MeasureTheory Filter Set
open scoped NNReal

@[expose] def parisiIntegralPartition (μ : Measure ℝ) (ell : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, Real.exp (ell * f (x + z)) ∂μ
@[expose] def parisiIntegralNumerator (μ : Measure ℝ) (ell : ℝ) (f p : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, Real.exp (ell * f (x + z)) * p (x + z) ∂μ
@[expose] def parisiIntegralSecondNumerator (μ : Measure ℝ) (ell : ℝ)
    (f p a : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ z, Real.exp (ell * f (x + z)) * (a (x + z) + ell * p (x + z) ^ 2) ∂μ

lemma parisi_profile_bounds (p a : ℝ → ℝ)
    (ha : ∀ y, 0 ≤ a y ∧ a y ≤ 1 - p y ^ 2) :
    (∀ y, |p y| ≤ 1) ∧ (∀ y, |a y| ≤ 1) := by
  constructor
  · intro y
    apply abs_le.mpr
    constructor <;> nlinarith [(ha y).1, (ha y).2]
  · intro y
    rw [abs_of_nonneg (ha y).1]
    nlinarith [(ha y).2, sq_nonneg (p y)]

theorem parisiIntegral_partition_derivatives (μ : Measure ℝ) (ell : ℝ)
    (f p a : ℝ → ℝ) (x₀ : ℝ)
    (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (hf : ∀ y, HasDerivAt f (p y) y)
    (hp : ∀ y, HasDerivAt p (a y) y) (hac : Continuous a)
    (ha : ∀ y, 0 ≤ a y ∧ a y ≤ 1 - p y ^ 2)
    (hi : Integrable (fun z => Real.exp (ell * f (x₀ + z))) μ) :
    HasDerivAt (parisiIntegralPartition μ ell f)
      (ell * parisiIntegralNumerator μ ell f p x₀) x₀ ∧
    HasDerivAt (parisiIntegralNumerator μ ell f p)
      (parisiIntegralSecondNumerator μ ell f p a x₀) x₀ := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun y => (hf y).continuousAt
  have hpc : Continuous p := continuous_iff_continuousAt.mpr fun y => (hp y).continuousAt
  obtain ⟨hpb, hab⟩ := parisi_profile_bounds p a ha
  have hLip (x y : ℝ) : |f x - f y| ≤ |x - y| := by
    have hh := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (hf t).hasDerivWithinAt) (fun t _ => by simpa only [Real.norm_eq_abs] using hpb t)
      (mem_univ y) (mem_univ x)
    simpa only [Real.norm_eq_abs, one_mul] using hh
  let F : ℝ → ℝ → ℝ := fun x z => Real.exp (ell * f (x + z))
  let F' : ℝ → ℝ → ℝ := fun x z => ell * Real.exp (ell * f (x + z)) * p (x + z)
  let A : ℝ → ℝ → ℝ := fun x z => Real.exp (ell * f (x + z)) * p (x + z)
  let A' : ℝ → ℝ → ℝ := fun x z => Real.exp (ell * f (x + z)) *
    (a (x + z) + ell * p (x + z) ^ 2)
  let b : ℝ → ℝ := fun z => 2 * Real.exp 1 * F x₀ z
  have hb : Integrable b μ := hi.const_mul (2 * Real.exp 1)
  have hFm (x : ℝ) : AEStronglyMeasurable (F x) μ := by
    apply Continuous.aestronglyMeasurable
    dsimp [F]
    fun_prop
  have hAm (x : ℝ) : AEStronglyMeasurable (A x) μ := by
    apply Continuous.aestronglyMeasurable
    dsimp [A]
    fun_prop
  have hF'm : AEStronglyMeasurable (F' x₀) μ := by
    apply Continuous.aestronglyMeasurable
    dsimp [F']
    fun_prop
  have hA'm : AEStronglyMeasurable (A' x₀) μ := by
    apply Continuous.aestronglyMeasurable
    dsimp [A']
    fun_prop
  have hAi : Integrable (A x₀) μ := hi.mono' (hAm x₀) (Eventually.of_forall fun z => by
    dsimp [A]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (hpb _) (Real.exp_pos _).le).trans (by simp))
  have hdom (x z : ℝ) (hx : x ∈ Metric.ball x₀ 1) : F x z ≤ Real.exp 1 * F x₀ z := by
    have hdist : |x - x₀| < 1 := by simpa only [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] using hx
    have hh := hLip (x + z) (x₀ + z)
    have hsub : (x + z) - (x₀ + z) = x - x₀ := by ring
    rw [hsub] at hh
    have hfd : f (x + z) - f (x₀ + z) ≤ 1 := by linarith [le_abs_self (f (x + z) - f (x₀ + z))]
    have hm := mul_le_mul_of_nonneg_left hfd hell
    have harg : ell * f (x + z) ≤ 1 + ell * f (x₀ + z) := by nlinarith
    dsimp [F]
    simpa only [Real.exp_add] using Real.exp_le_exp.mpr harg
  have hFb (z : ℝ) (x : ℝ) (hx : x ∈ Metric.ball x₀ 1) : ‖F' x z‖ ≤ b z := by
    have hm := mul_le_mul_of_nonneg_left (hpb (x + z)) (show 0 ≤ ell * F x z by dsimp [F]; positivity)
    have hd := hdom x z hx
    have hmell := mul_le_mul_of_nonneg_right hell1 (show 0 ≤ F x z by dsimp [F]; positivity)
    dsimp [F', b, F] at *
    rw [abs_mul, abs_mul, abs_of_nonneg hell, abs_of_pos (Real.exp_pos _)]
    nlinarith [Real.exp_pos (ell * f (x₀ + z)), Real.exp_pos 1]
  have hAb (z : ℝ) (x : ℝ) (hx : x ∈ Metric.ball x₀ 1) : ‖A' x z‖ ≤ b z := by
    have hp2 : p (x + z) ^ 2 ≤ 1 := by nlinarith [(ha (x + z)).1, (ha (x + z)).2]
    have hterm : 0 ≤ a (x + z) + ell * p (x + z) ^ 2 := add_nonneg (ha _).1 (mul_nonneg hell (sq_nonneg _))
    have hterm2 : a (x + z) + ell * p (x + z) ^ 2 ≤ 2 := by
      have hm := mul_le_mul_of_nonneg_left hp2 hell
      nlinarith [(ha (x + z)).2, sq_nonneg (p (x + z))]
    have hm := mul_le_mul_of_nonneg_left hterm2 (show 0 ≤ F x z by dsimp [F]; positivity)
    have hd := hdom x z hx
    dsimp [A', b, F] at *
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hterm]
    nlinarith
  have hFd (z x : ℝ) : HasDerivAt (fun y => F y z) (F' x z) x := by
    have hh := (((hf (x + z)).comp x ((hasDerivAt_id x).add_const z)).const_mul ell).exp
    convert hh using 1 <;> dsimp [F, F']
    ring
  have hAd (z x : ℝ) : HasDerivAt (fun y => A y z) (A' x z) x := by
    have hh := (((((hf (x + z)).comp x ((hasDerivAt_id x).add_const z)).const_mul ell).exp).mul
      ((hp (x + z)).comp x ((hasDerivAt_id x).add_const z)))
    convert hh using 1
    · funext y
      rfl
    · dsimp [A']
      ring
  obtain ⟨_, hZ⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (bound := b) (Metric.ball_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall hFm) hi hF'm (Eventually.of_forall hFb) hb
    (Eventually.of_forall fun z x _ => hFd z x)
  obtain ⟨_, hA⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := A) (F' := A') (bound := b) (Metric.ball_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall hAm) hAi hA'm (Eventually.of_forall hAb) hb
    (Eventually.of_forall fun z x _ => hAd z x)
  have heq : (∫ z, F' x₀ z ∂μ) = ell * parisiIntegralNumerator μ ell f p x₀ := by
    dsimp [F', parisiIntegralNumerator]
    simp only [mul_assoc, integral_const_mul]
  rw [heq] at hZ
  exact ⟨hZ, hA⟩

lemma parisi_bounded_weighted_integrable (μ : Measure ℝ) (t p : ℝ → ℝ)
    (hi : Integrable t μ) (ht : ∀ z, 0 ≤ t z) (hpc : Continuous p)
    (hb : ∀ z, |p z| ≤ 1) : Integrable (fun z => t z * p z) μ := by
  apply hi.mono' (hi.aestronglyMeasurable.mul hpc.aestronglyMeasurable)
  apply Eventually.of_forall
  intro z
  rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_nonneg (ht z)]
  exact (mul_le_mul_of_nonneg_left (hb z) (ht z)).trans (by simp)

theorem parisi_integral_curvature_le (μ : Measure ℝ) (t p a : ℝ → ℝ) (ell : ℝ)
    (hi : Integrable t μ) (ht : ∀ z, 0 ≤ t z) (htsum : ∫ z, t z ∂μ = 1)
    (hpc : Continuous p) (hac : Continuous a) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (ha : ∀ z, 0 ≤ a z ∧ a z ≤ 1 - p z ^ 2) :
    0 ≤ (∫ z, t z * a z ∂μ) + ell * ((∫ z, t z * p z ^ 2 ∂μ) - (∫ z, t z * p z ∂μ) ^ 2) ∧
    (∫ z, t z * a z ∂μ) + ell * ((∫ z, t z * p z ^ 2 ∂μ) - (∫ z, t z * p z ∂μ) ^ 2) ≤
      1 - (∫ z, t z * p z ∂μ) ^ 2 := by
  obtain ⟨hpb, hab⟩ := parisi_profile_bounds p a ha
  have hp2 : ∀ z, |p z ^ 2| ≤ 1 := by
    intro z
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [(ha z).1, (ha z).2]
  have hM := parisi_bounded_weighted_integrable μ t p hi ht hpc hpb
  have hP := parisi_bounded_weighted_integrable μ t (fun z => p z ^ 2) hi ht (hpc.pow 2) hp2
  have hA := parisi_bounded_weighted_integrable μ t a hi ht hac hab
  let m := ∫ z, t z * p z ∂μ
  have hvarEq : (∫ z, t z * (p z - m) ^ 2 ∂μ) = (∫ z, t z * p z ^ 2 ∂μ) - m ^ 2 := by
    calc
      _ = ∫ z, (t z * p z ^ 2 - (2 * m) * (t z * p z) + m ^ 2 * t z) ∂μ := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro z
        ring
      _ = _ := by
        have hsplit := integral_add (hP.sub (hM.const_mul (2 * m))) (hi.const_mul (m ^ 2))
        simp only [Pi.sub_apply] at hsplit
        rw [hsplit, integral_sub hP (hM.const_mul (2 * m)), integral_const_mul, integral_const_mul, htsum]
        dsimp [m]
        ring
  have hvar : 0 ≤ (∫ z, t z * p z ^ 2 ∂μ) - m ^ 2 := by
    rw [← hvarEq]
    exact integral_nonneg fun z => mul_nonneg (ht z) (sq_nonneg _)
  have hAnon : 0 ≤ ∫ z, t z * a z ∂μ := integral_nonneg fun z => mul_nonneg (ht z) (ha z).1
  have hAle : (∫ z, t z * a z ∂μ) ≤ 1 - ∫ z, t z * p z ^ 2 ∂μ := by
    calc
      _ ≤ ∫ z, t z - t z * p z ^ 2 ∂μ := integral_mono hA (hi.sub hP) fun z => by
        have hm := mul_le_mul_of_nonneg_left (ha z).2 (ht z)
        nlinarith
      _ = _ := by rw [integral_sub hi hP, htsum]
  have hm := mul_le_mul_of_nonneg_right hell1 hvar
  exact ⟨add_nonneg hAnon (mul_nonneg hell hvar), by dsimp [m] at *; nlinarith⟩

theorem parisiIntegral_curvature_bound (μ : Measure ℝ) [NeZero μ] (ell : ℝ)
    (f p a : ℝ → ℝ) (x : ℝ)
    (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (hpc : Continuous p) (hac : Continuous a)
    (ha : ∀ y, 0 ≤ a y ∧ a y ≤ 1 - p y ^ 2)
    (hi : Integrable (fun z => Real.exp (ell * f (x + z))) μ) :
    0 ≤ parisiIntegralSecondNumerator μ ell f p a x / parisiIntegralPartition μ ell f x -
        ell * (parisiIntegralNumerator μ ell f p x / parisiIntegralPartition μ ell f x) ^ 2 ∧
    parisiIntegralSecondNumerator μ ell f p a x / parisiIntegralPartition μ ell f x -
        ell * (parisiIntegralNumerator μ ell f p x / parisiIntegralPartition μ ell f x) ^ 2 ≤
      1 - (parisiIntegralNumerator μ ell f p x / parisiIntegralPartition μ ell f x) ^ 2 := by
  let Z := parisiIntegralPartition μ ell f x
  let t : ℝ → ℝ := fun z => Real.exp (ell * f (x + z)) / Z
  have hZ : 0 < Z := integral_exp_pos hi
  have ht : ∀ z, 0 ≤ t z := fun z => div_nonneg (Real.exp_pos _).le hZ.le
  have hti : Integrable t μ := hi.div_const Z
  have htsum : ∫ z, t z ∂μ = 1 := by
    dsimp [t]
    rw [integral_div]
    exact div_self hZ.ne'
  let pp : ℝ → ℝ := fun z => p (x + z)
  let aa : ℝ → ℝ := fun z => a (x + z)
  have hppc : Continuous pp := hpc.comp (continuous_const.add continuous_id)
  have haac : Continuous aa := hac.comp (continuous_const.add continuous_id)
  obtain ⟨hpb, hab⟩ := parisi_profile_bounds pp aa (fun z => ha (x + z))
  have hP := parisi_bounded_weighted_integrable μ t (fun z => pp z ^ 2) hti ht (hppc.pow 2) (fun z => by
    rw [abs_of_nonneg (sq_nonneg _)]
    dsimp [pp]
    nlinarith [(ha (x + z)).1, (ha (x + z)).2])
  have hA := parisi_bounded_weighted_integrable μ t aa hti ht haac hab
  have hM : (∫ z, t z * pp z ∂μ) = parisiIntegralNumerator μ ell f p x / Z := by
    dsimp [t, pp, parisiIntegralNumerator]
    simp_rw [div_mul_eq_mul_div]
    rw [integral_div]
  have hB : parisiIntegralSecondNumerator μ ell f p a x / Z =
      (∫ z, t z * aa z ∂μ) + ell * ∫ z, t z * pp z ^ 2 ∂μ := by
    dsimp [parisiIntegralSecondNumerator]
    rw [← integral_div]
    calc
      _ = ∫ z, (t z * aa z + ell * (t z * pp z ^ 2)) ∂μ := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro z
        dsimp [t, pp, aa]
        ring
      _ = _ := by rw [integral_add hA (hP.const_mul ell), integral_const_mul]
  have hb := parisi_integral_curvature_le μ t pp aa ell hti ht htsum hppc haac hell hell1
    (fun z => ha (x + z))
  rw [hM] at hb
  have heq : parisiIntegralSecondNumerator μ ell f p a x / Z -
      ell * (parisiIntegralNumerator μ ell f p x / Z) ^ 2 =
      (∫ z, t z * aa z ∂μ) + ell * ((∫ z, t z * pp z ^ 2 ∂μ) -
        (parisiIntegralNumerator μ ell f p x / Z) ^ 2) := by rw [hB]; ring
  change 0 ≤ parisiIntegralSecondNumerator μ ell f p a x / Z -
    ell * (parisiIntegralNumerator μ ell f p x / Z) ^ 2 ∧ _
  rw [heq]
  exact hb

theorem parisiGaussian_exp_integrable (center : ℝ) (variance : ℝ≥0)
    (ell : ℝ) (f p a : ℝ → ℝ) (x : ℝ)
    (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (hf : ∀ y, HasDerivAt f (p y) y)
    (ha : ∀ y, 0 ≤ a y ∧ a y ≤ 1 - p y ^ 2) :
    Integrable (fun z => Real.exp (ell * f (x + z))) (ProbabilityTheory.gaussianReal center variance) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun y => (hf y).continuousAt
  obtain ⟨hpb, _⟩ := parisi_profile_bounds p a ha
  have hLip (z : ℝ) : |f (x + z) - f x| ≤ |z| := by
    have hh := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (hf t).hasDerivWithinAt) (fun t _ => by simpa only [Real.norm_eq_abs] using hpb t)
      (mem_univ x) (mem_univ (x + z))
    simpa only [Real.norm_eq_abs, one_mul, add_sub_cancel_left] using hh
  have hd (z : ℝ) : Real.exp (ell * f (x + z)) ≤
      Real.exp (ell * f x) * (Real.exp z + Real.exp (-z)) := by
    have harg : ell * f (x + z) ≤ ell * f x + |z| := by
      have hm := mul_le_mul_of_nonneg_left (hLip z) hell
      have hm' := mul_le_mul_of_nonneg_right hell1 (abs_nonneg z)
      nlinarith [le_abs_self (f (x + z) - f x)]
    have hExp := Real.exp_le_exp.mpr harg
    rw [Real.exp_add] at hExp
    have hAbs : Real.exp |z| ≤ Real.exp z + Real.exp (-z) := by
      by_cases hz : 0 ≤ z
      · rw [abs_of_nonneg hz]
        linarith [Real.exp_pos (-z)]
      · rw [abs_of_neg (lt_of_not_ge hz)]
        linarith [Real.exp_pos z]
    exact hExp.trans (mul_le_mul_of_nonneg_left hAbs (Real.exp_pos _).le)
  have hi : Integrable (fun z => Real.exp z + Real.exp (-z))
      (ProbabilityTheory.gaussianReal center variance) := by
    have hh := (ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := center) (v := variance) 1).add
      (ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := center) (v := variance) (-1))
    have hfun : ((fun z : ℝ => Real.exp (1 * z)) + (fun z : ℝ => Real.exp ((-1) * z))) =
        (fun z => Real.exp z + Real.exp (-z)) := by
      funext z
      simp only [Pi.add_apply, one_mul, neg_one_mul]
    rw [hfun] at hh
    exact hh
  apply (hi.const_mul (Real.exp (ell * f x))).mono'
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · exact Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hd z

theorem parisiGaussian_profile_integrable (center : ℝ) (variance : ℝ≥0)
    (f p a : ℝ → ℝ) (x : ℝ)
    (hf : ∀ y, HasDerivAt f (p y) y)
    (ha : ∀ y, 0 ≤ a y ∧ a y ≤ 1 - p y ^ 2) :
    Integrable (fun z => f (x + z)) (ProbabilityTheory.gaussianReal center variance) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun y => (hf y).continuousAt
  obtain ⟨hpb, _⟩ := parisi_profile_bounds p a ha
  have hLip (z : ℝ) : |f (x + z) - f x| ≤ |z| := by
    have hh := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (hf t).hasDerivWithinAt) (fun t _ => by simpa only [Real.norm_eq_abs] using hpb t)
      (mem_univ x) (mem_univ (x + z))
    simpa only [Real.norm_eq_abs, one_mul, add_sub_cancel_left] using hh
  have hi : Integrable id (ProbabilityTheory.gaussianReal center variance) :=
    memLp_one_iff_integrable.mp (by
      simpa using (ProbabilityTheory.memLp_id_gaussianReal (μ := center) (v := variance) 1))
  apply ((integrable_const (|f x|)).add hi.norm).mono'
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · apply Eventually.of_forall
    intro z
    have hh := abs_add_le (f (x + z) - f x) (f x)
    rw [sub_add_cancel] at hh
    change |f (x + z)| ≤ |f x| + |z|
    exact hh.trans (by linarith [hLip z])

@[expose] def parisiIntegralStep (μ : Measure ℝ) (ell : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if ell = 0 then ∫ z, f (x + z) ∂μ else Real.log (parisiIntegralPartition μ ell f x) / ell
@[expose] def parisiIntegralSlope (μ : Measure ℝ) (ell : ℝ) (f p : ℝ → ℝ) (x : ℝ) : ℝ :=
  if ell = 0 then ∫ z, p (x + z) ∂μ else parisiIntegralNumerator μ ell f p x / parisiIntegralPartition μ ell f x
@[expose] def parisiIntegralCurvature (μ : Measure ℝ) (ell : ℝ) (f p a : ℝ → ℝ) (x : ℝ) : ℝ :=
  if ell = 0 then ∫ z, a (x + z) ∂μ else parisiIntegralSecondNumerator μ ell f p a x / parisiIntegralPartition μ ell f x -
    ell * (parisiIntegralNumerator μ ell f p x / parisiIntegralPartition μ ell f x) ^ 2

lemma parisiIntegral_mean_derivatives (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f p a : ℝ → ℝ) (x₀ : ℝ)
    (hf : ∀ y, HasDerivAt f (p y) y) (hp : ∀ y, HasDerivAt p (a y) y) (hac : Continuous a)
    (ha : ∀ y, 0 ≤ a y ∧ a y ≤ 1 - p y ^ 2)
    (hi : Integrable (fun z => f (x₀ + z)) μ) :
    HasDerivAt (fun x => ∫ z, f (x + z) ∂μ) (∫ z, p (x₀ + z) ∂μ) x₀ ∧
    HasDerivAt (fun x => ∫ z, p (x + z) ∂μ) (∫ z, a (x₀ + z) ∂μ) x₀ := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun y => (hf y).continuousAt
  have hpc : Continuous p := continuous_iff_continuousAt.mpr fun y => (hp y).continuousAt
  obtain ⟨hpb, hab⟩ := parisi_profile_bounds p a ha
  have hm (g : ℝ → ℝ) (hgc : Continuous g) (x : ℝ) :
      AEStronglyMeasurable (fun z => g (x + z)) μ := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  have hpint : Integrable (fun z => p (x₀ + z)) μ :=
    (integrable_const (1 : ℝ)).mono' (hm p hpc x₀)
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hpb (x₀ + z))
  have hd (g q : ℝ → ℝ) (hg : ∀ y, HasDerivAt g (q y) y) (z x : ℝ) :
      HasDerivAt (fun y => g (y + z)) (q (x + z)) x := by
    simpa only [Function.comp_def, id_eq, mul_one] using (hg (x + z)).comp x ((hasDerivAt_id x).add_const z)
  obtain ⟨_, hfirst⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun x z => f (x + z)) (F' := fun x z => p (x + z)) (bound := fun _ => (1 : ℝ))
    (Metric.ball_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall (hm f hfc)) hi (hm p hpc x₀)
    (Eventually.of_forall fun z x _ => by simpa only [Real.norm_eq_abs] using hpb (x + z))
    (integrable_const 1) (Eventually.of_forall fun z x _ => hd f p hf z x)
  obtain ⟨_, hsecond⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun x z => p (x + z)) (F' := fun x z => a (x + z)) (bound := fun _ => (1 : ℝ))
    (Metric.ball_mem_nhds x₀ (by norm_num : (0 : ℝ) < 1))
    (Eventually.of_forall (hm p hpc)) hpint (hm a hac x₀)
    (Eventually.of_forall fun z x _ => by simpa only [Real.norm_eq_abs] using hab (x + z))
    (integrable_const 1) (Eventually.of_forall fun z x _ => hd p a hp z x)
  exact ⟨hfirst, hsecond⟩

theorem parisiGaussianStep_derivatives (center : ℝ) (variance : ℝ≥0)
    (ell : ℝ) (f p a : ℝ → ℝ) (x : ℝ)
    (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (hf : ∀ y, HasDerivAt f (p y) y)
    (hp : ∀ y, HasDerivAt p (a y) y) (hac : Continuous a)
    (ha : ∀ y, 0 ≤ a y ∧ a y ≤ 1 - p y ^ 2) :
    HasDerivAt (parisiIntegralStep (ProbabilityTheory.gaussianReal center variance) ell f)
      (parisiIntegralSlope (ProbabilityTheory.gaussianReal center variance) ell f p x) x ∧
    HasDerivAt (parisiIntegralSlope (ProbabilityTheory.gaussianReal center variance) ell f p)
      (parisiIntegralCurvature (ProbabilityTheory.gaussianReal center variance) ell f p a x) x := by
  let μ := ProbabilityTheory.gaussianReal center variance
  by_cases hzero : ell = 0
  · have hh := parisiIntegral_mean_derivatives μ f p a x hf hp hac ha
      (parisiGaussian_profile_integrable center variance f p a x hf ha)
    have hG : parisiIntegralStep μ ell f = fun y => ∫ z, f (y + z) ∂μ := by
      funext y
      simp only [parisiIntegralStep, hzero, ite_true]
    have hS : parisiIntegralSlope μ ell f p = fun y => ∫ z, p (y + z) ∂μ := by
      funext y
      simp only [parisiIntegralSlope, hzero, ite_true]
    change HasDerivAt (parisiIntegralStep μ ell f) (parisiIntegralSlope μ ell f p x) x ∧
      HasDerivAt (parisiIntegralSlope μ ell f p) (parisiIntegralCurvature μ ell f p a x) x
    rw [hG, hS]
    simpa only [parisiIntegralCurvature, hzero, ite_true] using hh
  · have hi := parisiGaussian_exp_integrable center variance ell f p a x hell hell1 hf ha
    obtain ⟨hZ, hA⟩ := parisiIntegral_partition_derivatives μ ell f p a x hell hell1 hf hp hac ha hi
    have hzne : parisiIntegralPartition μ ell f x ≠ 0 := (integral_exp_pos hi).ne'
    have hG : parisiIntegralStep μ ell f = fun y => Real.log (parisiIntegralPartition μ ell f y) / ell := by
      funext y
      simp only [parisiIntegralStep, hzero, ite_false]
    have hS : parisiIntegralSlope μ ell f p = fun y =>
        parisiIntegralNumerator μ ell f p y / parisiIntegralPartition μ ell f y := by
      funext y
      simp only [parisiIntegralSlope, hzero, ite_false]
    change HasDerivAt (parisiIntegralStep μ ell f) (parisiIntegralSlope μ ell f p x) x ∧
      HasDerivAt (parisiIntegralSlope μ ell f p) (parisiIntegralCurvature μ ell f p a x) x
    rw [hG, hS]
    simp only [parisiIntegralCurvature, hzero, ite_false]
    constructor
    · convert (hZ.log hzne).div_const ell using 1
      field_simp [hzero, hzne]
    · convert hA.div hZ hzne using 1
      field_simp [hzne]

theorem parisiGaussianStep_second_derivative_bound (center : ℝ) (variance : ℝ≥0)
    (ell : ℝ) (f p a : ℝ → ℝ)
    (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (hf : ∀ y, HasDerivAt f (p y) y)
    (hp : ∀ y, HasDerivAt p (a y) y) (hac : Continuous a)
    (ha : ∀ y, 0 ≤ a y ∧ a y ≤ 1 - p y ^ 2) :
    let T := parisiIntegralStep (ProbabilityTheory.gaussianReal center variance) ell f
    ∀ x, DifferentiableAt ℝ T x ∧ DifferentiableAt ℝ (deriv T) x ∧
      0 ≤ deriv (deriv T) x ∧ deriv (deriv T) x ≤ 1 - (deriv T x) ^ 2 := by
  let μ := ProbabilityTheory.gaussianReal center variance
  have hfirst : deriv (parisiIntegralStep μ ell f) = parisiIntegralSlope μ ell f p := by
    funext y
    exact (parisiGaussianStep_derivatives center variance ell f p a y hell hell1 hf hp hac ha).1.deriv
  have hpc : Continuous p := continuous_iff_continuousAt.mpr fun y => (hp y).continuousAt
  dsimp only
  intro x
  obtain ⟨hd, hdd⟩ := parisiGaussianStep_derivatives center variance ell f p a x hell hell1 hf hp hac ha
  have hcurv : 0 ≤ parisiIntegralCurvature μ ell f p a x ∧
      parisiIntegralCurvature μ ell f p a x ≤ 1 - parisiIntegralSlope μ ell f p x ^ 2 := by
    by_cases hzero : ell = 0
    · have hh := parisi_integral_curvature_le μ (fun _ => 1) (fun z => p (x + z))
        (fun z => a (x + z)) 0 (integrable_const 1) (fun _ => by norm_num) (by simp)
        (hpc.comp (continuous_const.add continuous_id)) (hac.comp (continuous_const.add continuous_id))
        (by norm_num) (by norm_num) (fun z => ha (x + z))
      simpa only [parisiIntegralCurvature, parisiIntegralSlope, hzero, ite_true, one_mul, zero_mul, add_zero] using hh
    · have hh := parisiIntegral_curvature_bound μ ell f p a x hell hell1 hpc hac ha
        (parisiGaussian_exp_integrable center variance ell f p a x hell hell1 hf ha)
      simpa only [parisiIntegralCurvature, parisiIntegralSlope, hzero, ite_false] using hh
  refine ⟨hd.differentiableAt, ?_, ?_, ?_⟩
  · rw [hfirst]
    exact hdd.differentiableAt
  · rw [hfirst, hdd.deriv]
    exact hcurv.1
  · rw [hfirst, hdd.deriv]
    exact hcurv.2

end SKConstants

#print axioms SKConstants.parisiIntegral_partition_derivatives
#print axioms SKConstants.parisiIntegral_curvature_bound
#print axioms SKConstants.parisiGaussian_exp_integrable
#print axioms SKConstants.parisiGaussian_profile_integrable
#print axioms SKConstants.parisiGaussianStep_second_derivative_bound
