module

public import SKConstants.GaussianMaximum
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Distributions.Gaussian.Fernique

public section
open MeasureTheory ProbabilityTheory Filter WithLp
open scoped Topology BigOperators NNReal
noncomputable section
namespace SKConstants

lemma integrable_gaussian_density_iff (f : ℝ → ℝ) :
    Integrable f (gaussianReal 0 1) ↔
      Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [gaussianReal_of_var_ne_zero _ (by norm_num)]
  simpa only [toReal_gaussianPDF, smul_eq_mul] using
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ (fun x => gaussianPDF_lt_top (μ := 0) (v := 1) (x := x))) (g := f)

lemma hasDerivAt_standardGaussianDensity (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    (1 / Real.sqrt (2 * Real.pi))
  convert h using 1
  · ext y
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, one_div, Pi.neg_apply, Pi.pow_apply, id_eq]
  · simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, one_div, Pi.neg_apply, Pi.pow_apply, id_eq]
    norm_num
    ring

lemma gaussianReal_stein_of_bounded (f f' : ℝ → ℝ)
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : Measurable f) (hf' : Measurable f')
    (C D : ℝ) (hC : ∀ x, |f x| ≤ C) (hD : ∀ x, |f' x| ≤ D) :
    (∫ x, x * f x ∂gaussianReal 0 1) = ∫ x, f' x ∂gaussianReal 0 1 := by
  have hfi : Integrable f (gaussianReal 0 1) :=
    (integrable_const C).mono' hf.aestronglyMeasurable (ae_of_all _ hC)
  have hf'i : Integrable f' (gaussianReal 0 1) :=
    (integrable_const D).mono' hf'.aestronglyMeasurable (ae_of_all _ hD)
  have hxi : Integrable (fun x : ℝ => x * f x) (gaussianReal 0 1) := by
    apply (IsGaussian.integrable_fun_id.abs.const_mul C).mono'
      ((measurable_id.mul hf).aestronglyMeasurable)
    filter_upwards with x
    simpa only [Real.norm_eq_abs, Pi.mul_apply, id_eq, abs_mul, mul_comm C] using mul_le_mul_of_nonneg_left (hC x) (abs_nonneg x)
  have hφf := (integrable_gaussian_density_iff f).mp hfi
  have hφf' := (integrable_gaussian_density_iff f').mp hf'i
  have hφxf := (integrable_gaussian_density_iff (fun x => x * f x)).mp hxi
  have hleft : Integrable (fun x => f x * (-x * gaussianPDFReal 0 1 x)) := by
    convert hφxf.neg using 1
    ext x
    simp only [Pi.neg_apply]
    ring
  have hright : Integrable (fun x => f' x * gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using hφf'
  have hprod : Integrable (fun x => f x * gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using hφf
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (u' := f') (v := gaussianPDFReal 0 1)
    (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => hderiv x) (fun x _ => hasDerivAt_standardGaussianDensity x)
    hleft hright hprod
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  have heq : (fun x => f x * (-x * gaussianPDFReal 0 1 x)) =
      -(fun x => gaussianPDFReal 0 1 x * (x * f x)) := by ext x; simp; ring
  rw [heq] at hibp
  change (∫ x, -(gaussianPDFReal 0 1 x * (x * f x))) = _ at hibp
  rw [integral_neg] at hibp
  simpa only [mul_comm, neg_inj] using hibp
end SKConstants
namespace SKConstants
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
@[expose] def gaussianCoordinateSplit (i : ι) :
    (ι → ℝ) ≃ᵐ ℝ × ({j : ι // j ≠ i} → ℝ) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (fun j => j = i)).trans
    ((MeasurableEquiv.piUnique (fun _ : {j : ι // j = i} => ℝ)).prodCongr
      (MeasurableEquiv.refl _))
omit [Fintype ι] in
lemma gaussianCoordinateSplit_apply (i : ι) (z : ι → ℝ) :
    gaussianCoordinateSplit i z = (z i, fun j : {j : ι // j ≠ i} => z j) := by rfl
omit [Fintype ι] in
lemma gaussianCoordinateSplit_symm (i : ι) (t : ℝ) (z : {j : ι // j ≠ i} → ℝ) (j : ι) :
    (gaussianCoordinateSplit i).symm (t,z) j = if h : j = i then t else z ⟨j,h⟩ := by
  rfl
lemma gaussianCoordinateSplit_preserving (i : ι) :
    MeasurePreserving (gaussianCoordinateSplit i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1))
      ((gaussianReal 0 1).prod (Measure.pi (fun _ : {j : ι // j ≠ i} => gaussianReal 0 1))) := by
  let : Fintype {j : ι // j = i} := Subtype.fintype _
  exact ((measurePreserving_piUnique (fun _ : {j : ι // j = i} => gaussianReal 0 1)).prod
    (MeasurePreserving.id _)).comp
    (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => gaussianReal 0 1) (fun j => j = i))
end SKConstants
namespace SKConstants
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] in
lemma gaussianCoordinateSplit_update (i : ι) (t : ℝ) (w : {j : ι // j ≠ i} → ℝ) :
    (gaussianCoordinateSplit i).symm (t,w) =
      Function.update ((gaussianCoordinateSplit i).symm (0,w)) i t := by
  ext j
  by_cases h : j = i
  · subst j; simp [gaussianCoordinateSplit_symm]
  · simp [gaussianCoordinateSplit_symm, h]

lemma gaussianPi_coordinate_stein (i : ι) (f d : (ι → ℝ) → ℝ)
    (hf : Measurable f) (hd : Measurable d)
    (hderiv : ∀ z t, HasDerivAt (fun t => f (Function.update z i t))
      (d (Function.update z i t)) t)
    (C D : ℝ) (hC : ∀ z, |f z| ≤ C) (hD : ∀ z, |d z| ≤ D) :
    (∫ z, z i * f z ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      ∫ z, d z ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  let μ := Measure.pi (fun _ : ι => gaussianReal 0 1)
  let ν := Measure.pi (fun _ : {j : ι // j ≠ i} => gaussianReal 0 1)
  let e := gaussianCoordinateSplit i
  have he := (gaussianCoordinateSplit_preserving i).symm
  have hcoord : HasLaw (fun z : ι → ℝ => z i) (gaussianReal 0 1) μ := by
    refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
    simpa [μ] using Measure.pi_map_eval (fun _ : ι => gaussianReal 0 1) i
  have hxi : Integrable (fun z => z i * f z) μ := by
    apply ((hcoord.integrable_fun_comp IsGaussian.integrable_fun_id).abs.const_mul C).mono'
      ((measurable_pi_apply i).mul hf).aestronglyMeasurable
    filter_upwards with z
    simpa only [Real.norm_eq_abs, Pi.mul_apply, abs_mul, mul_comm C] using
      mul_le_mul_of_nonneg_left (hC z) (abs_nonneg (z i))
  have hdi : Integrable d μ := (integrable_const D).mono' hd.aestronglyMeasurable (ae_of_all _ hD)
  rw [← he.integral_comp' (fun z => z i * f z), ← he.integral_comp' d]
  have hxi' : Integrable (fun p => e.symm p i * f (e.symm p)) ((gaussianReal 0 1).prod ν) := by
    simpa [e, ν, Function.comp_def] using he.integrable_comp_of_integrable hxi
  have hdi' : Integrable (fun p => d (e.symm p)) ((gaussianReal 0 1).prod ν) := by
    simpa [e, ν, Function.comp_def] using he.integrable_comp_of_integrable hdi
  change (∫ p, e.symm p i * f (e.symm p) ∂(gaussianReal 0 1).prod ν) = ∫ p, d (e.symm p) ∂(gaussianReal 0 1).prod ν
  rw [integral_prod_symm _ hxi', integral_prod_symm _ hdi']
  apply integral_congr_ae
  filter_upwards with w
  have hdw : ∀ t, HasDerivAt (fun t => f (e.symm (t,w))) (d (e.symm (t,w))) t := by
    intro t
    have heq : (fun t => f (e.symm (t,w))) =
        (fun t => f (Function.update (e.symm (0,w)) i t)) := by
      funext t
      congr 1
      exact gaussianCoordinateSplit_update i t w
    rw [heq, show d (e.symm (t,w)) = d (Function.update (e.symm (0,w)) i t) from
      congrArg d (gaussianCoordinateSplit_update i t w)]
    exact hderiv (e.symm (0,w)) t
  have hfw : Measurable (fun t => f (e.symm (t,w))) := hf.comp (e.symm.measurable.comp (by fun_prop))
  have hdw' : Measurable (fun t => d (e.symm (t,w))) := hd.comp (e.symm.measurable.comp (by fun_prop))
  have h := gaussianReal_stein_of_bounded _ _ hdw hfw hdw' C D
    (fun t => hC (e.symm (t,w))) (fun t => hD (e.symm (t,w)))
  simpa only [e, gaussianCoordinateSplit_symm, dite_true] using h
end SKConstants
namespace SKConstants
open scoped Classical
@[expose] def spinGaussianCoefficient {n : ℕ} (sigma : ℝ) (x : Spin n)
    (p : Fin n × Fin n) : ℝ := sigma * signedSpin x p.1 * signedSpin x p.2
lemma goeSpinHamiltonian_eq_linear {n : ℕ} (sigma : ℝ) (x : Spin n)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) :
    goeSpinHamiltonian sigma x z = ∑ p, spinGaussianCoefficient sigma x p * z p := by
  rw [goeSpinHamiltonian_eq_half_bilinear]
  unfold GaussianProposal.goeBilinear GaussianProposal.linearForm
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  unfold spinGaussianCoefficient
  ring
lemma abs_spinGaussianCoefficient {n : ℕ} (sigma : ℝ) (x : Spin n) (p : Fin n × Fin n) :
    |spinGaussianCoefficient sigma x p| = |sigma| := by
  have h (i : Fin n) : |signedSpin x i| = 1 := by
    cases hx : x i <;> simp [signedSpin, hx]
  simp [spinGaussianCoefficient, abs_mul, h]

@[expose] def coordinateGibbsProbability {n : ℕ} (beta sigma : ℝ)
    (z : (Fin n × Fin n) → ℝ) (x : Spin n) : ℝ :=
  gibbsProbability beta (GaussianProposal.goeMatrix sigma (toLp 2 z)) x
@[expose] def coordinateGibbsMeanCoefficient {n : ℕ} (beta sigma : ℝ)
    (z : (Fin n × Fin n) → ℝ) (i : Fin n × Fin n) : ℝ :=
  ∑ x, coordinateGibbsProbability beta sigma z x * spinGaussianCoefficient sigma x i
@[expose] def coordinateGibbsDerivative {n : ℕ} (beta sigma : ℝ)
    (z : (Fin n × Fin n) → ℝ) (x : Spin n) (i : Fin n × Fin n) : ℝ :=
  beta * coordinateGibbsProbability beta sigma z x *
    (spinGaussianCoefficient sigma x i - coordinateGibbsMeanCoefficient beta sigma z i)

lemma hasDerivAt_coordinate_hamiltonian {n : ℕ} (sigma : ℝ) (x : Spin n)
    (z : (Fin n × Fin n) → ℝ) (i : Fin n × Fin n) (t : ℝ) :
    HasDerivAt (fun t => quadraticHamiltonian
      (GaussianProposal.goeMatrix sigma (toLp 2 (Function.update z i t))) x)
      (spinGaussianCoefficient sigma x i) t := by
  have heq : (fun t => quadraticHamiltonian
      (GaussianProposal.goeMatrix sigma (toLp 2 (Function.update z i t))) x) =
      (fun t => ∑ j, spinGaussianCoefficient sigma x j * (Function.update z i t) j) := by
    funext t
    exact goeSpinHamiltonian_eq_linear sigma x _
  rw [heq]
  have ht : ∀ j ∈ (Finset.univ : Finset (Fin n × Fin n)),
      HasDerivAt (fun t => spinGaussianCoefficient sigma x j * (Function.update z i t) j)
        (if j = i then spinGaussianCoefficient sigma x j else 0) t := by
    intro j _
    by_cases h : j = i
    · subst j
      simpa using (hasDerivAt_id t).const_mul (spinGaussianCoefficient sigma x i)
    · simpa [Function.update_of_ne h, h] using
        hasDerivAt_const t (spinGaussianCoefficient sigma x j * z j)
  simpa only [Finset.sum_fn, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using HasDerivAt.sum ht

lemma hasDerivAt_coordinateGibbsProbability {n : ℕ} (beta sigma : ℝ)
    (z : (Fin n × Fin n) → ℝ) (x : Spin n) (i : Fin n × Fin n) (t : ℝ) :
    HasDerivAt (fun t => coordinateGibbsProbability beta sigma (Function.update z i t) x)
      (coordinateGibbsDerivative beta sigma (Function.update z i t) x i) t := by
  have hn := ((hasDerivAt_coordinate_hamiltonian sigma x z i t).const_mul beta).exp
  have hZ : HasDerivAt
      (fun t => gibbsPartition beta (GaussianProposal.goeMatrix sigma (toLp 2 (Function.update z i t))))
      (∑ y : Spin n, Real.exp (beta * quadraticHamiltonian
        (GaussianProposal.goeMatrix sigma (toLp 2 (Function.update z i t))) y) *
        (beta * spinGaussianCoefficient sigma y i)) t := by
    simpa only [gibbsPartition, Finset.sum_fn] using HasDerivAt.sum (u := Finset.univ) (fun y _ =>
      ((hasDerivAt_coordinate_hamiltonian sigma y z i t).const_mul beta).exp)
  have hp := gibbsPartition_pos beta (GaussianProposal.goeMatrix sigma (toLp 2 (Function.update z i t)))
  convert hn.div hZ hp.ne' using 1
  · rfl
  · unfold coordinateGibbsDerivative coordinateGibbsMeanCoefficient coordinateGibbsProbability gibbsProbability
    simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
    have hs : (∑ y : Spin n, Real.exp (beta * quadraticHamiltonian
        (GaussianProposal.goeMatrix sigma (toLp 2 (Function.update z i t))) y) *
        (beta * spinGaussianCoefficient sigma y i)) =
        beta * ∑ y : Spin n, Real.exp (beta * quadraticHamiltonian
        (GaussianProposal.goeMatrix sigma (toLp 2 (Function.update z i t))) y) *
        spinGaussianCoefficient sigma y i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    rw [hs]
    field_simp

lemma measurable_coordinateGibbsProbability {n : ℕ} (beta sigma : ℝ) (x : Spin n) :
    Measurable (fun z => coordinateGibbsProbability beta sigma z x) := by
  exact (continuous_gibbsProbability beta x).measurable.comp
    ((continuous_goeMatrix sigma).measurable.comp (by fun_prop))
lemma measurable_coordinateGibbsMeanCoefficient {n : ℕ} (beta sigma : ℝ) (i : Fin n × Fin n) :
    Measurable (fun z => coordinateGibbsMeanCoefficient beta sigma z i) := by
  exact Finset.measurable_sum _ (fun x _ =>
    (measurable_coordinateGibbsProbability beta sigma x).mul_const _)
lemma measurable_coordinateGibbsDerivative {n : ℕ} (beta sigma : ℝ) (x : Spin n) (i : Fin n × Fin n) :
    Measurable (fun z => coordinateGibbsDerivative beta sigma z x i) := by
  exact ((measurable_coordinateGibbsProbability beta sigma x).const_mul beta).mul
    (measurable_const.sub (measurable_coordinateGibbsMeanCoefficient beta sigma i))
lemma coordinateGibbsProbability_le_one {n : ℕ} (beta sigma : ℝ) (z) (x : Spin n) :
    coordinateGibbsProbability beta sigma z x ≤ 1 := by
  have h := Finset.single_le_sum (f := fun y => coordinateGibbsProbability beta sigma z y)
    (fun y _ => (gibbsProbability_pos beta _ y).le) (Finset.mem_univ x)
  simpa [coordinateGibbsProbability, gibbsProbability_sum] using h
lemma abs_coordinateGibbsMeanCoefficient_le {n : ℕ} (beta sigma : ℝ) (z) (i : Fin n × Fin n) :
    |coordinateGibbsMeanCoefficient beta sigma z i| ≤ |sigma| := by
  calc
    _ ≤ ∑ x, |coordinateGibbsProbability beta sigma z x * spinGaussianCoefficient sigma x i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = |sigma| := by
      have hp (x : Spin n) : 0 < coordinateGibbsProbability beta sigma z x := gibbsProbability_pos beta _ x
      simp_rw [abs_mul, abs_of_pos (hp _), abs_spinGaussianCoefficient]
      rw [← Finset.sum_mul]
      simp [coordinateGibbsProbability, gibbsProbability_sum]
lemma abs_coordinateGibbsDerivative_le {n : ℕ} (beta sigma : ℝ) (z) (x : Spin n) (i : Fin n × Fin n) :
    |coordinateGibbsDerivative beta sigma z x i| ≤ 2 * |beta| * |sigma| := by
  have hdiff : |spinGaussianCoefficient sigma x i - coordinateGibbsMeanCoefficient beta sigma z i| ≤
      2 * |sigma| := by
    calc
      _ ≤ |spinGaussianCoefficient sigma x i| + |coordinateGibbsMeanCoefficient beta sigma z i| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (spinGaussianCoefficient sigma x i) 0 (coordinateGibbsMeanCoefficient beta sigma z i)
      _ ≤ 2 * |sigma| := by rw [abs_spinGaussianCoefficient]; linarith [abs_coordinateGibbsMeanCoefficient_le beta sigma z i]
  unfold coordinateGibbsDerivative
  have hp : 0 < coordinateGibbsProbability beta sigma z x := gibbsProbability_pos beta _ x
  rw [abs_mul, abs_mul, abs_of_pos hp]
  calc
    _ ≤ |beta| * 1 * (2 * |sigma|) := mul_le_mul
      (mul_le_mul_of_nonneg_left (coordinateGibbsProbability_le_one beta sigma z x) (abs_nonneg beta))
      hdiff (abs_nonneg _) (by positivity)
    _ = _ := by ring
end SKConstants
namespace SKConstants
open scoped Classical
@[expose] def coordinateGibbsEnergy {n : ℕ} (beta sigma : ℝ)
    (z : (Fin n × Fin n) → ℝ) : ℝ :=
  ∑ x : Spin n, coordinateGibbsProbability beta sigma z x *
    goeSpinHamiltonian sigma x (toLp 2 z)
lemma spinGaussianCoefficient_sq {n : ℕ} (sigma : ℝ) (x : Spin n) (i : Fin n × Fin n) :
    spinGaussianCoefficient sigma x i ^ 2 = sigma ^ 2 := by
  simp [spinGaussianCoefficient, mul_pow, signedSpin_sq]
lemma coordinateGibbsDerivative_sum {n : ℕ} (beta sigma : ℝ) (z) (i : Fin n × Fin n) :
    (∑ x : Spin n, spinGaussianCoefficient sigma x i * coordinateGibbsDerivative beta sigma z x i) =
      beta * (sigma ^ 2 - coordinateGibbsMeanCoefficient beta sigma z i ^ 2) := by
  have hp : (∑ x : Spin n, coordinateGibbsProbability beta sigma z x) = 1 :=
    gibbsProbability_sum beta _
  calc
    _ = beta * ((∑ x : Spin n, coordinateGibbsProbability beta sigma z x *
          spinGaussianCoefficient sigma x i ^ 2) -
          (∑ x : Spin n, coordinateGibbsProbability beta sigma z x *
          spinGaussianCoefficient sigma x i) * coordinateGibbsMeanCoefficient beta sigma z i) := by
      rw [mul_sub, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      unfold coordinateGibbsDerivative
      ring
    _ = _ := by
      simp_rw [spinGaussianCoefficient_sq]
      rw [← Finset.sum_mul, hp]
      unfold coordinateGibbsMeanCoefficient
      ring
lemma coordinateGibbsDerivative_total_sum {n : ℕ} (beta sigma : ℝ) (z) :
    (∑ i : Fin n × Fin n, ∑ x : Spin n,
      spinGaussianCoefficient sigma x i * coordinateGibbsDerivative beta sigma z x i) =
      beta * (sigma ^ 2 * (n : ℝ) ^ 2 - ∑ i : Fin n × Fin n,
        coordinateGibbsMeanCoefficient beta sigma z i ^ 2) := by
  simp_rw [coordinateGibbsDerivative_sum]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp [Fintype.card_prod, Nat.cast_mul, pow_two, mul_comm]
lemma coordinateGibbsEnergy_eq_sum {n : ℕ} (beta sigma : ℝ) (z) :
    coordinateGibbsEnergy beta sigma z = ∑ i : Fin n × Fin n, ∑ x : Spin n,
      spinGaussianCoefficient sigma x i * (z i * coordinateGibbsProbability beta sigma z x) := by
  unfold coordinateGibbsEnergy
  simp_rw [goeSpinHamiltonian_eq_linear, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma coordinateGibbsProbability_coordinate_integrable {n : ℕ} (beta sigma : ℝ)
    (x : Spin n) (i : Fin n × Fin n) :
    Integrable (fun z => z i * coordinateGibbsProbability beta sigma z x)
      (Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1)) := by
  have hlaw : HasLaw (fun z : (Fin n × Fin n) → ℝ => z i) (gaussianReal 0 1)
      (Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1)) := by
    refine ⟨(measurable_pi_apply i).aemeasurable, ?_⟩
    simpa using Measure.pi_map_eval (fun _ : Fin n × Fin n => gaussianReal 0 1) i
  apply (hlaw.integrable_fun_comp IsGaussian.integrable_fun_id).abs.mono'
    ((measurable_pi_apply i).mul (measurable_coordinateGibbsProbability beta sigma x)).aestronglyMeasurable
  filter_upwards with z
  have hp : 0 < coordinateGibbsProbability beta sigma z x := gibbsProbability_pos beta _ x
  simpa only [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_pos hp, mul_one] using
    mul_le_mul_of_nonneg_left (coordinateGibbsProbability_le_one beta sigma z x) (abs_nonneg (z i))
lemma coordinateGibbsDerivative_integrable {n : ℕ} (beta sigma : ℝ)
    (x : Spin n) (i : Fin n × Fin n) :
    Integrable (fun z => coordinateGibbsDerivative beta sigma z x i)
      (Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1)) :=
  (integrable_const (2 * |beta| * |sigma|)).mono'
    (measurable_coordinateGibbsDerivative beta sigma x i).aestronglyMeasurable
    (ae_of_all _ (fun z => abs_coordinateGibbsDerivative_le beta sigma z x i))
lemma coordinateGibbsEnergy_integrable {n : ℕ} (beta sigma : ℝ) :
    Integrable (coordinateGibbsEnergy (n := n) beta sigma)
      (Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1)) := by
  have h := integrable_finsetSum Finset.univ (fun (i : Fin n × Fin n) _ =>
    integrable_finsetSum Finset.univ (fun (x : Spin n) _ =>
      (coordinateGibbsProbability_coordinate_integrable beta sigma x i).const_mul
        (spinGaussianCoefficient sigma x i)))
  simpa only [← coordinateGibbsEnergy_eq_sum] using h

lemma coordinateGibbsEnergy_stein {n : ℕ} (beta sigma : ℝ) :
    (∫ z, coordinateGibbsEnergy (n := n) beta sigma z
      ∂Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1)) =
    ∫ z, beta * (sigma ^ 2 * (n : ℝ) ^ 2 - ∑ i : Fin n × Fin n,
      coordinateGibbsMeanCoefficient beta sigma z i ^ 2)
      ∂Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1) := by
  have hstein (x : Spin n) (i : Fin n × Fin n) := gaussianPi_coordinate_stein i
    (fun z => coordinateGibbsProbability beta sigma z x)
    (fun z => coordinateGibbsDerivative beta sigma z x i)
    (measurable_coordinateGibbsProbability beta sigma x)
    (measurable_coordinateGibbsDerivative beta sigma x i)
    (fun z t => hasDerivAt_coordinateGibbsProbability beta sigma z x i t)
    1 (2 * |beta| * |sigma|)
    (fun z => by rw [abs_of_pos (show 0 < coordinateGibbsProbability beta sigma z x from gibbsProbability_pos beta _ x)]; exact coordinateGibbsProbability_le_one beta sigma z x)
    (fun z => abs_coordinateGibbsDerivative_le beta sigma z x i)
  simp_rw [coordinateGibbsEnergy_eq_sum]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun x _ =>
    (coordinateGibbsProbability_coordinate_integrable beta sigma x i).const_mul _))]
  simp_rw [integral_finsetSum _ (fun x _ =>
    (coordinateGibbsProbability_coordinate_integrable beta sigma x _).const_mul _), integral_const_mul]
  simp_rw [hstein]
  have hd (i : Fin n × Fin n) (x : Spin n) :=
    (coordinateGibbsDerivative_integrable beta sigma x i).const_mul (spinGaussianCoefficient sigma x i)
  simp_rw [← integral_const_mul]
  have hinner (i : Fin n × Fin n) :
      (∑ x : Spin n, ∫ z, spinGaussianCoefficient sigma x i * coordinateGibbsDerivative beta sigma z x i
        ∂Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1)) =
      ∫ z, ∑ x : Spin n, spinGaussianCoefficient sigma x i * coordinateGibbsDerivative beta sigma z x i
        ∂Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1) :=
    (integral_finsetSum _ (fun x _ => hd i x)).symm
  simp_rw [hinner]
  rw [← integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun x _ => hd i x))]
  apply integral_congr_ae
  filter_upwards with z
  exact coordinateGibbsDerivative_total_sum beta sigma z
end SKConstants
namespace SKConstants
open scoped Classical
lemma coordinateGibbsEnergy_expected_bound {n : ℕ} (beta sigma : ℝ) :
    beta * (∫ z, coordinateGibbsEnergy (n := n) beta sigma z
      ∂Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1)) ≤
      beta ^ 2 * sigma ^ 2 * (n : ℝ) ^ 2 := by
  let μ := Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1)
  have hi : Integrable (fun z => beta * (sigma ^ 2 * (n : ℝ) ^ 2 -
      ∑ i : Fin n × Fin n, coordinateGibbsMeanCoefficient beta sigma z i ^ 2)) μ := by
    have h := integrable_finsetSum Finset.univ (fun (i : Fin n × Fin n) _ =>
      integrable_finsetSum Finset.univ (fun (x : Spin n) _ =>
        (coordinateGibbsDerivative_integrable beta sigma x i).const_mul
          (spinGaussianCoefficient sigma x i)))
    convert h using 1
    funext z
    exact (coordinateGibbsDerivative_total_sum beta sigma z).symm
  rw [coordinateGibbsEnergy_stein, ← integral_const_mul]
  calc
    _ ≤ ∫ _, beta ^ 2 * sigma ^ 2 * (n : ℝ) ^ 2 ∂μ :=
      integral_mono (hi.const_mul beta) (integrable_const _) (fun z => by
        have hs : 0 ≤ ∑ i : Fin n × Fin n, coordinateGibbsMeanCoefficient beta sigma z i ^ 2 :=
          Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        nlinarith [mul_nonneg (sq_nonneg beta) hs])
    _ = _ := by simp [μ]

@[expose] def goeGibbsEnergy {n : ℕ} (beta sigma : ℝ)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) : ℝ :=
  ∑ x : Spin n, gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x *
    quadraticHamiltonian (GaussianProposal.goeMatrix sigma z) x
lemma measurable_goeGibbsEnergy {n : ℕ} (beta sigma : ℝ) :
    Measurable (goeGibbsEnergy (n := n) beta sigma) := by
  apply Finset.measurable_sum
  intro x _
  exact ((continuous_gibbsProbability beta x).measurable.comp (continuous_goeMatrix sigma).measurable).mul
    ((continuous_quadraticHamiltonian x).measurable.comp (continuous_goeMatrix sigma).measurable)
lemma goeGibbsEnergy_integrable {n : ℕ} (beta sigma : ℝ) :
    Integrable (goeGibbsEnergy (n := n) beta sigma)
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  change Integrable _ (stdGaussian (EuclideanSpace ℝ (Fin n × Fin n)))
  rw [← map_pi_eq_stdGaussian]
  apply (integrable_map_measure
    (measurable_goeGibbsEnergy beta sigma).aestronglyMeasurable (by fun_prop)).mpr
  exact coordinateGibbsEnergy_integrable beta sigma

lemma goe_gibbs_expected_energy_bound {n : ℕ} (beta sigma : ℝ) :
    beta * (∫ z, goeGibbsEnergy (n := n) beta sigma z
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) ≤
      beta ^ 2 * sigma ^ 2 * (n : ℝ) ^ 2 := by
  change beta * (∫ z, goeGibbsEnergy beta sigma z
    ∂stdGaussian (EuclideanSpace ℝ (Fin n × Fin n))) ≤ _
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop)
    (measurable_goeGibbsEnergy beta sigma).aestronglyMeasurable]
  exact coordinateGibbsEnergy_expected_bound beta sigma

lemma sk_gibbs_expected_energy_bound {n : ℕ} (hn : 0 < n) (beta : ℝ) :
    beta * (∫ z, goeGibbsEnergy (n := n) beta (1 / Real.sqrt (2 * (n : ℝ))) z
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) ≤ beta ^ 2 * (n : ℝ) / 2 := by
  have h := goe_gibbs_expected_energy_bound (n := n) beta (1 / Real.sqrt (2 * (n : ℝ)))
  have heq : beta ^ 2 * (1 / Real.sqrt (2 * (n : ℝ))) ^ 2 * (n : ℝ) ^ 2 = beta ^ 2 * (n : ℝ) / 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
    have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
    field_simp
  rwa [heq] at h
end SKConstants

namespace SKConstants
lemma goeGibbsProbability_integrable {n : ℕ} (beta sigma : ℝ) (x : Spin n) :
    Integrable (fun z => gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x)
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  apply (integrable_const (1 : ℝ)).mono'
    (((continuous_gibbsProbability beta x).measurable.comp (continuous_goeMatrix sigma).measurable).aestronglyMeasurable)
  filter_upwards with z
  change ‖gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (gibbsProbability_pos beta _ x)]
  exact coordinateGibbsProbability_le_one beta sigma z.ofLp x

@[expose] def goeCrossGibbsEnergy {n : ℕ} (beta sigma : ℝ)
    (p : EuclideanSpace ℝ (Fin n × Fin n) × EuclideanSpace ℝ (Fin n × Fin n)) : ℝ :=
  ∑ x : Spin n, gibbsProbability beta (GaussianProposal.goeMatrix sigma p.1) x *
    goeSpinHamiltonian sigma x p.2
lemma goeCrossGibbsEnergy_integrable {n : ℕ} (beta sigma : ℝ) :
    Integrable (goeCrossGibbsEnergy (n := n) beta sigma)
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n))) := by
  exact integrable_finsetSum _ (fun x _ =>
    (goeGibbsProbability_integrable beta sigma x).mul_prod
      (goeSpinHamiltonian_gaussian sigma x).integrable)
lemma goeCrossGibbsEnergy_integral {n : ℕ} (beta sigma : ℝ) :
    (∫ p, goeCrossGibbsEnergy (n := n) beta sigma p
      ∂((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n)))) = 0 := by
  unfold goeCrossGibbsEnergy
  rw [integral_finsetSum _ (fun x _ =>
    (goeGibbsProbability_integrable beta sigma x).mul_prod
      (goeSpinHamiltonian_gaussian sigma x).integrable)]
  apply Finset.sum_eq_zero
  intro x _
  rw [integral_prod_mul (fun z => gibbsProbability beta (GaussianProposal.goeMatrix sigma z) x)
    (goeSpinHamiltonian sigma x), goeSpinHamiltonian_mean, mul_zero]

lemma goeSpinHamiltonian_linear_combination {n : ℕ} (sigma a b : ℝ) (x : Spin n)
    (z w : EuclideanSpace ℝ (Fin n × Fin n)) :
    goeSpinHamiltonian sigma x (a • z + b • w) =
      a * goeSpinHamiltonian sigma x z + b * goeSpinHamiltonian sigma x w := by
  simp_rw [goeSpinHamiltonian_eq_linear]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[expose] def goeMixedGibbsEnergy {n : ℕ} (beta sigma a b : ℝ)
    (p : EuclideanSpace ℝ (Fin n × Fin n) × EuclideanSpace ℝ (Fin n × Fin n)) : ℝ :=
  ∑ x : Spin n, gibbsProbability beta (GaussianProposal.goeMatrix sigma p.1) x *
    goeSpinHamiltonian sigma x (a • p.1 + b • p.2)
lemma goeMixedGibbsEnergy_eq {n : ℕ} (beta sigma a b : ℝ)
    (p : EuclideanSpace ℝ (Fin n × Fin n) × EuclideanSpace ℝ (Fin n × Fin n)) :
    goeMixedGibbsEnergy beta sigma a b p =
      a * goeGibbsEnergy beta sigma p.1 + b * goeCrossGibbsEnergy beta sigma p := by
  unfold goeMixedGibbsEnergy goeGibbsEnergy goeCrossGibbsEnergy
  simp_rw [goeSpinHamiltonian_linear_combination]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  unfold goeSpinHamiltonian
  ring
lemma goeMixedGibbsEnergy_integrable {n : ℕ} (beta sigma a b : ℝ) :
    Integrable (goeMixedGibbsEnergy (n := n) beta sigma a b)
      ((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n))) := by
  have h := (((goeGibbsEnergy_integrable (n := n) beta sigma).comp_fst (GaussianProposal.primitiveGaussian (Fin n × Fin n))).const_mul a).add
    ((goeCrossGibbsEnergy_integrable (n := n) beta sigma).const_mul b)
  convert h using 1
  funext p
  exact goeMixedGibbsEnergy_eq beta sigma a b p

lemma goeMixedGibbsEnergy_integral {n : ℕ} (beta sigma a b : ℝ) :
    (∫ p, goeMixedGibbsEnergy (n := n) beta sigma a b p
      ∂((GaussianProposal.primitiveGaussian (Fin n × Fin n)).prod
        (GaussianProposal.primitiveGaussian (Fin n × Fin n)))) =
    a * ∫ z, goeGibbsEnergy (n := n) beta sigma z
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n) := by
  simp_rw [goeMixedGibbsEnergy_eq]
  rw [integral_add (((goeGibbsEnergy_integrable (n := n) beta sigma).comp_fst (GaussianProposal.primitiveGaussian (Fin n × Fin n))).const_mul a)
    ((goeCrossGibbsEnergy_integrable (n := n) beta sigma).const_mul b)]
  rw [integral_const_mul, integral_const_mul, integral_fun_fst, goeCrossGibbsEnergy_integral]
  simp
end SKConstants

namespace SKConstants
lemma coordinateGibbsMeanCoefficient_diagonal {n : ℕ} (beta sigma : ℝ) (z) (i : Fin n) :
    coordinateGibbsMeanCoefficient beta sigma z (i,i) = sigma := by
  have ha (x : Spin n) : spinGaussianCoefficient sigma x (i,i) = sigma := by
    unfold spinGaussianCoefficient
    rw [mul_assoc, ← pow_two, signedSpin_sq, mul_one]
  unfold coordinateGibbsMeanCoefficient
  simp_rw [ha]
  rw [← Finset.sum_mul]
  simp [coordinateGibbsProbability, gibbsProbability_sum]
lemma coordinateGibbsMeanCoefficient_square_sum_lower {n : ℕ} (beta sigma : ℝ) (z) :
    sigma ^ 2 * (n : ℝ) ≤ ∑ i : Fin n × Fin n, coordinateGibbsMeanCoefficient beta sigma z i ^ 2 := by
  calc
    _ = ∑ _ : Fin n, sigma ^ 2 := by simp [mul_comm]
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, coordinateGibbsMeanCoefficient beta sigma z (i,j) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      calc
        sigma ^ 2 = coordinateGibbsMeanCoefficient beta sigma z (i,i) ^ 2 := by
          rw [coordinateGibbsMeanCoefficient_diagonal]
        _ ≤ _ := Finset.single_le_sum (f := fun j : Fin n => coordinateGibbsMeanCoefficient beta sigma z (i,j) ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    _ = _ := by rw [Fintype.sum_prod_type]

lemma coordinateGibbsEnergy_expected_diagonal_bound {n : ℕ} (beta sigma : ℝ) :
    beta * (∫ z, coordinateGibbsEnergy (n := n) beta sigma z
      ∂Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1)) ≤
      beta ^ 2 * sigma ^ 2 * ((n : ℝ) ^ 2 - n) := by
  let μ := Measure.pi (fun _ : Fin n × Fin n => gaussianReal 0 1)
  have hi : Integrable (fun z => beta * (sigma ^ 2 * (n : ℝ) ^ 2 -
      ∑ i : Fin n × Fin n, coordinateGibbsMeanCoefficient beta sigma z i ^ 2)) μ := by
    have h := integrable_finsetSum Finset.univ (fun (i : Fin n × Fin n) _ =>
      integrable_finsetSum Finset.univ (fun (x : Spin n) _ =>
        (coordinateGibbsDerivative_integrable beta sigma x i).const_mul
          (spinGaussianCoefficient sigma x i)))
    convert h using 1
    funext z
    exact (coordinateGibbsDerivative_total_sum beta sigma z).symm
  rw [coordinateGibbsEnergy_stein, ← integral_const_mul]
  calc
    _ ≤ ∫ _, beta ^ 2 * sigma ^ 2 * ((n : ℝ) ^ 2 - n) ∂μ :=
      integral_mono (hi.const_mul beta) (integrable_const _) (fun z => by
        have hs := coordinateGibbsMeanCoefficient_square_sum_lower beta sigma z
        nlinarith [mul_nonneg (sq_nonneg beta) (sub_nonneg.mpr hs)])
    _ = _ := by simp [μ]

lemma goe_gibbs_expected_energy_diagonal_bound {n : ℕ} (beta sigma : ℝ) :
    beta * (∫ z, goeGibbsEnergy (n := n) beta sigma z
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) ≤
      beta ^ 2 * sigma ^ 2 * ((n : ℝ) ^ 2 - n) := by
  change beta * (∫ z, goeGibbsEnergy beta sigma z
    ∂stdGaussian (EuclideanSpace ℝ (Fin n × Fin n))) ≤ _
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop)
    (measurable_goeGibbsEnergy beta sigma).aestronglyMeasurable]
  exact coordinateGibbsEnergy_expected_diagonal_bound beta sigma

lemma sk_gibbs_expected_energy_diagonal_bound {n : ℕ} (hn : 0 < n) (beta : ℝ) :
    beta * (∫ z, goeGibbsEnergy (n := n) beta (1 / Real.sqrt (2 * (n : ℝ))) z
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n)) ≤ beta ^ 2 * ((n : ℝ) - 1) / 2 := by
  have h := goe_gibbs_expected_energy_diagonal_bound (n := n) beta (1 / Real.sqrt (2 * (n : ℝ)))
  have heq : beta ^ 2 * (1 / Real.sqrt (2 * (n : ℝ))) ^ 2 * ((n : ℝ) ^ 2 - n) = beta ^ 2 * ((n : ℝ) - 1) / 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
    have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
    field_simp
  rwa [heq] at h
end SKConstants
