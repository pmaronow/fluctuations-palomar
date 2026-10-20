module
public import SKConstants.GaussianIntegralL2

public section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
noncomputable section
namespace SKConstants

lemma gaussian_predictable_fiber_factor (v : ℝ≥0) (theta : ℝ) (p : ℝ × ℝ × ℝ) (x : ℝ) :
    Real.exp (theta * (p.1 + p.2.1 * x) - theta ^ 2 * (p.2.2 + p.2.1 ^ 2 * (v : ℝ)) / 2) =
      Real.exp (theta * p.1 - theta ^ 2 * p.2.2 / 2) *
        Real.exp ((theta * p.2.1) * x - (v : ℝ) * (theta * p.2.1) ^ 2 / 2) := by
  rw [← Real.exp_add]
  congr 1
  ring
lemma gaussian_predictable_fiber_integrable (v : ℝ≥0) (theta : ℝ) (p : ℝ × ℝ × ℝ) :
    Integrable (fun x => Real.exp (theta * (p.1 + p.2.1 * x) -
      theta ^ 2 * (p.2.2 + p.2.1 ^ 2 * (v : ℝ)) / 2)) (gaussianReal 0 v) := by
  simp_rw [gaussian_predictable_fiber_factor]
  exact (integrable_gaussian_compensated_exp v (theta * p.2.1)).const_mul _
lemma gaussian_predictable_fiber_integral (v : ℝ≥0) (theta : ℝ) (p : ℝ × ℝ × ℝ) :
    (∫ x, Real.exp (theta * (p.1 + p.2.1 * x) -
      theta ^ 2 * (p.2.2 + p.2.1 ^ 2 * (v : ℝ)) / 2) ∂gaussianReal 0 v) =
      Real.exp (theta * p.1 - theta ^ 2 * p.2.2 / 2) := by
  simp_rw [gaussian_predictable_fiber_factor]
  rw [integral_const_mul, integral_gaussian_compensated_exp, mul_one]

lemma independent_gaussian_step_exponential {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (v : ℝ≥0) (X A H Q : Ω → ℝ) (theta : ℝ)
    (hstate : AEMeasurable (fun ω => (A ω, H ω, Q ω)) P)
    (hX : HasLaw X (gaussianReal 0 v) P)
    (hindep : IndepFun (fun ω => (A ω, H ω, Q ω)) X P)
    (hprior : Integrable (fun ω => Real.exp (theta * A ω - theta ^ 2 * Q ω / 2)) P) :
    Integrable (fun ω => Real.exp (theta * (A ω + H ω * X ω) -
      theta ^ 2 * (Q ω + H ω ^ 2 * (v : ℝ)) / 2)) P ∧
    (∫ ω, Real.exp (theta * (A ω + H ω * X ω) -
      theta ^ 2 * (Q ω + H ω ^ 2 * (v : ℝ)) / 2) ∂P) =
      ∫ ω, Real.exp (theta * A ω - theta ^ 2 * Q ω / 2) ∂P := by
  let S := fun ω => (A ω, H ω, Q ω)
  let μ := P.map S
  have : IsFiniteMeasure μ := P.isFiniteMeasure_map S
  let f := fun p : (ℝ × ℝ × ℝ) × ℝ => Real.exp (theta * (p.1.1 + p.1.2.1 * p.2) -
    theta ^ 2 * (p.1.2.2 + p.1.2.1 ^ 2 * (v : ℝ)) / 2)
  have hm : Measurable f := by fun_prop
  have hp : Integrable (fun p : ℝ × ℝ × ℝ => Real.exp (theta * p.1 - theta ^ 2 * p.2.2 / 2)) μ := by
    apply (integrable_map_measure (by fun_prop) hstate).mpr
    exact hprior
  have hprod : Integrable f (μ.prod (gaussianReal 0 v)) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall (gaussian_predictable_fiber_integrable v theta)
    · convert hp using 1
      funext p
      simp only [f, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact gaussian_predictable_fiber_integral v theta p
  have hlaw : HasLaw (fun ω => (S ω, X ω)) (μ.prod (gaussianReal 0 v)) P :=
    hindep.hasLaw_prod ⟨hstate, rfl⟩ hX
  refine ⟨hlaw.integrable_fun_comp hprod, ?_⟩
  have hi := hlaw.integral_comp hprod.aestronglyMeasurable
  change (∫ ω, f (S ω, X ω) ∂P) = ∫ p, f p ∂μ.prod (gaussianReal 0 v) at hi
  rw [hi, integral_prod _ hprod]
  simp only [f, gaussian_predictable_fiber_integral]
  exact (integral_map (f := fun p : ℝ × ℝ × ℝ => Real.exp (theta * p.1 - theta ^ 2 * p.2.2 / 2)) hstate (by fun_prop))

lemma independent_gaussian_step_square {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (v : ℝ≥0) (X A H : Ω → ℝ)
    (hstate : AEMeasurable (fun ω => (A ω, H ω)) P)
    (hX : HasLaw X (gaussianReal 0 v) P)
    (hindep : IndepFun (fun ω => (A ω, H ω)) X P)
    (hA : Integrable (fun ω => A ω ^ 2) P) (hH : Integrable (fun ω => H ω ^ 2) P) :
    Integrable (fun ω => (A ω + H ω * X ω) ^ 2) P ∧
    (∫ ω, (A ω + H ω * X ω) ^ 2 ∂P) =
      (∫ ω, A ω ^ 2 ∂P) + (v : ℝ) * ∫ ω, H ω ^ 2 ∂P := by
  let S := fun ω => (A ω, H ω)
  let μ := P.map S
  have : IsFiniteMeasure μ := P.isFiniteMeasure_map S
  let f := fun p : (ℝ × ℝ) × ℝ => (p.1.1 + p.1.2 * p.2) ^ 2
  have hm : Measurable f := by fun_prop
  have hAmap : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) μ :=
    (integrable_map_measure (by fun_prop) hstate).mpr hA
  have hHmap : Integrable (fun p : ℝ × ℝ => p.2 ^ 2) μ :=
    (integrable_map_measure (by fun_prop) hstate).mpr hH
  have hprod : Integrable f (μ.prod (gaussianReal 0 v)) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall (fun p => integrable_gaussian_affine_sq v p.1 p.2)
    · convert hAmap.add (hHmap.mul_const (v : ℝ)) using 1
      funext p
      simp only [f, Real.norm_eq_abs, abs_pow, sq_abs, Pi.add_apply]
      exact integral_gaussian_affine_sq v p.1 p.2
  have hlaw : HasLaw (fun ω => (S ω, X ω)) (μ.prod (gaussianReal 0 v)) P :=
    hindep.hasLaw_prod ⟨hstate, rfl⟩ hX
  refine ⟨hlaw.integrable_fun_comp hprod, ?_⟩
  have hi := hlaw.integral_comp hprod.aestronglyMeasurable
  change (∫ ω, f (S ω, X ω) ∂P) = ∫ p, f p ∂μ.prod (gaussianReal 0 v) at hi
  rw [hi, integral_prod _ hprod]
  simp only [f, integral_gaussian_affine_sq]
  rw [integral_add hAmap (hHmap.mul_const (v : ℝ)), integral_mul_const,
    integral_map hstate (by fun_prop), integral_map hstate (by fun_prop)]
  dsimp only
  ring

@[expose] def predictableGaussianSum {Ω : Type*} (X H : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n+1, ω => predictableGaussianSum X H n ω + H n ω * X n ω
@[expose] def predictableGaussianVariation {Ω : Type*} (v : ℕ → ℝ≥0)
    (H : ℕ → Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n+1, ω => predictableGaussianVariation v H n ω + H n ω ^ 2 * (v n : ℝ)
@[expose] def predictableGaussianExponential {Ω : Type*} (X H : ℕ → Ω → ℝ)
    (v : ℕ → ℝ≥0) (theta : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (theta * predictableGaussianSum X H n ω -
    theta ^ 2 * predictableGaussianVariation v H n ω / 2)

lemma aemeasurable_predictableGaussianSum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X H : ℕ → Ω → ℝ) (hX : ∀ k, AEMeasurable (X k) P)
    (hH : ∀ k, AEMeasurable (H k) P) (n : ℕ) :
    AEMeasurable (predictableGaussianSum X H n) P := by
  induction n with
  | zero => exact aemeasurable_const
  | succ n ih => exact ih.add ((hH n).mul (hX n))
lemma aemeasurable_predictableGaussianVariation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (v : ℕ → ℝ≥0) (H : ℕ → Ω → ℝ)
    (hH : ∀ k, AEMeasurable (H k) P) (n : ℕ) :
    AEMeasurable (predictableGaussianVariation v H n) P := by
  induction n with
  | zero => exact aemeasurable_const
  | succ n ih => exact ih.add ((hH n).pow_const 2 |>.mul_const (v n : ℝ))

lemma predictableGaussianExponential_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X H : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hX : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (hH : ∀ k, AEMeasurable (H k) P)
    (hindep : ∀ k, IndepFun
      (fun ω => (predictableGaussianSum X H k ω, H k ω, predictableGaussianVariation v H k ω))
      (X k) P) (theta : ℝ) (n : ℕ) :
    Integrable (predictableGaussianExponential X H v theta n) P ∧
      (∫ ω, predictableGaussianExponential X H v theta n ω ∂P) = 1 := by
  induction n with
  | zero =>
    constructor
    · rw [show predictableGaussianExponential X H v theta 0 = (fun _ : Ω => (1 : ℝ)) by
        funext ω
        simp [predictableGaussianExponential, predictableGaussianSum, predictableGaussianVariation]]
      exact integrable_const (1 : ℝ)
    · simp [predictableGaussianExponential, predictableGaussianSum, predictableGaussianVariation]
  | succ n ih =>
    have hstate := (aemeasurable_predictableGaussianSum P X H (fun k => (hX k).aemeasurable) hH n).prodMk
      ((hH n).prodMk (aemeasurable_predictableGaussianVariation P v H hH n))
    have hs := independent_gaussian_step_exponential P (v n) (X n)
      (predictableGaussianSum X H n) (H n) (predictableGaussianVariation v H n) theta
      hstate (hX n) (hindep n) ih.1
    exact ⟨hs.1, hs.2.trans ih.2⟩

lemma predictableGaussianVariation_nonneg {Ω : Type*} (v : ℕ → ℝ≥0)
    (H : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : 0 ≤ predictableGaussianVariation v H n ω := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact add_nonneg ih (mul_nonneg (sq_nonneg _) (v n).coe_nonneg)

lemma predictableGaussianSum_L2_isometry {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X H : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hX : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (hH : ∀ k, AEMeasurable (H k) P)
    (hHsq : ∀ k, Integrable (fun ω => H k ω ^ 2) P)
    (hindep : ∀ k, IndepFun
      (fun ω => (predictableGaussianSum X H k ω, H k ω, predictableGaussianVariation v H k ω))
      (X k) P) (n : ℕ) :
    Integrable (fun ω => predictableGaussianSum X H n ω ^ 2) P ∧
    Integrable (predictableGaussianVariation v H n) P ∧
    (∫ ω, predictableGaussianSum X H n ω ^ 2 ∂P) =
      ∫ ω, predictableGaussianVariation v H n ω ∂P := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · simp [predictableGaussianSum]
    · exact integrable_const (0 : ℝ)
    · simp [predictableGaussianSum, predictableGaussianVariation]
  | succ n ih =>
    have hi := (hindep n).comp (φ := fun p : ℝ × ℝ × ℝ => (p.1,p.2.1)) (ψ := id)
      (by fun_prop) measurable_id
    have hm := (aemeasurable_predictableGaussianSum P X H (fun k => (hX k).aemeasurable) hH n).prodMk (hH n)
    have hs := independent_gaussian_step_square P (v n) (X n) (predictableGaussianSum X H n)
      (H n) hm (hX n) hi ih.1 (hHsq n)
    refine ⟨hs.1, ih.2.1.add ((hHsq n).mul_const (v n : ℝ)), ?_⟩
    simp only [predictableGaussianSum]
    rw [hs.2, ih.2.2]
    change _ = ∫ ω, predictableGaussianVariation v H n ω + H n ω ^ 2 * (v n : ℝ) ∂P
    rw [integral_add ih.2.1 ((hHsq n).mul_const (v n : ℝ)), integral_mul_const]
    rw [mul_comm]
lemma predictableGaussianSum_eq_range_sum {Ω : Type*} (X H : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    predictableGaussianSum X H n ω = ∑ k ∈ Finset.range n, H k ω * X k ω := by
  induction n with
  | zero => simp [predictableGaussianSum]
  | succ n ih => simp only [predictableGaussianSum, Finset.sum_range_succ, ih]
lemma predictableGaussianVariation_eq_range_sum {Ω : Type*} (v : ℕ → ℝ≥0) (H : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    predictableGaussianVariation v H n ω = ∑ k ∈ Finset.range n, H k ω ^ 2 * (v k : ℝ) := by
  induction n with
  | zero => simp [predictableGaussianVariation]
  | succ n ih => simp only [predictableGaussianVariation, Finset.sum_range_succ, ih]
lemma predictableGaussianSum_eq_fin_sum {Ω : Type*} (X H : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    predictableGaussianSum X H n ω = ∑ k : Fin n, H k ω * X k ω := by
  rw [predictableGaussianSum_eq_range_sum, ← Fin.sum_univ_eq_sum_range]
lemma predictableGaussianVariation_eq_fin_sum {Ω : Type*} (v : ℕ → ℝ≥0) (H : ℕ → Ω → ℝ)
    (n : ℕ) (ω : Ω) :
    predictableGaussianVariation v H n ω = ∑ k : Fin n, H k ω ^ 2 * (v k : ℝ) := by
  rw [predictableGaussianVariation_eq_range_sum, ← Fin.sum_univ_eq_sum_range]

lemma predictableGaussianSum_mgf_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X H : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hX : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P)
    (hH : ∀ k, AEMeasurable (H k) P)
    (hindep : ∀ k, IndepFun
      (fun ω => (predictableGaussianSum X H k ω, H k ω, predictableGaussianVariation v H k ω))
      (X k) P) (theta : ℝ) (n : ℕ) (V : ℝ)
    (hV : ∀ᵐ ω ∂P, predictableGaussianVariation v H n ω ≤ V) :
    Integrable (fun ω => Real.exp (theta * predictableGaussianSum X H n ω)) P ∧
      mgf (predictableGaussianSum X H n) P theta ≤ Real.exp (theta ^ 2 * V / 2) := by
  have he := predictableGaussianExponential_integral P X H v hX hH hindep theta n
  have hbound : ∀ᵐ ω ∂P, Real.exp (theta * predictableGaussianSum X H n ω) ≤
      Real.exp (theta ^ 2 * V / 2) * predictableGaussianExponential X H v theta n ω := by
    filter_upwards [hV] with ω hw
    unfold predictableGaussianExponential
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hw (sq_nonneg theta)]
  have hi : Integrable (fun ω => Real.exp (theta * predictableGaussianSum X H n ω)) P := by
    refine (he.1.const_mul (Real.exp (theta ^ 2 * V / 2))).mono'
      ((aemeasurable_predictableGaussianSum P X H (fun k => (hX k).aemeasurable) hH n).const_mul theta).exp.aestronglyMeasurable ?_
    filter_upwards [hbound] with ω hw
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Pi.mul_apply] using hw
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, Real.exp (theta ^ 2 * V / 2) * predictableGaussianExponential X H v theta n ω ∂P :=
      integral_mono_ae hi (he.1.const_mul _) hbound
    _ = _ := by rw [integral_const_mul, he.2, mul_one]
lemma integral_predictableGaussianVariation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (v : ℕ → ℝ≥0) (H : ℕ → Ω → ℝ)
    (hHsq : ∀ k, Integrable (fun ω => H k ω ^ 2) P) (n : ℕ) :
    (∫ ω, predictableGaussianVariation v H n ω ∂P) =
      ∑ k : Fin n, (v k : ℝ) * ∫ ω, H k ω ^ 2 ∂P := by
  simp_rw [predictableGaussianVariation_eq_fin_sum]
  rw [integral_finsetSum (Finset.univ : Finset (Fin n)) (fun k _ => (hHsq (k : ℕ)).mul_const (v k : ℝ))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_mul_const, mul_comm]
end SKConstants
