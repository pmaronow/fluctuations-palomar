module

public import SKBarriers2.Corner.FrozenCoef8
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

noncomputable section
open scoped BigOperators Matrix ContDiff Topology NNReal
open Set MeasureTheory ProbabilityTheory Filter OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

def standardGaussianVector (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance (n : ℕ) : IsProbabilityMeasure (standardGaussianVector n) := by
  unfold standardGaussianVector
  infer_instance

def gaussianProductWeight {n : ℕ} (d : ℕ) (g : Fin n → ℝ) : ℝ :=
  ∏ i, gaussianPolynomialWeight d (g i)

theorem gaussianProductWeight_nonneg {n : ℕ} (d : ℕ) (g : Fin n → ℝ) :
    0 ≤ gaussianProductWeight d g := by
  exact Finset.prod_nonneg (fun i _ => by unfold gaussianPolynomialWeight; positivity)

theorem gaussianProductWeight_integrable (n d : ℕ) :
    Integrable (gaussianProductWeight (n := n) d) (standardGaussianVector n) :=
  Integrable.fintype_prod (fun _ => gaussianPolynomialWeight_integrable d)

theorem gaussianProductWeight_integral (n d : ℕ) :
    (∫ g, gaussianProductWeight (n := n) d g ∂standardGaussianVector n) =
      (∫ t, gaussianPolynomialWeight d t ∂gaussianReal 0 1) ^ n := by
  simpa only [Fintype.card_fin, gaussianProductWeight, standardGaussianVector] using
    (integral_fintype_prod_eq_pow (ι := Fin n) (gaussianPolynomialWeight d)
      (μ := gaussianReal 0 1))

theorem integrable_of_gaussianProductWeight_bound {n d : ℕ}
    {F : (Fin n → ℝ) → ℝ} {B : ℝ}
    (hm : AEStronglyMeasurable F (standardGaussianVector n))
    (hb : ∀ g, |F g| ≤ B * gaussianProductWeight d g) :
    Integrable F (standardGaussianVector n) :=
  ((gaussianProductWeight_integrable n d).const_mul B).mono' hm
    (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hb g))

theorem gaussianProductIntegral_abs_le {n d : ℕ} {F : (Fin n → ℝ) → ℝ} {B : ℝ}
    (hb : ∀ g, |F g| ≤ B * gaussianProductWeight d g) :
    |∫ g, F g ∂standardGaussianVector n| ≤
      B * (∫ t, gaussianPolynomialWeight d t ∂gaussianReal 0 1) ^ n := by
  have H := norm_integral_le_of_norm_le (f := F)
    ((gaussianProductWeight_integrable n d).const_mul B)
    (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hb g))
  simpa only [Real.norm_eq_abs, integral_const_mul, gaussianProductWeight_integral] using H

theorem standardGaussianVector_integral_cons {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : Integrable F (standardGaussianVector (n + 1))) :
    (∫ g, F g ∂standardGaussianVector (n + 1)) =
      ∫ t, ∫ g, F (Fin.cons t g) ∂standardGaussianVector n ∂gaussianReal 0 1 := by
  let e := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => gaussianReal 0 1) 0).symm
  have he : (∫ g, F g ∂standardGaussianVector (n + 1)) =
      ∫ p : ℝ × (Fin n → ℝ), F (Fin.cons p.1 p.2)
        ∂(gaussianReal 0 1).prod (standardGaussianVector n) := by
    unfold standardGaussianVector
    rw [← e.integral_comp']
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq]
  rw [he]
  apply integral_prod
  have hi := (e.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hF
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq, Function.comp_def,
    standardGaussianVector] using hi

private theorem gaussianProductWeight_cons {n : ℕ} (d : ℕ) (t : ℝ) (g : Fin n → ℝ) :
    gaussianProductWeight d (Fin.cons t g) =
      gaussianPolynomialWeight d t * gaussianProductWeight d g := by
  simp only [gaussianProductWeight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

private theorem standardGaussianVector_integral_zero (F : (Fin 0 → ℝ) → ℝ) :
    (∫ g, F g ∂standardGaussianVector 0) = F Fin.elim0 := by
  have he : F = fun _ => F Fin.elim0 := funext (fun g => congrArg F (Subsingleton.elim _ _))
  rw [he]
  simp

theorem gaussianProductIntegral_derivatives {n d : ℕ}
    {F F₁ F₂ : ℝ → (Fin n → ℝ) → ℝ} {U : Set ℝ} {B : ℝ}
    (hU : IsOpen U)
    (hc : ∀ k ∈ U, Continuous (F k) ∧ Continuous (F₁ k) ∧ Continuous (F₂ k))
    (hd : ∀ k ∈ U, ∀ g, HasDerivAt (fun x => F x g) (F₁ k g) k ∧
      HasDerivAt (fun x => F₁ x g) (F₂ k g) k)
    (hb : ∀ k ∈ U, ∀ g, |F k g| ≤ B * gaussianProductWeight d g ∧
      |F₁ k g| ≤ B * gaussianProductWeight d g ∧
      |F₂ k g| ≤ B * gaussianProductWeight d g) :
    ∀ k ∈ U,
      HasDerivAt (fun x => ∫ g, F x g ∂standardGaussianVector n)
        (∫ g, F₁ k g ∂standardGaussianVector n) k ∧
      HasDerivAt (fun x => ∫ g, F₁ x g ∂standardGaussianVector n)
        (∫ g, F₂ k g ∂standardGaussianVector n) k := by
  induction n generalizing B with
  | zero =>
    simpa only [standardGaussianVector_integral_zero] using fun k hk => hd k hk Fin.elim0
  | succ n ih =>
    have hi (x : ℝ) (hx : x ∈ U) :
        Integrable (F x) (standardGaussianVector (n + 1)) ∧
        Integrable (F₁ x) (standardGaussianVector (n + 1)) ∧
        Integrable (F₂ x) (standardGaussianVector (n + 1)) :=
      ⟨integrable_of_gaussianProductWeight_bound (hc x hx).1.aestronglyMeasurable
          (fun g => (hb x hx g).1),
        integrable_of_gaussianProductWeight_bound (hc x hx).2.1.aestronglyMeasurable
          (fun g => (hb x hx g).2.1),
        integrable_of_gaussianProductWeight_bound (hc x hx).2.2.aestronglyMeasurable
          (fun g => (hb x hx g).2.2)⟩
    have hiDeriv (t : ℝ) := ih
      (F := fun x g => F x (Fin.cons t g))
      (F₁ := fun x g => F₁ x (Fin.cons t g))
      (F₂ := fun x g => F₂ x (Fin.cons t g))
      (B := B * gaussianPolynomialWeight d t)
      (fun x hx => ⟨(hc x hx).1.comp (by fun_prop),
        (hc x hx).2.1.comp (by fun_prop), (hc x hx).2.2.comp (by fun_prop)⟩)
      (fun x hx g => hd x hx (Fin.cons t g))
      (fun x hx g => by
        simpa only [gaussianProductWeight_cons, mul_assoc] using hb x hx (Fin.cons t g))
    intro k hk
    have HO := gaussian_polynomial_integral_controls (hU.mem_nhds hk)
      (F := fun x t => ∫ g, F x (Fin.cons t g) ∂standardGaussianVector n)
      (F₁ := fun x t => ∫ g, F₁ x (Fin.cons t g) ∂standardGaussianVector n)
      (F₂ := fun x t => ∫ g, F₂ x (Fin.cons t g) ∂standardGaussianVector n)
      (B := B * (∫ t, gaussianPolynomialWeight d t ∂gaussianReal 0 1) ^ n)
      (n := d) (by
        intro x hx
        exact ⟨((hc x hx).1.comp (by fun_prop : Continuous
            (fun p : ℝ × (Fin n → ℝ) => Fin.cons p.1 p.2))).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable,
          ((hc x hx).2.1.comp (by fun_prop : Continuous
            (fun p : ℝ × (Fin n → ℝ) => Fin.cons p.1 p.2))).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable,
          ((hc x hx).2.2.comp (by fun_prop : Continuous
            (fun p : ℝ × (Fin n → ℝ) => Fin.cons p.1 p.2))).stronglyMeasurable.integral_prod_right'.aestronglyMeasurable⟩)
      (fun t x hx => hiDeriv t x hx) (by
        intro x hx t
        have H₀ := gaussianProductIntegral_abs_le (F := fun g => F x (Fin.cons t g))
          (B := B * gaussianPolynomialWeight d t) (d := d) (fun g => by
            simpa only [gaussianProductWeight_cons, mul_assoc] using (hb x hx (Fin.cons t g)).1)
        have H₁ := gaussianProductIntegral_abs_le (F := fun g => F₁ x (Fin.cons t g))
          (B := B * gaussianPolynomialWeight d t) (d := d) (fun g => by
            simpa only [gaussianProductWeight_cons, mul_assoc] using (hb x hx (Fin.cons t g)).2.1)
        have H₂ := gaussianProductIntegral_abs_le (F := fun g => F₂ x (Fin.cons t g))
          (B := B * gaussianPolynomialWeight d t) (d := d) (fun g => by
            simpa only [gaussianProductWeight_cons, mul_assoc] using (hb x hx (Fin.cons t g)).2.2)
        exact ⟨by simpa only [mul_assoc, mul_left_comm, mul_comm] using H₀,
          by simpa only [mul_assoc, mul_left_comm, mul_comm] using H₁,
          by simpa only [mul_assoc, mul_left_comm, mul_comm] using H₂⟩)
    have he₀ : (fun x => ∫ g, F x g ∂standardGaussianVector (n + 1)) =ᶠ[𝓝 k]
        (fun x => ∫ t, ∫ g, F x (Fin.cons t g) ∂standardGaussianVector n ∂gaussianReal 0 1) :=
      Filter.mem_of_superset (hU.mem_nhds hk)
        (fun x hx => standardGaussianVector_integral_cons (hi x hx).1)
    have he₁ : (fun x => ∫ g, F₁ x g ∂standardGaussianVector (n + 1)) =ᶠ[𝓝 k]
        (fun x => ∫ t, ∫ g, F₁ x (Fin.cons t g) ∂standardGaussianVector n ∂gaussianReal 0 1) :=
      Filter.mem_of_superset (hU.mem_nhds hk)
        (fun x hx => standardGaussianVector_integral_cons (hi x hx).2.1)
    rw [standardGaussianVector_integral_cons (hi k hk).2.1,
      standardGaussianVector_integral_cons (hi k hk).2.2]
    exact ⟨HO.1.hasDerivAt.congr_of_eventuallyEq he₀,
      HO.2.hasDerivAt.congr_of_eventuallyEq he₁⟩

def gaussianVectorAffine {n : ℕ} (A : Fin (n + 1) → ℝ → ℝ)
    (k : ℝ) (g : Fin n → ℝ) : ℝ :=
  A 0 k + ∑ i : Fin n, A i.succ k * g i

private theorem one_add_sum_abs_le_product {ι : Type*} (s : Finset ι) (g : ι → ℝ) :
    1 + ∑ i ∈ s, |g i| ≤ ∏ i ∈ s, (1 + |g i|) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have hP : 1 ≤ ∏ j ∈ s, (1 + |g j|) :=
      Finset.one_le_prod₀ (fun j _ => by linarith [abs_nonneg (g j)])
    nlinarith [mul_nonneg (abs_nonneg (g i)) (sub_nonneg.mpr hP)]

theorem gaussianVectorAffine_bound {n : ℕ} {A : Fin (n + 1) → ℝ → ℝ}
    {k z M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hA : ∀ i, |A i k - (if i = 0 then z else 0)| ≤ M * ρ) (g : Fin n → ℝ) :
    |gaussianVectorAffine A k g - z| ≤ (M * gaussianProductWeight 1 g) * ρ := by
  have h₀ : |A 0 k - z| ≤ M * ρ := by simpa using hA 0
  have h₁ (i : Fin n) : |A i.succ k| ≤ M * ρ := by simpa using hA i.succ
  calc
    _ = |(A 0 k - z) + ∑ i : Fin n, A i.succ k * g i| := by
      congr 1
      unfold gaussianVectorAffine
      ring
    _ ≤ |A 0 k - z| + |∑ i : Fin n, A i.succ k * g i| := abs_add_le _ _
    _ ≤ M * ρ + ∑ i : Fin n, M * ρ * |g i| := add_le_add h₀
      ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (h₁ i) (abs_nonneg _))))
    _ = M * ρ * (1 + ∑ i : Fin n, |g i|) := by rw [mul_add, Finset.mul_sum]; ring
    _ ≤ M * ρ * gaussianProductWeight 1 g := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hM hρ)
      simpa only [gaussianProductWeight, gaussianPolynomialWeight, pow_one] using
        one_add_sum_abs_le_product Finset.univ g
    _ = _ := by ring

def VectorAffineRegularOn {n : ℕ} (A A₁ A₂ : Fin (n + 1) → ℝ → ℝ)
    (U : Set ℝ) : Prop :=
  ∀ k ∈ U, ∀ i, HasDerivAt (A i) (A₁ i k) k ∧ HasDerivAt (A₁ i) (A₂ i k) k

def VectorAffineScaleBound {n : ℕ} (A A₁ A₂ : Fin (n + 1) → ℝ → ℝ)
    (U : Set ℝ) (z M ρ : ℝ) : Prop :=
  ∀ k ∈ U, ∀ i, |A i k - (if i = 0 then z else 0)| ≤ M * ρ ∧
    |A₁ i k| ≤ M * ρ ∧ |A₂ i k| ≤ M * ρ

def vectorAffineLift {n : ℕ} (A : Fin (n + 1) → ℝ → ℝ)
    (g : Fin n → ℝ) : Fin 3 → ℝ → ℝ :=
  ![fun k => gaussianVectorAffine A k g, fun _ => 0, fun _ => 0]

private theorem vectorAffineLift_regular {n : ℕ}
    {A A₁ A₂ : Fin (n + 1) → ℝ → ℝ} {U : Set ℝ}
    (hA : VectorAffineRegularOn A A₁ A₂ U) (g : Fin n → ℝ) :
    JointAffineRegularOn (vectorAffineLift A g) (vectorAffineLift A₁ g)
      (vectorAffineLift A₂ g) U := by
  intro k hk i
  fin_cases i
  · constructor
    · apply (hA k hk 0).1.add
      exact HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        ((hA k hk i.succ).1.mul_const (g i)))
    · apply (hA k hk 0).2.add
      exact HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
        ((hA k hk i.succ).2.mul_const (g i)))
  · exact ⟨hasDerivAt_const k 0, hasDerivAt_const k 0⟩
  · exact ⟨hasDerivAt_const k 0, hasDerivAt_const k 0⟩

private theorem vectorAffineLift_scale {n : ℕ} {A A₁ A₂ : Fin (n + 1) → ℝ → ℝ}
    {U : Set ℝ} {z M ρ : ℝ} (hM : 0 ≤ M) (hρ : 0 ≤ ρ)
    (hA : VectorAffineScaleBound A A₁ A₂ U z M ρ) (g : Fin n → ℝ) :
    JointAffineScaleBound (vectorAffineLift A g) (vectorAffineLift A₁ g)
      (vectorAffineLift A₂ g) U z (M * gaussianProductWeight 1 g) ρ := by
  have hW := gaussianProductWeight_nonneg 1 g
  intro k hk i
  fin_cases i
  · change |gaussianVectorAffine A k g - z| ≤ _ ∧
      |gaussianVectorAffine A₁ k g| ≤ _ ∧ |gaussianVectorAffine A₂ k g| ≤ _
    refine ⟨gaussianVectorAffine_bound hM hρ (fun j => (hA k hk j).1) g, ?_, ?_⟩
    · simpa only [sub_zero] using (gaussianVectorAffine_bound (z := 0) hM hρ
        (fun j => by simpa using (hA k hk j).2.1) g)
    · simpa only [sub_zero] using (gaussianVectorAffine_bound (z := 0) hM hρ
        (fun j => by simpa using (hA k hk j).2.2) g)
  · change |(0 : ℝ) - 0| ≤ _ ∧ |(0 : ℝ)| ≤ _ ∧ |(0 : ℝ)| ≤ _
    simp only [sub_zero, abs_zero]
    exact ⟨by positivity, by positivity, by positivity⟩
  · change |(0 : ℝ) - 0| ≤ _ ∧ |(0 : ℝ)| ≤ _ ∧ |(0 : ℝ)| ≤ _
    simp only [sub_zero, abs_zero]
    exact ⟨by positivity, by positivity, by positivity⟩

def vectorTailProductJet {n : ℕ} (f : ℝ → ℝ) (z : ℝ)
    (A A₁ A₂ B B₁ B₂ : Fin (n + 1) → ℝ → ℝ) (g : Fin n → ℝ) : JointGaussianJet :=
  jointTailProductJet f z (vectorAffineLift A g) (vectorAffineLift A₁ g)
    (vectorAffineLift A₂ g) (vectorAffineLift B g) (vectorAffineLift B₁ g) (vectorAffineLift B₂ g)

private theorem gaussianProductWeight_one_pow {n : ℕ} (d : ℕ) (g : Fin n → ℝ) :
    gaussianProductWeight 1 g ^ d = gaussianProductWeight d g := by
  simp only [gaussianProductWeight, gaussianPolynomialWeight, pow_one, Finset.prod_pow]

theorem vectorTailProductJet_bound {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {J M ρ z : ℝ} (hJ : 0 ≤ J) (hM : 0 ≤ M) (hρ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (h₃ : |iteratedDeriv 3 f z| ≤ J) (h₄ : ∀ y, |iteratedDeriv 4 f y| ≤ J)
    {A A₁ A₂ B B₁ B₂ : Fin (n + 1) → ℝ → ℝ} {U : Set ℝ}
    (hA : VectorAffineScaleBound A A₁ A₂ U z M ρ)
    (hB : VectorAffineScaleBound B B₁ B₂ U z M ρ) :
    ∀ k ∈ U, ∀ g,
      |(vectorTailProductJet f z A A₁ A₂ B B₁ B₂ g).value k 0 0| ≤
        (16 * J ^ 2 * (2 * M ^ 7 + M ^ 8) * ρ ^ 7) * gaussianProductWeight 8 g ∧
      |(vectorTailProductJet f z A A₁ A₂ B B₁ B₂ g).first k 0 0| ≤
        (16 * J ^ 2 * (2 * M ^ 7 + M ^ 8) * ρ ^ 7) * gaussianProductWeight 8 g ∧
      |(vectorTailProductJet f z A A₁ A₂ B B₁ B₂ g).second k 0 0| ≤
        (16 * J ^ 2 * (2 * M ^ 7 + M ^ 8) * ρ ^ 7) * gaussianProductWeight 8 g := by
  intro k hk g
  have hW : 1 ≤ gaussianProductWeight 1 g := Finset.one_le_prod₀ (fun i _ => by
    simp only [gaussianPolynomialWeight, pow_one]
    linarith [abs_nonneg (g i)])
  have H := jointTailProductJet_bound hf hJ
    (mul_nonneg hM (gaussianProductWeight_nonneg 1 g)) hρ hρ₁ h₃ h₄
    (vectorAffineLift_scale hM hρ hA g) (vectorAffineLift_scale hM hρ hB g) k hk 0 0
  simp only [gaussianPolynomialWeight, abs_zero, add_zero, one_pow, mul_one] at H
  have hP : gaussianProductWeight 1 g ^ 7 ≤ gaussianProductWeight 1 g ^ 8 :=
    pow_le_pow_right₀ hW (by norm_num)
  have he : 16 * J ^ 2 * (2 * (M * gaussianProductWeight 1 g) ^ 7 +
      (M * gaussianProductWeight 1 g) ^ 8) * ρ ^ 7 ≤
      (16 * J ^ 2 * (2 * M ^ 7 + M ^ 8) * ρ ^ 7) * gaussianProductWeight 8 g := by
    rw [mul_pow, mul_pow, ← gaussianProductWeight_one_pow 8 g]
    calc
      _ ≤ 16 * J ^ 2 * (2 * (M ^ 7 * gaussianProductWeight 1 g ^ 8) +
        M ^ 8 * gaussianProductWeight 1 g ^ 8) * ρ ^ 7 := by gcongr
      _ = _ := by ring
  exact ⟨H.1.trans he, H.2.1.trans he, H.2.2.trans he⟩

private theorem vectorTailProductJet_continuous {n : ℕ} {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (z k : ℝ)
    (A A₁ A₂ B B₁ B₂ : Fin (n + 1) → ℝ → ℝ) :
    Continuous (fun g => (vectorTailProductJet f z A A₁ A₂ B B₁ B₂ g).value k 0 0) ∧
    Continuous (fun g => (vectorTailProductJet f z A A₁ A₂ B B₁ B₂ g).first k 0 0) ∧
    Continuous (fun g => (vectorTailProductJet f z A A₁ A₂ B B₁ B₂ g).second k 0 0) := by
  have hf₁ := contDiff_deriv_infty hf
  have hf₂ : ContDiff ℝ ∞ (iteratedDeriv 2 f) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero] using
      contDiff_deriv_infty hf₁
  have hC : Continuous (scalarCubicPart f z) := by unfold scalarCubicPart; fun_prop
  have hC₁ : Continuous (scalarCubicPartFirst f z) := by unfold scalarCubicPartFirst; fun_prop
  have hC₂ : Continuous (scalarCubicPartSecond f z) := by unfold scalarCubicPartSecond; fun_prop
  have hT : Continuous (scalarFourthTail f z) :=
    hf.continuous.sub (scalarTaylorPolynomial_contDiff f 3 z).continuous
  have hT₁ : Continuous (scalarFourthTailFirst f z) :=
    hf₁.continuous.sub (scalarTaylorPolynomial_contDiff (deriv f) 2 z).continuous
  have hT₂ : Continuous (scalarFourthTailSecond f z) :=
    hf₂.continuous.sub (scalarTaylorPolynomial_contDiff (iteratedDeriv 2 f) 1 z).continuous
  have hX (C : Fin (n + 1) → ℝ → ℝ) :
      Continuous (fun g => jointGaussianAffine (vectorAffineLift C g) k 0 0) := by
    simp only [jointGaussianAffine, vectorAffineLift, Matrix.cons_val_zero,
      mul_zero, add_zero]
    unfold gaussianVectorAffine
    fun_prop
  dsimp only [vectorTailProductJet, jointTailProductJet, JointGaussianJet.add,
    JointGaussianJet.mul, jointCubicJet, jointFourthTailJet, jointAffineRemainderJet]
  exact ⟨by fun_prop, by fun_prop, by fun_prop⟩

def vectorTaylorTailError {n : ℕ} (f : ℝ → ℝ) (z : ℝ)
    (A B : Fin (n + 1) → ℝ → ℝ) (k : ℝ) : ℝ :=
  ∫ g, (f (gaussianVectorAffine A k g) - scalarTaylorPolynomial f 2 z (gaussianVectorAffine A k g)) *
      (f (gaussianVectorAffine B k g) - scalarTaylorPolynomial f 2 z (gaussianVectorAffine B k g)) -
    scalarCubicPart f z (gaussianVectorAffine A k g) *
      scalarCubicPart f z (gaussianVectorAffine B k g) ∂standardGaussianVector n

theorem vectorTaylorTailError_eq {n : ℕ} (f : ℝ → ℝ) (z : ℝ)
    (A A₁ A₂ B B₁ B₂ : Fin (n + 1) → ℝ → ℝ) :
    vectorTaylorTailError f z A B =
      fun k => ∫ g, (vectorTailProductJet f z A A₁ A₂ B B₁ B₂ g).value k 0 0
        ∂standardGaussianVector n := by
  funext k
  apply integral_congr_ae
  apply ae_of_all
  intro g
  dsimp only
  rw [scalarResidual_eq_cubic_add_fourth, scalarResidual_eq_cubic_add_fourth]
  dsimp only [vectorTailProductJet, jointTailProductJet, JointGaussianJet.add,
    JointGaussianJet.mul, jointCubicJet, jointFourthTailJet, jointAffineRemainderJet,
    jointGaussianAffine, vectorAffineLift, Matrix.cons_val_zero]
  simp only [mul_zero, add_zero]
  ring

theorem vectorTaylorTailError_control {n : ℕ} {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {J M h z : ℝ} (hJ : 0 ≤ J) (hM : 0 ≤ M) (hh : 0 ≤ h) (hh₁ : h ≤ 1)
    (h₃ : |iteratedDeriv 3 f z| ≤ J) (h₄ : ∀ y, |iteratedDeriv 4 f y| ≤ J)
    {A A₁ A₂ B B₁ B₂ : Fin (n + 1) → ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hA : VectorAffineRegularOn A A₁ A₂ U) (hB : VectorAffineRegularOn B B₁ B₂ U)
    (hpA : VectorAffineScaleBound A A₁ A₂ U z M (Real.sqrt h))
    (hpB : VectorAffineScaleBound B B₁ B₂ U z M (Real.sqrt h)) :
    ∃ f₁ f₂ : ℝ → ℝ, ∀ k ∈ U,
      HasDerivAt (vectorTaylorTailError f z A B) (f₁ k) k ∧ HasDerivAt f₁ (f₂ k) k ∧
      |vectorTaylorTailError f z A B k| ≤
        (16 * J ^ 2 * (2 * M ^ 7 + M ^ 8) *
          (∫ g, gaussianPolynomialWeight 8 g ∂gaussianReal 0 1) ^ n) * Real.sqrt h * h ^ 3 ∧
      |f₁ k| ≤ (16 * J ^ 2 * (2 * M ^ 7 + M ^ 8) *
          (∫ g, gaussianPolynomialWeight 8 g ∂gaussianReal 0 1) ^ n) * Real.sqrt h * h ^ 3 ∧
      |f₂ k| ≤ (16 * J ^ 2 * (2 * M ^ 7 + M ^ 8) *
          (∫ g, gaussianPolynomialWeight 8 g ∂gaussianReal 0 1) ^ n) * Real.sqrt h * h ^ 3 := by
  let V (k : ℝ) (g : Fin n → ℝ) := (vectorTailProductJet f z A A₁ A₂ B B₁ B₂ g).value k 0 0
  let V₁ (k : ℝ) (g : Fin n → ℝ) := (vectorTailProductJet f z A A₁ A₂ B B₁ B₂ g).first k 0 0
  let V₂ (k : ℝ) (g : Fin n → ℝ) := (vectorTailProductJet f z A A₁ A₂ B B₁ B₂ g).second k 0 0
  have hc := fun k (_ : k ∈ U) => vectorTailProductJet_continuous hf z k A A₁ A₂ B B₁ B₂
  have hd (k : ℝ) (hk : k ∈ U) (g : Fin n → ℝ) :
      HasDerivAt (fun x => V x g) (V₁ k g) k ∧
      HasDerivAt (fun x => V₁ x g) (V₂ k g) k :=
    (jointTailProductJet_regular hf z (vectorAffineLift_regular hA g)
      (vectorAffineLift_regular hB g)).2 k hk 0 0
  have hb := vectorTailProductJet_bound hf hJ hM (Real.sqrt_nonneg h)
    (Real.sqrt_le_one.mpr hh₁) h₃ h₄ hpA hpB
  have HD := gaussianProductIntegral_derivatives hU hc hd hb
  have he := vectorTaylorTailError_eq f z A A₁ A₂ B B₁ B₂
  have hs : Real.sqrt h ^ 7 = Real.sqrt h * h ^ 3 := by
    calc
      _ = Real.sqrt h * (Real.sqrt h ^ 2) ^ 3 := by ring
      _ = _ := by rw [Real.sq_sqrt hh]
  have hen : (16 * J ^ 2 * (2 * M ^ 7 + M ^ 8) * Real.sqrt h ^ 7) *
      (∫ g, gaussianPolynomialWeight 8 g ∂gaussianReal 0 1) ^ n =
      (16 * J ^ 2 * (2 * M ^ 7 + M ^ 8) *
        (∫ g, gaussianPolynomialWeight 8 g ∂gaussianReal 0 1) ^ n) * Real.sqrt h * h ^ 3 := by
    rw [hs]
    ring
  refine ⟨fun k => ∫ g, V₁ k g ∂standardGaussianVector n,
    fun k => ∫ g, V₂ k g ∂standardGaussianVector n, ?_⟩
  intro k hk
  have h₀ := gaussianProductIntegral_abs_le (F := V k) (fun g => (hb k hk g).1)
  have h₁ := gaussianProductIntegral_abs_le (F := V₁ k) (fun g => (hb k hk g).2.1)
  have h₂ := gaussianProductIntegral_abs_le (F := V₂ k) (fun g => (hb k hk g).2.2)
  rw [hen] at h₀ h₁ h₂
  exact ⟨by simpa only [he] using (HD k hk).1, (HD k hk).2,
    by simpa only [he] using h₀, h₁, h₂⟩

theorem scalarData_vectorTaylorTailError_control {β : ℝ} (D : ScalarData β)
    (n : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ s h z : ℝ,
      0 ≤ h → h ≤ 1 → s + 4 * h ∈ Icc (0 : ℝ) 1 →
      ∀ (U : Set ℝ), IsOpen U → ∀ A A₁ A₂ B B₁ B₂ : Fin (n + 1) → ℝ → ℝ,
      VectorAffineRegularOn A A₁ A₂ U → VectorAffineRegularOn B B₁ B₂ U →
      VectorAffineScaleBound A A₁ A₂ U z M (Real.sqrt h) →
      VectorAffineScaleBound B B₁ B₂ U z M (Real.sqrt h) →
      ∃ f₁ f₂ : ℝ → ℝ, ∀ k ∈ U,
        HasDerivAt (vectorTaylorTailError (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)) z A B)
          (f₁ k) k ∧ HasDerivAt f₁ (f₂ k) k ∧
        |vectorTaylorTailError (Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)) z A B k| ≤
          C * Real.sqrt h * h ^ 3 ∧
        |f₁ k| ≤ C * Real.sqrt h * h ^ 3 ∧ |f₂ k| ≤ C * Real.sqrt h * h ^ 3 := by
  let J := scalarTerminalJetBound D 4 + 1
  have hJ : 0 < J := by dsimp only [J]; linarith [scalarTerminalJetBound_nonneg D 4]
  let K := 16 * J ^ 2 * (2 * M ^ 7 + M ^ 8) *
    (∫ g, gaussianPolynomialWeight 8 g ∂gaussianReal 0 1) ^ n
  have hI : 0 ≤ ∫ g, gaussianPolynomialWeight 8 g ∂gaussianReal 0 1 :=
    integral_nonneg (fun _ => by unfold gaussianPolynomialWeight; positivity)
  refine ⟨K + 1, by dsimp only [K]; positivity, ?_⟩
  intro s h z hh hh₁ ht U hU A A₁ A₂ B B₁ B₂ hA hB hpA hpB
  let f := Phi β (cdf (D.μ : Measure ℝ)) (s + 4 * h)
  have hj (j : ℕ) (hj₁ : 1 ≤ j) (hj₄ : j ≤ 4) (y : ℝ) :
      |iteratedDeriv j f y| ≤ J :=
    (scalarData_jet_le D hj₁ hj₄ ht y).trans (by dsimp only [J]; linarith)
  obtain ⟨f₁, f₂, H⟩ := vectorTaylorTailError_control (scalarData_phi_contDiff D ht)
    hJ.le hM hh hh₁ (hj 3 (by norm_num) (by norm_num) z)
    (hj 4 (by norm_num) le_rfl) hU hA hB hpA hpB
  have hen : K * Real.sqrt h * h ^ 3 ≤ (K + 1) * Real.sqrt h * h ^ 3 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : K ≤ K + 1) (Real.sqrt_nonneg h))
      (pow_nonneg hh 3)
  refine ⟨f₁, f₂, ?_⟩
  intro k hk
  have Hk := H k hk
  exact ⟨Hk.1, Hk.2.1, Hk.2.2.1.trans hen, Hk.2.2.2.1.trans hen, Hk.2.2.2.2.trans hen⟩

theorem hasExpGrowth_integrable_standardGaussianVector {n : ℕ}
    {F : (Fin n → ℝ) → ℝ} (hc : Continuous F) (hg : HasExpGrowth F) :
    Integrable F (standardGaussianVector n) := by
  obtain ⟨C, M, hC, hM, hb⟩ := hg
  have hi : Integrable (fun g : Fin n → ℝ => ∏ i, Real.exp (M * |g i|))
      (standardGaussianVector n) :=
    Integrable.fintype_prod (fun _ => integrable_exp_mul_abs_gaussian M)
  apply (hi.const_mul C).mono' hc.aestronglyMeasurable
  apply ae_of_all
  intro g
  have hnorm : ‖g‖ ≤ ∑ i : Fin n, |g i| :=
    (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg (g i)))).mpr
      (fun i => by
        rw [Real.norm_eq_abs]
        exact Finset.single_le_sum (fun j _ => abs_nonneg (g j)) (Finset.mem_univ i))
  calc
    ‖F g‖ ≤ C * Real.exp (M * ‖g‖) := hb g
    _ ≤ C * Real.exp (M * ∑ i : Fin n, |g i|) := by gcongr
    _ = C * ∏ i : Fin n, Real.exp (M * |g i|) := by
      rw [Finset.mul_sum, Real.exp_sum]

private theorem originalNoise_hasExpGrowth_affine {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} (hf : HasExpGrowth f) (c : F) (L : E →L[ℝ] F) :
    HasExpGrowth (fun x => f (c + L x)) := by
  obtain ⟨C, M, hC, hM, hb⟩ := hf
  refine ⟨C * Real.exp (M * ‖c‖), M * ‖L‖, by positivity, by positivity, ?_⟩
  intro x
  calc
    _ ≤ C * Real.exp (M * ‖c + L x‖) := hb _
    _ ≤ C * Real.exp (M * (‖c‖ + ‖L‖ * ‖x‖)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
          (add_le_add (le_refl ‖c‖) (L.le_opNorm x))) hM)) hC
    _ = _ := by rw [mul_add, ← mul_assoc M ‖L‖ ‖x‖, Real.exp_add]; ring

def quadraticNoisePath : (l : List (ℝ × Vec3)) → QuadraticTerminal →
    Vec3 → (Fin l.length → ℝ) → Vec3
  | [], _, x, _ => x
  | u :: l, Q, x, g => quadraticNoisePath l Q
      (quadraticNoiseConstant (riccatiRecursion l Q) u.1 u.2 +
        quadraticNoiseCLM (riccatiRecursion l Q) u.1 u.2 (x, g 0))
      (fun i => g i.succ)

private def quadraticNoisePathStepLinear (n : ℕ) (Q : QuadraticTerminal) (u : ℝ × Vec3) :
    (Vec3 × (Fin (n + 1) → ℝ)) →ₗ[ℝ] (Vec3 × (Fin n → ℝ)) where
  toFun p := (quadraticNoiseLinear Q u.1 u.2 (p.1, p.2 0), fun i => p.2 i.succ)
  map_add' p q := by
    apply Prod.ext
    · exact (quadraticNoiseLinear Q u.1 u.2).map_add (p.1, p.2 0) (q.1, q.2 0)
    · rfl
  map_smul' c p := by
    apply Prod.ext
    · exact (quadraticNoiseLinear Q u.1 u.2).map_smul c (p.1, p.2 0)
    · rfl

theorem quadraticNoisePath_continuous_expGrowth (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    {K : Vec3 → ℝ} (hK : Continuous K) (hg : HasExpGrowth K) :
    Continuous (fun p : Vec3 × (Fin l.length → ℝ) => K (quadraticNoisePath l Q p.1 p.2)) ∧
    HasExpGrowth (fun p : Vec3 × (Fin l.length → ℝ) => K (quadraticNoisePath l Q p.1 p.2)) := by
  induction l with
  | nil =>
    simp only [List.length_nil]
    exact ⟨hK.comp continuous_fst, hg.compCLM (ContinuousLinearMap.fst ℝ Vec3 (Fin 0 → ℝ))⟩
  | cons u l ih =>
    let L := (quadraticNoisePathStepLinear l.length (riccatiRecursion l Q) u).toContinuousLinearMap
    let c : Vec3 × (Fin l.length → ℝ) :=
      (quadraticNoiseConstant (riccatiRecursion l Q) u.1 u.2, 0)
    have he : (fun p : Vec3 × (Fin (u :: l).length → ℝ) =>
        K (quadraticNoisePath (u :: l) Q p.1 p.2)) =
        fun p => K (quadraticNoisePath l Q (c + L p).1 (c + L p).2) := by
      simp only [quadraticNoisePath, c, L, quadraticNoisePathStepLinear,
        Prod.fst_add, Prod.snd_add, zero_add]
      rfl
    rw [he]
    exact ⟨ih.1.comp (continuous_const.add L.continuous),
      originalNoise_hasExpGrowth_affine ih.2 c L⟩

theorem quadraticNoisePath_integrable (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    {K : Vec3 → ℝ} (hK : Continuous K) (hg : HasExpGrowth K) (x : Vec3) :
    Integrable (fun g => K (quadraticNoisePath l Q x g)) (standardGaussianVector l.length) := by
  have H := quadraticNoisePath_continuous_expGrowth l Q hK hg
  let L : (Fin l.length → ℝ) →L[ℝ] (Vec3 × (Fin l.length → ℝ)) :=
    (0 : (Fin l.length → ℝ) →L[ℝ] Vec3).prod (ContinuousLinearMap.id ℝ _)
  have he : (fun g => K (quadraticNoisePath l Q x g)) =
      fun g => K (quadraticNoisePath l Q ((x, 0) + L g).1 ((x, 0) + L g).2) := by
    simp only [L, ContinuousLinearMap.prod_apply, zero_apply,
      ContinuousLinearMap.id_apply, Prod.fst_add, Prod.snd_add, add_zero, zero_add]
  rw [he]
  exact hasExpGrowth_integrable_standardGaussianVector
    (H.1.comp (continuous_const.add L.continuous))
    (originalNoise_hasExpGrowth_affine H.2 (x, 0) L)

theorem quadraticNoisePath_affine (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) :
    ∃ c : Vec3, ∃ L : (Vec3 × (Fin l.length → ℝ)) →L[ℝ] Vec3,
      ∀ p, quadraticNoisePath l Q p.1 p.2 = c + L p := by
  induction l with
  | nil => exact ⟨0, ContinuousLinearMap.fst ℝ _ _, fun p => (zero_add p.1).symm⟩
  | cons u l ih =>
    obtain ⟨c, L, hL⟩ := ih
    let M := (quadraticNoisePathStepLinear l.length (riccatiRecursion l Q) u).toContinuousLinearMap
    let d : Vec3 × (Fin l.length → ℝ) :=
      (quadraticNoiseConstant (riccatiRecursion l Q) u.1 u.2, 0)
    refine ⟨c + L d, L.comp M, ?_⟩
    intro p
    have he : quadraticNoisePath (u :: l) Q p.1 p.2 =
        quadraticNoisePath l Q (d + M p).1 (d + M p).2 := by
      simp only [quadraticNoisePath, d, M, quadraticNoisePathStepLinear,
        Prod.fst_add, Prod.snd_add, zero_add]
      rfl
    rw [he, hL, map_add]
    exact (add_assoc _ _ _).symm

theorem quadraticNoisePath_zero (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (x : Vec3) :
    quadraticNoisePath l Q x 0 = gaussianPathMean l Q x := by
  induction l generalizing x with
  | nil => rfl
  | cons u l ih =>
    simp only [quadraticNoisePath, Pi.zero_apply, quadraticNoise_affine,
      mul_zero, add_zero, gaussianPathMean, quadraticMeanTransition]
    exact ih _

def quadraticNoiseCoefficients (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (x : Vec3) (i : Fin 3) : Fin (l.length + 1) → ℝ :=
  Fin.cons (quadraticNoisePath l Q x 0 i)
    (fun j => quadraticNoisePath l Q x (Pi.single j 1) i - quadraticNoisePath l Q x 0 i)

theorem quadraticNoisePath_eq_affine_coefficients
    (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (x : Vec3) (i : Fin 3)
    (g : Fin l.length → ℝ) :
    quadraticNoisePath l Q x g i =
      quadraticNoiseCoefficients l Q x i 0 +
        ∑ j : Fin l.length, quadraticNoiseCoefficients l Q x i j.succ * g j := by
  obtain ⟨c, L, hL⟩ := quadraticNoisePath_affine l Q
  have hg : ((0 : Vec3), g) = ∑ j : Fin l.length, g j • ((0 : Vec3), Pi.single j (1 : ℝ)) := by
    ext j
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hsplit : (x, g) = (x, 0) + (0, g) := by simp
  have he (j : Fin l.length) : quadraticNoiseCoefficients l Q x i j.succ =
      L (0, Pi.single j (1 : ℝ)) i := by
    simp only [quadraticNoiseCoefficients, Fin.cons_succ,
      hL (x, Pi.single j 1), hL (x, 0)]
    rw [show (x, Pi.single j (1 : ℝ)) = (x, (0 : Fin l.length → ℝ)) +
      ((0 : Vec3), Pi.single j (1 : ℝ)) by simp, map_add]
    simp
  have hz : quadraticNoiseCoefficients l Q x i 0 = (c + L (x, 0)) i := by
    simp only [quadraticNoiseCoefficients, Fin.cons_zero, hL (x, 0)]
  rw [hL (x, g), hsplit, map_add, hg, map_sum, hz]
  simp only [he,
    map_smul, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [← add_assoc]
  apply congrArg (fun t => c i + L (x, 0) i + t)
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadraticNoisePath_shared_zero (l t : List (ℝ × Vec3))
    (Q : QuadraticTerminal) (x : Vec3) :
    quadraticNoisePath t Q (quadraticNoisePath l (riccatiRecursion t Q) x 0) 0 =
      gaussianPathMean (l ++ t) Q x := by
  rw [quadraticNoisePath_zero, quadraticNoisePath_zero, gaussianPathMean_append]

theorem frozenSchedule_original_intercept (β a h k c u χ z : ℝ)
    (hh : 0 ≤ h) (hk : |k| ≤ 1 / 2)
    (hQ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (separableTaylorQuadratic c u χ z))
    (l t : List (ℝ × Vec3)) (hlt : l ++ t = frozenSchedule β a (1 / 2) h k) (i : Fin 3) :
    quadraticNoisePath t (separableTaylorQuadratic c u χ z)
      (quadraticNoisePath l (riccatiRecursion t (separableTaylorQuadratic c u χ z))
        (fun _ => z) 0) 0 i =
      z + 4 * a * β ^ 2 * h * u / (1 - 4 * a * β ^ 2 * χ * h) := by
  rw [quadraticNoisePath_shared_zero, hlt]
  exact frozenSchedule_pathMean β a h k c u χ z hh hk hQ i

theorem quadraticFirst_eq_original_noises (l : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible l Q) {K : Vec3 → ℝ}
    (hK : Continuous K) (hg : HasExpGrowth K) (x : Vec3) :
    quadraticFirst l Q K x =
      ∫ g, K (quadraticNoisePath l Q x g) ∂standardGaussianVector l.length := by
  induction l generalizing x with
  | nil => simpa only [List.length_nil, quadraticFirst, quadraticNoisePath] using
      (standardGaussianVector_integral_zero (fun _ : Fin 0 → ℝ => K x)).symm
  | cons u l ih =>
    have HK := quadraticFirst_continuous_expGrowth l Q hl.1 hK hg
    simp only [List.length_cons]
    rw [quadraticFirst, quadraticAverage_eq_standard_of_kernel _ u.1 u.2 x hl.2.2 HK.1,
      standardGaussianVector_integral_cons (quadraticNoisePath_integrable (u :: l) Q hK hg x)]
    apply integral_congr_ae
    apply ae_of_all
    intro t
    simpa only [quadraticNoisePath, Fin.cons_zero, Fin.cons_succ] using ih hl.1
      (quadraticNoiseConstant (riccatiRecursion l Q) u.1 u.2 +
        quadraticNoiseCLM (riccatiRecursion l Q) u.1 u.2 (x, t))

theorem quadraticFirst_conditional_product_original_noises
    (l t : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible (l ++ t) Q) {F G : Vec3 → ℝ}
    (hF : Continuous F) (hgF : HasExpGrowth F)
    (hG : Continuous G) (hgG : HasExpGrowth G) (x : Vec3) :
    quadraticFirst l (riccatiRecursion t Q)
      (fun y => quadraticFirst t Q F y * quadraticFirst t Q G y) x =
      ∫ p, ∫ a, ∫ b,
        F (quadraticNoisePath t Q (quadraticNoisePath l (riccatiRecursion t Q) x p) a) *
          G (quadraticNoisePath t Q (quadraticNoisePath l (riccatiRecursion t Q) x p) b)
        ∂standardGaussianVector t.length ∂standardGaussianVector t.length
        ∂standardGaussianVector l.length := by
  have hA := (riccatiAdmissible_append l t Q).mp hl
  have HF := quadraticFirst_continuous_expGrowth t Q hA.1 hF hgF
  have HG := quadraticFirst_continuous_expGrowth t Q hA.1 hG hgG
  have he := quadraticFirst_eq_original_noises l _ hA.2
    (K := fun y => quadraticFirst t Q F y * quadraticFirst t Q G y)
    (HF.1.mul HG.1) (HF.2.mul HG.2) x
  rw [he]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  dsimp only
  rw [quadraticFirst_eq_original_noises t Q hA.1 hF hgF,
    quadraticFirst_eq_original_noises t Q hA.1 hG hgG]
  simp only [integral_const_mul, integral_mul_const]

theorem quadraticFirst_conditional_square_original_noises
    (l t : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible (l ++ t) Q) {K : Vec3 → ℝ}
    (hK : Continuous K) (hg : HasExpGrowth K) (x : Vec3) :
    quadraticFirst l (riccatiRecursion t Q)
      (fun y => quadraticFirst t Q K y ^ 2) x =
      ∫ p, ∫ a, ∫ b,
        K (quadraticNoisePath t Q (quadraticNoisePath l (riccatiRecursion t Q) x p) a) *
          K (quadraticNoisePath t Q (quadraticNoisePath l (riccatiRecursion t Q) x p) b)
        ∂standardGaussianVector t.length ∂standardGaussianVector t.length
        ∂standardGaussianVector l.length := by
  simpa only [pow_two] using quadraticFirst_conditional_product_original_noises
    l t Q hl hK hg hK hg x

theorem frozenSchedule_shared_noises_le_twenty_four
    (β a h k : ℝ) (l t : List (ℝ × Vec3))
    (hlt : l ++ t = frozenSchedule β a (1 / 2) h k) :
    l.length + 2 * t.length ≤ 24 := by
  have H := congrArg List.length hlt
  rw [List.length_append, frozenSchedule_length] at H
  omega

def originalConditionalSquare (l t : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) (x : Vec3) : ℝ :=
  ∫ p, ∫ a, ∫ b,
    K (quadraticNoisePath t Q (quadraticNoisePath l (riccatiRecursion t Q) x p) a) *
      K (quadraticNoisePath t Q (quadraticNoisePath l (riccatiRecursion t Q) x p) b)
    ∂standardGaussianVector t.length ∂standardGaussianVector t.length
    ∂standardGaussianVector l.length

theorem quadraticFirst_conditional_square_eq_originalConditionalSquare
    (l t : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (hl : RiccatiAdmissible (l ++ t) Q) {K : Vec3 → ℝ}
    (hK : Continuous K) (hg : HasExpGrowth K) (x : Vec3) :
    quadraticFirst l (riccatiRecursion t Q)
      (fun y => quadraticFirst t Q K y ^ 2) x =
      originalConditionalSquare l t Q K x :=
  quadraticFirst_conditional_square_original_noises l t Q hl hK hg x

theorem frozenSchedule_second_original_squares (β a h k : ℝ) (Q : QuadraticTerminal)
    {K : Vec3 → ℝ} (hQ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) Q)
    (hK : Continuous K) (hg : HasExpGrowth K) (x : Vec3) :
    quadraticSecond (frozenSchedule β a (1 / 2) h k) Q K x =
      a * originalConditionalSquare (frozenSchedule β a (1 / 2) h k) [] Q K x -
      a / 2 * originalConditionalSquare
        (frozenCommon β a (1 / 2) h k ++ frozenShared β a (1 / 2) h k)
        (frozenInner β a (1 / 2) h k) Q K x -
      a / 6 * originalConditionalSquare (frozenCommon β a (1 / 2) h k)
        (frozenShared β a (1 / 2) h k ++ frozenInner β a (1 / 2) h k) Q K x -
      a / 3 * originalConditionalSquare [] (frozenSchedule β a (1 / 2) h k) Q K x := by
  have h₀ := quadraticFirst_conditional_square_eq_originalConditionalSquare
    (frozenSchedule β a (1 / 2) h k) [] Q (by simpa using hQ) hK hg x
  have h₁ := quadraticFirst_conditional_square_eq_originalConditionalSquare
    (frozenCommon β a (1 / 2) h k ++ frozenShared β a (1 / 2) h k)
    (frozenInner β a (1 / 2) h k) Q (by simpa [frozenSchedule, List.append_assoc] using hQ) hK hg x
  have h₂ := quadraticFirst_conditional_square_eq_originalConditionalSquare
    (frozenCommon β a (1 / 2) h k)
    (frozenShared β a (1 / 2) h k ++ frozenInner β a (1 / 2) h k) Q hQ hK hg x
  have h₃ := quadraticFirst_conditional_square_eq_originalConditionalSquare
    [] (frozenSchedule β a (1 / 2) h k) Q hQ hK hg x
  simp only [quadraticFirst, riccatiRecursion] at h₀ h₃
  rw [frozenSchedule_second_nested_squares β a h k Q hQ hK hg x, h₀, h₁, h₂, h₃]

def originalFrozenSecond (β a h k : ℝ) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) (x : Vec3) : ℝ :=
  a * originalConditionalSquare (frozenSchedule β a (1 / 2) h k) [] Q K x -
    a / 2 * originalConditionalSquare
      (frozenCommon β a (1 / 2) h k ++ frozenShared β a (1 / 2) h k)
      (frozenInner β a (1 / 2) h k) Q K x -
    a / 6 * originalConditionalSquare (frozenCommon β a (1 / 2) h k)
      (frozenShared β a (1 / 2) h k ++ frozenInner β a (1 / 2) h k) Q K x -
    a / 3 * originalConditionalSquare [] (frozenSchedule β a (1 / 2) h k) Q K x

def originalWickTailCoefficientError (β : ℝ) (α : ℝ → ℝ) (a s h z k : ℝ) : ℝ :=
  let Q := terminalTaylorQuadratic β α s h z
  let K := terminalResidual β α s h z
  let P := terminalCubicResidual β α s h z
  ((originalFrozenSecond β a h k Q K (fun _ => z) -
      originalFrozenSecond β a h k Q P (fun _ => z)) -
    (originalFrozenSecond β a h 0 Q K (fun _ => z) -
      originalFrozenSecond β a h 0 Q P (fun _ => z))) / 2

theorem wickTailCoefficientError_eq_original (β : ℝ) (α : ℝ → ℝ) (a s h z k : ℝ)
    (hφ : BoundedDerivs (Phi β α (s + 4 * h)))
    (hQk : RiccatiAdmissible (frozenSchedule β a (1 / 2) h k) (terminalTaylorQuadratic β α s h z))
    (hQ₀ : RiccatiAdmissible (frozenSchedule β a (1 / 2) h 0) (terminalTaylorQuadratic β α s h z)) :
    wickTailCoefficientError β α a s h z k = originalWickTailCoefficientError β α a s h z k := by
  have hK := terminalResidual_continuous β α s h z hφ
  have hgK := terminalResidual_hasExpGrowth β α s h z hφ
  have hP := terminalCubicResidual_continuous_expGrowth β α s h z
  unfold wickTailCoefficientError frozenSecondMoment originalWickTailCoefficientError
  change _ = ((originalFrozenSecond _ _ _ _ _ _ _ - originalFrozenSecond _ _ _ _ _ _ _) -
    (originalFrozenSecond _ _ _ _ _ _ _ - originalFrozenSecond _ _ _ _ _ _ _)) / 2
  rw [frozenSchedule_second_original_squares β a h k _ hQk hK hgK,
    frozenSchedule_second_original_squares β a h k _ hQk hP.1 hP.2,
    frozenSchedule_second_original_squares β a h 0 _ hQ₀ hK hgK,
    frozenSchedule_second_original_squares β a h 0 _ hQ₀ hP.1 hP.2]
  rfl

theorem scalarData_wickTailCoefficientError_eq_original {β : ℝ} (D : ScalarData β) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ a s h z : ℝ,
      a ∈ Ioc (0 : ℝ) 1 → 0 ≤ h → h ≤ h₀ → s + 4 * h ∈ Icc (0 : ℝ) 1 →
      ∀ k : ℝ, |k| ≤ 1 / 2 →
        wickTailCoefficientError β (cdf (D.μ : Measure ℝ)) a s h z k =
          originalWickTailCoefficientError β (cdf (D.μ : Measure ℝ)) a s h z k := by
  let B := scalarTerminalJetBound D 2 + 1
  have hB : 0 < B := by dsimp only [B]; linarith [scalarTerminalJetBound_nonneg D 2]
  obtain ⟨h₀, hh₀, H⟩ := terminalTaylorQuadratic_uniform_admissible β B hB
  refine ⟨h₀, hh₀, ?_⟩
  intro a s h z ha hh hh₀' ht k hk
  have hχ : |jet β (cdf (D.μ : Measure ℝ)) 2 (s + 4 * h) z| ≤ B :=
    (scalarData_jet_le D (by norm_num : 1 ≤ 2) le_rfl ht z).trans (by dsimp only [B]; linarith)
  exact wickTailCoefficientError_eq_original β _ a s h z k (scalarData_phi_regular D ht)
    (H _ a s h k z ha hh hh₀' hk hχ)
    (H _ a s h 0 z ha hh hh₀' (by norm_num) hχ)

private def originalNoiseRestriction {ι κ : Type} [Fintype ι] [Fintype κ]
    (f : κ → ι) : (ι → ℝ) →L[ℝ] (κ → ℝ) :=
  ({ toFun := fun g i => g (f i)
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : (ι → ℝ) →ₗ[ℝ] (κ → ℝ)).toContinuousLinearMap

theorem quadraticNoisePath_affine_inputs {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : List (ℝ × Vec3)) (Q : QuadraticTerminal) (x : Vec3)
    (X : E →L[ℝ] Vec3) (G : E →L[ℝ] (Fin l.length → ℝ)) :
    ∃ c : Vec3, ∃ L : E →L[ℝ] Vec3,
      ∀ g, quadraticNoisePath l Q (x + X g) (G g) = c + L g := by
  obtain ⟨c, L, hL⟩ := quadraticNoisePath_affine l Q
  refine ⟨c + L (x, 0), L.comp (X.prod G), ?_⟩
  intro g
  have he : (x + X g, G g) = (x, 0) + (X.prod G) g := by simp
  rw [hL (x + X g, G g), he, map_add]
  exact (add_assoc _ _ _).symm

private theorem originalSharedProduct_continuous_expGrowth {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l t : List (ℝ × Vec3)) (Q : QuadraticTerminal) (x : Vec3)
    (P : E →L[ℝ] (Fin l.length → ℝ)) (A B : E →L[ℝ] (Fin t.length → ℝ))
    {K : Vec3 → ℝ} (hc : Continuous K) (hg : HasExpGrowth K) :
    Continuous (fun g =>
      K (quadraticNoisePath t Q (quadraticNoisePath l (riccatiRecursion t Q) x (P g)) (A g)) *
      K (quadraticNoisePath t Q (quadraticNoisePath l (riccatiRecursion t Q) x (P g)) (B g))) ∧
    HasExpGrowth (fun g =>
      K (quadraticNoisePath t Q (quadraticNoisePath l (riccatiRecursion t Q) x (P g)) (A g)) *
      K (quadraticNoisePath t Q (quadraticNoisePath l (riccatiRecursion t Q) x (P g)) (B g))) := by
  obtain ⟨cP, LP, hP⟩ := quadraticNoisePath_affine_inputs l (riccatiRecursion t Q) x
    (0 : E →L[ℝ] Vec3) P
  have hp (g : E) : quadraticNoisePath l (riccatiRecursion t Q) x (P g) = cP + LP g := by
    simpa using hP g
  obtain ⟨cA, LA, hA⟩ := quadraticNoisePath_affine_inputs t Q cP LP A
  obtain ⟨cB, LB, hB⟩ := quadraticNoisePath_affine_inputs t Q cP LP B
  simp_rw [hp, hA, hB]
  exact ⟨(hc.comp (continuous_const.add LA.continuous)).mul
      (hc.comp (continuous_const.add LB.continuous)),
    (originalNoise_hasExpGrowth_affine hg cA LA).mul
      (originalNoise_hasExpGrowth_affine hg cB LB)⟩

private theorem originalNoise_integrable_fintype {ι : Type} [Fintype ι]
    {F : (ι → ℝ) → ℝ} (hc : Continuous F) (hg : HasExpGrowth F) :
    Integrable F (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  obtain ⟨C, M, hC, hM, hb⟩ := hg
  have hi : Integrable (fun g : ι → ℝ => ∏ i, Real.exp (M * |g i|))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    Integrable.fintype_prod (fun _ => integrable_exp_mul_abs_gaussian M)
  apply (hi.const_mul C).mono' hc.aestronglyMeasurable
  apply ae_of_all
  intro g
  have hnorm : ‖g‖ ≤ ∑ i : ι, |g i| :=
    (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg (g i)))).mpr
      (fun i => by
        rw [Real.norm_eq_abs]
        exact Finset.single_le_sum (fun j _ => abs_nonneg (g j)) (Finset.mem_univ i))
  calc
    ‖F g‖ ≤ C * Real.exp (M * ‖g‖) := hb g
    _ ≤ C * Real.exp (M * ∑ i : ι, |g i|) := by gcongr
    _ = C * ∏ i : ι, Real.exp (M * |g i|) := by rw [Finset.mul_sum, Real.exp_sum]

private theorem originalNoise_integral_sum {ι κ : Type} [Fintype ι] [Fintype κ]
    {F : ((ι ⊕ κ) → ℝ) → ℝ}
    (hF : Integrable F (Measure.pi (fun _ : ι ⊕ κ => gaussianReal 0 1))) :
    (∫ g, F g ∂Measure.pi (fun _ : ι ⊕ κ => gaussianReal 0 1)) =
      ∫ p, ∫ q, F (Sum.elim p q)
        ∂Measure.pi (fun _ : κ => gaussianReal 0 1)
        ∂Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  let e := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : ι ⊕ κ => gaussianReal 0 1)
  have hi := e.integrable_comp_of_integrable hF
  have he := e.integral_comp' F
  change (∫ p : (ι → ℝ) × (κ → ℝ), F (Sum.elim p.1 p.2)
      ∂(Measure.pi (fun _ : ι => gaussianReal 0 1)).prod
        (Measure.pi (fun _ : κ => gaussianReal 0 1))) = _ at he
  rw [← he]
  exact integral_prod _ hi

abbrev OriginalSharedNoiseIndex (l t : List (ℝ × Vec3)) :=
  Fin l.length ⊕ (Fin t.length ⊕ Fin t.length)

theorem originalSharedNoiseIndex_card (l t : List (ℝ × Vec3)) :
    Fintype.card (OriginalSharedNoiseIndex l t) = l.length + 2 * t.length := by
  simp only [OriginalSharedNoiseIndex, Fintype.card_sum, Fintype.card_fin]
  omega

theorem frozenSchedule_originalSharedNoiseIndex_card_le (β a h k : ℝ)
    (l t : List (ℝ × Vec3)) (hlt : l ++ t = frozenSchedule β a (1 / 2) h k) :
    Fintype.card (OriginalSharedNoiseIndex l t) ≤ 24 := by
  rw [originalSharedNoiseIndex_card]
  exact frozenSchedule_shared_noises_le_twenty_four β a h k l t hlt

def originalSharedNoiseProduct (l t : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    (K : Vec3 → ℝ) (x : Vec3) (g : OriginalSharedNoiseIndex l t → ℝ) : ℝ :=
  let y := quadraticNoisePath l (riccatiRecursion t Q) x (fun i => g (.inl i))
  K (quadraticNoisePath t Q y (fun i => g (.inr (.inl i)))) *
    K (quadraticNoisePath t Q y (fun i => g (.inr (.inr i))))

theorem originalConditionalSquare_eq_pi (l t : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    {K : Vec3 → ℝ} (hc : Continuous K) (hg : HasExpGrowth K) (x : Vec3) :
    originalConditionalSquare l t Q K x =
      ∫ g, originalSharedNoiseProduct l t Q K x g
        ∂Measure.pi (fun _ : OriginalSharedNoiseIndex l t => gaussianReal 0 1) := by
  let F := originalSharedNoiseProduct l t Q K x
  have H := originalSharedProduct_continuous_expGrowth
    (E := OriginalSharedNoiseIndex l t → ℝ) l t Q x
    (originalNoiseRestriction (fun i : Fin l.length => (Sum.inl i : OriginalSharedNoiseIndex l t)))
    (originalNoiseRestriction (fun i : Fin t.length => (Sum.inr (Sum.inl i) : OriginalSharedNoiseIndex l t)))
    (originalNoiseRestriction (fun i : Fin t.length => (Sum.inr (Sum.inr i) : OriginalSharedNoiseIndex l t))) hc hg
  have hi : Integrable F (Measure.pi (fun _ : OriginalSharedNoiseIndex l t => gaussianReal 0 1)) :=
    originalNoise_integrable_fintype H.1 H.2
  rw [originalNoise_integral_sum hi]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  have hs : Integrable (fun q : (Fin t.length ⊕ Fin t.length) → ℝ => F (Sum.elim p q))
      (Measure.pi (fun _ : Fin t.length ⊕ Fin t.length => gaussianReal 0 1)) := by
    let A := originalNoiseRestriction (fun i : Fin t.length => (Sum.inl i : Fin t.length ⊕ Fin t.length))
    let B := originalNoiseRestriction (fun i : Fin t.length => (Sum.inr i : Fin t.length ⊕ Fin t.length))
    let y := quadraticNoisePath l (riccatiRecursion t Q) x p
    have HA := quadraticNoisePath_affine_inputs t Q y (0 : ((Fin t.length ⊕ Fin t.length) → ℝ) →L[ℝ] Vec3) A
    have HB := quadraticNoisePath_affine_inputs t Q y (0 : ((Fin t.length ⊕ Fin t.length) → ℝ) →L[ℝ] Vec3) B
    obtain ⟨cA, LA, hA⟩ := HA
    obtain ⟨cB, LB, hB⟩ := HB
    have he : (fun q : (Fin t.length ⊕ Fin t.length) → ℝ => F (Sum.elim p q)) =
        fun q => K (cA + LA q) * K (cB + LB q) := by
      funext q
      simpa only [F, originalSharedNoiseProduct, Sum.elim_inl, Sum.elim_inr, y,
        add_zero, zero_apply, A, B, originalNoiseRestriction,
        LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk] using
          congrArg₂ (fun a b => K a * K b) (hA q) (hB q)
    rw [he]
    exact originalNoise_integrable_fintype
      ((hc.comp (continuous_const.add LA.continuous)).mul
        (hc.comp (continuous_const.add LB.continuous)))
      ((originalNoise_hasExpGrowth_affine hg cA LA).mul
        (originalNoise_hasExpGrowth_affine hg cB LB))
  dsimp only
  rw [originalNoise_integral_sum hs]
  rfl

theorem originalConditionalSquare_eq_finiteGaussian
    (l t : List (ℝ × Vec3)) (Q : QuadraticTerminal)
    {K : Vec3 → ℝ} (hc : Continuous K) (hg : HasExpGrowth K) (x : Vec3) :
    originalConditionalSquare l t Q K x =
      ∫ g, originalSharedNoiseProduct l t Q K x
        (fun i => g ((Fintype.equivFin (OriginalSharedNoiseIndex l t)) i))
        ∂standardGaussianVector (Fintype.card (OriginalSharedNoiseIndex l t)) := by
  rw [originalConditionalSquare_eq_pi l t Q hc hg x]
  have H := (measurePreserving_piCongrLeft
    (fun _ : OriginalSharedNoiseIndex l t => gaussianReal 0 1)
    (Fintype.equivFin (OriginalSharedNoiseIndex l t)).symm).integral_comp'
      (originalSharedNoiseProduct l t Q K x)
  have he (g : Fin (Fintype.card (OriginalSharedNoiseIndex l t)) → ℝ) :
      (MeasurableEquiv.piCongrLeft (fun _ : OriginalSharedNoiseIndex l t => ℝ)
        (Fintype.equivFin (OriginalSharedNoiseIndex l t)).symm) g =
        fun i => g ((Fintype.equivFin (OriginalSharedNoiseIndex l t)) i) := by
    funext i
    simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,
      Equiv.symm_symm, eq_rec_constant]
  simpa only [he, standardGaussianVector] using H.symm

end SKBarriers2.Corner
