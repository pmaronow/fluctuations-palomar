module
public import SKConstants.PredictableGaussianSums
public import SKConstants.ScalarProcessPosteriorIncrement

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
namespace SKConstants

lemma integrable_gaussian_centered_square_affine_sq (v : ℝ≥0) (a b : ℝ) :
    Integrable (fun x : ℝ => (a+b*(x^2-(v : ℝ)))^2) (gaussianReal 0 v) := by
  have he : (fun x : ℝ => (a+b*(x^2-(v : ℝ)))^2) =
      (fun x => (a-b*(v : ℝ))^2+2*(a-b*(v : ℝ))*b*x^2+b^2*x^4) := by
    funext x
    ring
  rw [he]
  exact ((integrable_const _).add ((gaussianReal_integrable_pow 0 v 2).const_mul _)).add
    ((gaussianReal_integrable_pow 0 v 4).const_mul _)

lemma integral_gaussian_centered_square_affine_sq (v : ℝ≥0) (a b : ℝ) :
    (∫ x : ℝ, (a+b*(x^2-(v : ℝ)))^2 ∂gaussianReal 0 v) = a^2+2*b^2*(v : ℝ)^2 := by
  have he : (fun x : ℝ => (a+b*(x^2-(v : ℝ)))^2) =
      (fun x => (a-b*(v : ℝ))^2+2*(a-b*(v : ℝ))*b*x^2+b^2*x^4) := by
    funext x
    ring
  rw [he,integral_add (f := fun x : ℝ => (a-b*(v : ℝ))^2+2*(a-b*(v : ℝ))*b*x^2)
      (g := fun x : ℝ => b^2*x^4) ((integrable_const _).add
      ((gaussianReal_integrable_pow 0 v 2).const_mul _))
      ((gaussianReal_integrable_pow 0 v 4).const_mul _),
    integral_add (f := fun _ : ℝ => (a-b*(v : ℝ))^2)
      (g := fun x : ℝ => 2*(a-b*(v : ℝ))*b*x^2)
      (integrable_const _) ((gaussianReal_integrable_pow 0 v 2).const_mul _),
    integral_const_mul,integral_const_mul,gaussianReal_integral_fourth]
  have h2 : (∫ x : ℝ, x^2 ∂gaussianReal 0 v) = (v : ℝ) := by
    simpa only [sub_zero] using gaussianReal_integral_centered_sq 0 v
  rw [h2,integral_const]
  simp only [probReal_univ,one_smul,zero_pow (by decide : 4≠0),
    zero_pow (by decide : 2≠0),mul_zero,add_zero,zero_add]
  ring

lemma independent_gaussian_centered_square_step {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (v : ℝ≥0) (X A H : Ω → ℝ)
    (hstate : AEMeasurable (fun ω => (A ω,H ω)) P)
    (hX : HasLaw X (gaussianReal 0 v) P)
    (hindep : IndepFun (fun ω => (A ω,H ω)) X P)
    (hA : Integrable (fun ω => A ω^2) P) (hH : Integrable (fun ω => H ω^2) P) :
    Integrable (fun ω => (A ω+H ω*(X ω^2-(v : ℝ)))^2) P ∧
      (∫ ω, (A ω+H ω*(X ω^2-(v : ℝ)))^2 ∂P) =
        (∫ ω, A ω^2 ∂P)+2*(v : ℝ)^2*(∫ ω,H ω^2 ∂P) := by
  let S := fun ω => (A ω,H ω)
  let μ := P.map S
  have : IsFiniteMeasure μ := P.isFiniteMeasure_map S
  let f := fun p : (ℝ×ℝ)×ℝ => (p.1.1+p.1.2*(p.2^2-(v : ℝ)))^2
  have hm : Measurable f := by fun_prop
  have hAm : Integrable (fun p : ℝ×ℝ => p.1^2) μ :=
    (integrable_map_measure (by fun_prop) hstate).mpr hA
  have hHm : Integrable (fun p : ℝ×ℝ => p.2^2) μ :=
    (integrable_map_measure (by fun_prop) hstate).mpr hH
  have hp : Integrable f (μ.prod (gaussianReal 0 v)) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall (fun p => integrable_gaussian_centered_square_affine_sq v p.1 p.2)
    · convert hAm.add (hHm.const_mul (2*(v : ℝ)^2)) using 1
      funext p
      simp only [f,Real.norm_eq_abs,abs_pow,sq_abs,Pi.add_apply]
      rw [integral_gaussian_centered_square_affine_sq]
      ring
  have hlaw : HasLaw (fun ω => (S ω,X ω)) (μ.prod (gaussianReal 0 v)) P :=
    hindep.hasLaw_prod ⟨hstate,rfl⟩ hX
  refine ⟨hlaw.integrable_fun_comp hp,?_⟩
  have hi := hlaw.integral_comp hp.aestronglyMeasurable
  change (∫ ω,f (S ω,X ω) ∂P) = ∫ p,f p ∂μ.prod (gaussianReal 0 v) at hi
  rw [hi,integral_prod _ hp]
  simp only [f,integral_gaussian_centered_square_affine_sq]
  rw [integral_add hAm ((hHm.const_mul 2).mul_const ((v : ℝ)^2)),
    integral_mul_const,integral_const_mul,
    integral_map hstate (by fun_prop),integral_map hstate (by fun_prop)]
  dsimp only
  ring

def predictableGaussianCenteredSquareSum {Ω : Type*}
    (X H : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0) : ℕ → Ω → ℝ :=
  predictableGaussianSum (fun k ω => X k ω^2-(v k : ℝ)) H

lemma aemeasurable_predictableGaussianCenteredSquareSum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X H : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hX : ∀ k,AEMeasurable (X k) P) (hH : ∀ k,AEMeasurable (H k) P) (n : ℕ) :
    AEMeasurable (predictableGaussianCenteredSquareSum X H v n) P :=
  aemeasurable_predictableGaussianSum P _ H
    (fun k => (hX k).pow_const 2 |>.sub_const _) hH n

theorem predictableGaussianCenteredSquareSum_L2_isometry {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X H : ℕ → Ω → ℝ) (v : ℕ → ℝ≥0)
    (hX : ∀ k,HasLaw (X k) (gaussianReal 0 (v k)) P)
    (hH : ∀ k,AEMeasurable (H k) P)
    (hHsq : ∀ k,Integrable (fun ω => H k ω^2) P)
    (hindep : ∀ k,IndepFun
      (fun ω => (predictableGaussianCenteredSquareSum X H v k ω,H k ω)) (X k) P)
    (n : ℕ) :
    Integrable (fun ω => predictableGaussianCenteredSquareSum X H v n ω^2) P ∧
      (∫ ω,predictableGaussianCenteredSquareSum X H v n ω^2 ∂P) =
        ∑ k∈Finset.range n,2*(v k : ℝ)^2*(∫ ω,H k ω^2 ∂P) := by
  induction n with
  | zero => simp [predictableGaussianCenteredSquareSum,predictableGaussianSum]
  | succ n ih =>
    have hs := independent_gaussian_centered_square_step P (v n) (X n)
      (predictableGaussianCenteredSquareSum X H v n) (H n)
      ((aemeasurable_predictableGaussianCenteredSquareSum P X H v
        (fun k => (hX k).aemeasurable) hH n).prodMk (hH n))
      (hX n) (hindep n) ih.1 (hHsq n)
    refine ⟨hs.1,?_⟩
    change (∫ ω,(predictableGaussianCenteredSquareSum X H v n ω+H n ω*(X n ω^2-(v n : ℝ)))^2 ∂P)=_
    rw [hs.2,ih.2,Finset.sum_range_succ]

end SKConstants
