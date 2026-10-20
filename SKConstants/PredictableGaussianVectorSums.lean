module
public import SKConstants.BrownianVectorFullPast
public import SKConstants.BrownianFullPastLikelihood

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

def gaussianVectorCompensatedExp {ι : Type*} [Fintype ι] (v : ℝ≥0)
    (θ : ℝ) (H x : ι → ℝ) : ℝ :=
  Real.exp (∑ i, ((θ*H i)*x i-(v : ℝ)*(θ*H i)^2/2))

lemma gaussianVectorCompensatedExp_eq_prod {ι : Type*} [Fintype ι] (v : ℝ≥0)
    (θ : ℝ) (H x : ι → ℝ) :
    gaussianVectorCompensatedExp v θ H x = ∏ i, Real.exp ((θ*H i)*x i-(v : ℝ)*(θ*H i)^2/2) :=
  Real.exp_sum _ _

lemma integral_gaussianVectorCompensatedExp {ι : Type*} [Fintype ι] (v : ℝ≥0)
    (θ : ℝ) (H : ι → ℝ) :
    (∫ x, gaussianVectorCompensatedExp v θ H x ∂Measure.pi (fun _ : ι => gaussianReal 0 v)) = 1 := by
  simp_rw [gaussianVectorCompensatedExp_eq_prod]
  rw [integral_fintype_prod_eq_prod (fun i x => Real.exp ((θ*H i)*x-(v : ℝ)*(θ*H i)^2/2))]
  simp_rw [integral_gaussian_compensated_exp]
  simp

lemma integrable_gaussianVectorCompensatedExp {ι : Type*} [Fintype ι] (v : ℝ≥0)
    (θ : ℝ) (H : ι → ℝ) :
    Integrable (gaussianVectorCompensatedExp v θ H) (Measure.pi (fun _ : ι => gaussianReal 0 v)) := by
  by_contra hn
  have h := integral_gaussianVectorCompensatedExp v θ H
  rw [integral_undef hn] at h
  norm_num at h

lemma gaussianVectorCompensatedExp_exponent {ι : Type*} [Fintype ι] (v : ℝ≥0)
    (θ : ℝ) (H x : ι → ℝ) :
    gaussianVectorCompensatedExp v θ H x =
      Real.exp (θ*(∑ i,H i*x i)-θ^2*(v : ℝ)*(∑ i,H i^2)/2) := by
  unfold gaussianVectorCompensatedExp
  congr 1
  rw [Finset.sum_sub_distrib]
  have hfirst : (∑ i,(θ*H i)*x i) = θ*(∑ i,H i*x i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsecond : (∑ i,(v : ℝ)*(θ*H i)^2/2) = θ^2*(v : ℝ)*(∑ i,H i^2)/2 := by
    rw [Finset.mul_sum,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfirst,hsecond]

lemma gaussian_vector_predictable_fiber_factor {ι : Type*} [Fintype ι]
    (v : ℝ≥0) (θ : ℝ) (p : ℝ × (ι → ℝ) × ℝ) (x : ι → ℝ) :
    Real.exp (θ*(p.1+∑ i,p.2.1 i*x i)-
      θ^2*(p.2.2+(v : ℝ)*∑ i,p.2.1 i^2)/2) =
      Real.exp (θ*p.1-θ^2*p.2.2/2)*gaussianVectorCompensatedExp v θ p.2.1 x := by
  rw [gaussianVectorCompensatedExp_exponent,← Real.exp_add]
  congr 1
  ring

lemma independent_gaussian_vector_step_exponential {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (v : ℝ≥0)
    (X H : Ω → ι → ℝ) (A V : Ω → ℝ) (θ : ℝ)
    (hstate : AEMeasurable (fun ω => (A ω,H ω,V ω)) P)
    (hX : HasLaw X (Measure.pi (fun _ : ι => gaussianReal 0 v)) P)
    (hindep : IndepFun (fun ω => (A ω,H ω,V ω)) X P)
    (hprior : Integrable (fun ω => Real.exp (θ*A ω-θ^2*V ω/2)) P) :
    Integrable (fun ω => Real.exp (θ*(A ω+∑ i,H ω i*X ω i)-
      θ^2*(V ω+(v : ℝ)*∑ i,H ω i^2)/2)) P ∧
      (∫ ω, Real.exp (θ*(A ω+∑ i,H ω i*X ω i)-
        θ^2*(V ω+(v : ℝ)*∑ i,H ω i^2)/2) ∂P) =
        ∫ ω, Real.exp (θ*A ω-θ^2*V ω/2) ∂P := by
  let S := fun ω => (A ω,H ω,V ω)
  let μ := P.map S
  let ν := Measure.pi (fun _ : ι => gaussianReal 0 v)
  have : IsFiniteMeasure μ := P.isFiniteMeasure_map S
  let f := fun p : (ℝ × (ι → ℝ) × ℝ) × (ι → ℝ) => Real.exp
    (θ*(p.1.1+∑ i,p.1.2.1 i*p.2 i)-θ^2*(p.1.2.2+(v : ℝ)*∑ i,p.1.2.1 i^2)/2)
  have hm : Measurable f := by fun_prop
  have hp : Integrable (fun p : ℝ × (ι → ℝ) × ℝ => Real.exp (θ*p.1-θ^2*p.2.2/2)) μ :=
    (integrable_map_measure (by fun_prop) hstate).mpr hprior
  have hfiber (p : ℝ × (ι → ℝ) × ℝ) : Integrable (fun x => f (p,x)) ν := by
    simp only [f,gaussian_vector_predictable_fiber_factor]
    exact (integrable_gaussianVectorCompensatedExp v θ p.2.1).const_mul _
  have hint (p : ℝ × (ι → ℝ) × ℝ) : (∫ x,f (p,x) ∂ν) = Real.exp (θ*p.1-θ^2*p.2.2/2) := by
    simp only [f,gaussian_vector_predictable_fiber_factor]
    rw [integral_const_mul,integral_gaussianVectorCompensatedExp,mul_one]
  have hprod : Integrable f (μ.prod ν) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).2
    refine ⟨ae_of_all _ hfiber,?_⟩
    convert hp using 1
    funext p
    simp only [f,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact hint p
  have hlaw : HasLaw (fun ω => (S ω,X ω)) (μ.prod ν) P :=
    hindep.hasLaw_prod ⟨hstate,rfl⟩ hX
  refine ⟨hlaw.integrable_fun_comp hprod,?_⟩
  have hi := hlaw.integral_comp hprod.aestronglyMeasurable
  change (∫ ω,f (S ω,X ω) ∂P) = ∫ p,f p ∂μ.prod ν at hi
  rw [hi,integral_prod _ hprod]
  simp_rw [hint]
  exact integral_map hstate (by fun_prop)

def predictableGaussianVectorSum {ι Ω : Type*} [Fintype ι] (X H : ℕ → Ω → ι → ℝ) : ℕ → Ω → ℝ
  | 0,_ => 0
  | k+1,ω => predictableGaussianVectorSum X H k ω+∑ i,H k ω i*X k ω i

def predictableGaussianVectorVariation {ι Ω : Type*} [Fintype ι]
    (v : ℕ → ℝ≥0) (H : ℕ → Ω → ι → ℝ) : ℕ → Ω → ℝ
  | 0,_ => 0
  | k+1,ω => predictableGaussianVectorVariation v H k ω+(v k : ℝ)*∑ i,H k ω i^2

lemma aemeasurable_predictableGaussianVectorSum {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) (X H : ℕ → Ω → ι → ℝ)
    (hX : ∀ k, AEMeasurable (X k) P) (hH : ∀ k, AEMeasurable (H k) P) (n : ℕ) :
    AEMeasurable (predictableGaussianVectorSum X H n) P := by
  induction n with
  | zero => exact aemeasurable_const
  | succ n ih =>
    exact ih.add (Finset.aemeasurable_fun_sum _ (fun i _ =>
      ((measurable_pi_apply i).comp_aemeasurable (hH n)).mul
        ((measurable_pi_apply i).comp_aemeasurable (hX n))))

lemma predictableGaussianVectorSum_eq_fin_sum {ι Ω : Type*} [Fintype ι]
    (X H : ℕ → Ω → ι → ℝ) (n : ℕ) (ω : Ω) :
    predictableGaussianVectorSum X H n ω = ∑ k : Fin n,∑ i,H k ω i*X k ω i := by
  have hr : predictableGaussianVectorSum X H n ω =
      ∑ k ∈ Finset.range n,∑ i,H k ω i*X k ω i := by
    induction n with
    | zero => simp [predictableGaussianVectorSum]
    | succ n ih => rw [predictableGaussianVectorSum,ih,Finset.sum_range_succ]
  rw [Fin.sum_univ_eq_sum_range (fun k => ∑ i,H k ω i*X k ω i)]
  exact hr

lemma predictableGaussianVectorVariation_eq_fin_sum {ι Ω : Type*} [Fintype ι]
    (v : ℕ → ℝ≥0) (H : ℕ → Ω → ι → ℝ) (n : ℕ) (ω : Ω) :
    predictableGaussianVectorVariation v H n ω = ∑ k : Fin n,(v k : ℝ)*∑ i,H k ω i^2 := by
  have hr : predictableGaussianVectorVariation v H n ω =
      ∑ k ∈ Finset.range n,(v k : ℝ)*∑ i,H k ω i^2 := by
    induction n with
    | zero => simp [predictableGaussianVectorVariation]
    | succ n ih => rw [predictableGaussianVectorVariation,ih,Finset.sum_range_succ]
  rw [Fin.sum_univ_eq_sum_range (fun k => (v k : ℝ)*∑ i,H k ω i^2)]
  exact hr

lemma aemeasurable_predictableGaussianVectorVariation {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) (v : ℕ → ℝ≥0) (H : ℕ → Ω → ι → ℝ)
    (hH : ∀ k, AEMeasurable (H k) P) (n : ℕ) :
    AEMeasurable (predictableGaussianVectorVariation v H n) P := by
  induction n with
  | zero => exact aemeasurable_const
  | succ n ih =>
    exact ih.add ((Finset.aemeasurable_fun_sum _ (fun i _ =>
      ((measurable_pi_apply i).comp_aemeasurable (hH n)).pow_const 2)).const_mul _)

theorem predictableGaussianVectorExponential_integral {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X H : ℕ → Ω → ι → ℝ) (v : ℕ → ℝ≥0)
    (hX : ∀ k, HasLaw (X k) (Measure.pi (fun _ : ι => gaussianReal 0 (v k))) P)
    (hH : ∀ k, AEMeasurable (H k) P)
    (hindep : ∀ k, IndepFun (fun ω => (predictableGaussianVectorSum X H k ω,H k ω,
      predictableGaussianVectorVariation v H k ω)) (X k) P) (θ : ℝ) (n : ℕ) :
    Integrable (fun ω => Real.exp (θ*predictableGaussianVectorSum X H n ω-
      θ^2*predictableGaussianVectorVariation v H n ω/2)) P ∧
      (∫ ω, Real.exp (θ*predictableGaussianVectorSum X H n ω-
        θ^2*predictableGaussianVectorVariation v H n ω/2) ∂P) = 1 := by
  induction n with
  | zero => simp only [predictableGaussianVectorSum,predictableGaussianVectorVariation,mul_zero,
      zero_div,sub_self,Real.exp_zero];exact ⟨integrable_const _,by simp⟩
  | succ n ih =>
    have hs := (aemeasurable_predictableGaussianVectorSum P X H (fun k => (hX k).aemeasurable) hH n).prodMk
      ((hH n).prodMk (aemeasurable_predictableGaussianVectorVariation P v H hH n))
    have h := independent_gaussian_vector_step_exponential P (v n) (X n) (H n)
      (predictableGaussianVectorSum X H n) (predictableGaussianVectorVariation v H n) θ hs
      (hX n) (hindep n) ih.1
    exact ⟨h.1,h.2.trans ih.2⟩

end SKConstants
