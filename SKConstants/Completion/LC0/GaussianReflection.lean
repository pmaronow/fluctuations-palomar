module
public import SKConstants.ScalarWeightedGaussianFamilies

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
namespace SKConstants.M1
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def reflect (a b : ι → ℝ) (p : (ι → ℝ) × (ι → ℝ)) : (ι → ℝ) × (ι → ℝ) :=
  (fun i => a i * p.1 i + b i * p.2 i,
   fun i => b i * p.1 i - a i * p.2 i)

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_reflect (a b : ι → ℝ) : Measurable (reflect a b) := by
  apply Measurable.prodMk
  · exact Measurable.of_eval fun i =>
      (((measurable_pi_apply i).comp measurable_fst).const_mul _).add
        (((measurable_pi_apply i).comp measurable_snd).const_mul _)
  · exact Measurable.of_eval fun i =>
      (((measurable_pi_apply i).comp measurable_fst).const_mul _).sub
        (((measurable_pi_apply i).comp measurable_snd).const_mul _)

omit [Fintype ι] [DecidableEq ι] in
theorem reflect_involutive (a b : ι → ℝ) (hab : ∀ i, (a i)^2+(b i)^2=1) :
    Function.Involutive (reflect a b) := by
  intro p
  apply Prod.ext
  · funext i
    change a i * (a i * p.1 i + b i * p.2 i) + b i * (b i * p.1 i - a i * p.2 i) = p.1 i
    calc
      _ = ((a i)^2+(b i)^2)*p.1 i := by ring
      _ = _ := by rw [hab i, one_mul]
  · funext i
    change b i * (a i * p.1 i + b i * p.2 i) - a i * (b i * p.1 i - a i * p.2 i) = p.2 i
    calc
      _ = ((a i)^2+(b i)^2)*p.2 i := by ring
      _ = _ := by rw [hab i, one_mul]

def reflectionCoefficients (a b : ι → ℝ) : (ι ⊕ ι) → (ι ⊕ ι) → ℝ
  | .inl i, .inl j => if j = i then a i else 0
  | .inl i, .inr j => if j = i then b i else 0
  | .inr i, .inl j => if j = i then b i else 0
  | .inr i, .inr j => if j = i then -a i else 0

theorem reflectionCoefficients_covariance (v : ι → ℝ≥0) (a b : ι → ℝ)
    (hab : ∀ i, (a i)^2+(b i)^2=1) (k l : ι ⊕ ι) :
    (∑ j, reflectionCoefficients a b k j * reflectionCoefficients a b l j *
      ((Sum.elim v v j : ℝ≥0) : ℝ)) = if k=l then ((Sum.elim v v k : ℝ≥0) : ℝ) else 0 := by
  cases k with
  | inl i =>
    cases l with
    | inl j =>
      by_cases hij : i=j
      · subst j
        simp [reflectionCoefficients, Fintype.sum_sum_type, ← sq]
        nlinarith [congrArg (fun x : ℝ => x * (v i : ℝ)) (hab i)]
      · simp [reflectionCoefficients, Fintype.sum_sum_type, mul_ite, ite_mul, hij, Ne.symm hij]
    | inr j =>
      by_cases hij : i=j
      · subst j
        simp [reflectionCoefficients, Fintype.sum_sum_type, mul_ite, ite_mul]
        ring
      · simp [reflectionCoefficients, Fintype.sum_sum_type, mul_ite, ite_mul, Ne.symm hij]
  | inr i =>
    cases l with
    | inl j =>
      by_cases hij : i=j
      · subst j
        simp [reflectionCoefficients, Fintype.sum_sum_type, mul_ite, ite_mul]
        ring
      · simp [reflectionCoefficients, Fintype.sum_sum_type, mul_ite, ite_mul, Ne.symm hij]
    | inr j =>
      by_cases hij : i=j
      · subst j
        simp [reflectionCoefficients, Fintype.sum_sum_type, ← sq]
        nlinarith [congrArg (fun x : ℝ => x * (v i : ℝ)) (hab i)]
      · simp [reflectionCoefficients, Fintype.sum_sum_type, mul_ite, ite_mul, hij, Ne.symm hij]

theorem reflectionCoefficients_apply (a b : ι → ℝ) (z : (ι ⊕ ι) → ℝ) :
    (fun k => ∑ j, reflectionCoefficients a b k j * z j) =
      Sum.elim (fun i => a i * z (.inl i) + b i * z (.inr i))
        (fun i => b i * z (.inl i) - a i * z (.inr i)) := by
  funext k
  cases k <;> simp [reflectionCoefficients, Fintype.sum_sum_type, ite_mul, sub_eq_add_neg]

theorem gaussianReflection_law (v : ι → ℝ≥0) (a b : ι → ℝ)
    (hab : ∀ i, (a i)^2+(b i)^2=1) :
    ((Measure.pi (fun i => gaussianReal 0 (v i))).prod
      (Measure.pi (fun i => gaussianReal 0 (v i)))).map (reflect a b) =
      (Measure.pi (fun i => gaussianReal 0 (v i))).prod
        (Measure.pi (fun i => gaussianReal 0 (v i))) := by
  let ν : Measure ((ι ⊕ ι) → ℝ) :=
    Measure.pi (fun i => gaussianReal 0 (Sum.elim v v i))
  have hcoord (i : ι ⊕ ι) : HasLaw (fun z : (ι ⊕ ι) → ℝ => z i)
      (gaussianReal 0 (Sum.elim v v i)) ν :=
    (measurePreserving_eval (fun i => gaussianReal 0 (Sum.elim v v i)) i).hasLaw
  have hind : iIndepFun (fun i (z : (ι ⊕ ι) → ℝ) => z i) ν :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hl := scalarIndependentGaussian_linearForms_hasLaw ν _ (Sum.elim v v) hcoord hind
    (reflectionCoefficients a b) (fun k l hkl => by
      rw [reflectionCoefficients_covariance v a b hab k l, ite_eq_right hkl])
  have hvar (k : ι ⊕ ι) :
      (∑ j, (reflectionCoefficients a b k j)^2 * ((Sum.elim v v j : ℝ≥0) : ℝ)).toNNReal =
        Sum.elim v v k := by
    have hc := reflectionCoefficients_covariance v a b hab k k
    simpa only [sq, ite_true, Real.toNNReal_coe] using congrArg Real.toNNReal hc
  simp only [hvar] at hl
  let E : ((ι ⊕ ι) → ℝ) → (ι → ℝ) × (ι → ℝ) :=
    fun z => (fun i => z (.inl i),fun i => z (.inr i))
  have hE : Measurable E :=
    (Measurable.of_eval fun i => measurable_pi_apply (Sum.inl i : ι ⊕ ι)).prodMk
      (Measurable.of_eval fun i => measurable_pi_apply (Sum.inr i : ι ⊕ ι))
  have hprod : ν.map E = (Measure.pi (fun i => gaussianReal 0 (v i))).prod
      (Measure.pi (fun i => gaussianReal 0 (v i))) :=
    (measurePreserving_sumPiEquivProdPi (fun i : ι ⊕ ι => gaussianReal 0 (Sum.elim v v i))).map_eq
  rw [← hprod, Measure.map_map (measurable_reflect a b) hE]
  have hcomp : reflect a b ∘ E = E ∘ (fun z k => ∑ j, reflectionCoefficients a b k j*z j) := by
    funext z
    dsimp only [Function.comp_apply]
    rw [reflectionCoefficients_apply]
    rfl
  have hLin : Measurable (fun (z : (ι ⊕ ι) → ℝ) k => ∑ j, reflectionCoefficients a b k j*z j) := by
    fun_prop
  rw [hcomp, ← Measure.map_map hE hLin, hl.map_eq]

theorem gaussianReflection_graph_law (v : ι → ℝ≥0) (a b : ι → ℝ)
    (hab : ∀ i, (a i)^2+(b i)^2=1) :
    let μ := (Measure.pi (fun i => gaussianReal 0 (v i))).prod
      (Measure.pi (fun i => gaussianReal 0 (v i)))
    μ.map (fun p => (p,reflect a b p)) = μ.map (fun p => (reflect a b p,p)) := by
  dsimp only
  let μ := (Measure.pi (fun i => gaussianReal 0 (v i))).prod
    (Measure.pi (fun i => gaussianReal 0 (v i)))
  change μ.map _ = μ.map _
  have hl : μ.map (reflect a b) = μ := gaussianReflection_law v a b hab
  calc
    _ = (μ.map (reflect a b)).map (fun p => (reflect a b p,p)) := by
      rw [Measure.map_map (show Measurable (fun p => (reflect a b p,p)) from
        (measurable_reflect a b).prodMk measurable_id)
        (measurable_reflect a b)]
      congr 1
      funext p
      exact (congrArg (fun x => (x,reflect a b p)) (reflect_involutive a b hab p)).symm
    _ = _ := by rw [hl]

end SKConstants.M1
