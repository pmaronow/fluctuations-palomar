module

public import SKConstants.TransportStrongConvex

/-!
# Sharp transport from the proved Gibbs infimal-convolution inequality

The scalar entropy and variational argument is adapted from OpenAI/math,
`lean/OAI/Probability/SKGap/Entropy/EntropyTransport.lean`, commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (Apache-2.0).
The coupling is constructed by the proved Hopf-duality theorem; no transport
inequality or coupling-cost bound is a hypothesis.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace SKConstants.Transport
open WeakHessianTransport
set_option backward.isDefEq.respectTransparency false

theorem entropy_fenchel {r : ℝ} (hr : 0 ≤ r) (v : ℝ) :
    r * v ≤ klFun r + exp v - 1 := by
  rcases hr.eq_or_lt with rfl | hr
  · simpa [klFun] using (exp_pos v).le
  · have h := mul_le_mul_of_nonneg_left (add_one_le_exp (v - log r)) hr.le
    rw [exp_sub, exp_log hr, mul_div_cancel₀ _ hr.ne'] at h
    unfold klFun
    nlinarith

theorem entropy_variational {α : Type*} [MeasurableSpace α]
    {P Q : Measure α} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hD : klDiv P Q ≠ ⊤) {f : α → ℝ} (hf : Integrable f P)
    (he : Integrable (fun x => exp (f x)) Q) :
    (∫ x, f x ∂P) ≤ (klDiv P Q).toReal + (∫ x, exp (f x) ∂Q) - 1 := by
  obtain ⟨hac, hllr⟩ := klDiv_ne_top_iff.mp hD
  have hk := (integrable_klFun_rnDeriv_iff hac).mpr hllr
  have hrf := (integrable_toReal_rnDeriv_mul_iff hac).mpr hf
  have hle := integral_mono hrf ((hk.add he).sub (integrable_const 1))
    (fun x => entropy_fenchel ENNReal.toReal_nonneg (f x))
  simp only [Pi.add_apply, Pi.sub_apply] at hle
  rw [integral_toReal_rnDeriv_mul hac,
    integral_sub (f := fun x => klFun (P.rnDeriv Q x).toReal + exp (f x))
      (g := fun _ => (1 : ℝ)) (hk.add he) (integrable_const 1),
    integral_add hk he, ← toReal_klDiv_eq_integral_klFun hac] at hle
  simpa using hle

theorem strongConvex_hopf_entropy_bound {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℝ ι → ℝ) (hUm : Measurable U)
    (hU : StrongConvexOn univ 1 U) [IsProbabilityMeasure (expPotentialLaw U)]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ]
    (hD : klDiv μ (expPotentialLaw U) ≠ ⊤)
    (f : EuclideanSpace ℝ ι →ᵇ ℝ) :
    (∫ x, hopfLax f 1 x ∂μ) - (∫ x, f x ∂expPotentialLaw U) ≤
      (klDiv μ (expPotentialLaw U)).toReal := by
  let ν := expPotentialLaw U
  let c := ∫ x, f x ∂ν
  let Q := boundedHopf f
  let g := Q - BoundedContinuousFunction.const _ c
  have hlog : log (mgf Q ν 1) ≤ c := strongConvex_hopf_log_mgf_le U hUm hU f
  have hpos : 0 < mgf Q ν 1 := mgf_pos (bounded_exp_integrable ν Q 1)
  have hex : mgf Q ν 1 ≤ exp c := by
    simpa only [exp_log hpos] using exp_le_exp.mpr hlog
  have he : Integrable (fun x => exp (g x)) ν := by
    simpa only [one_mul] using bounded_exp_integrable ν g 1
  have hZ : (∫ x, exp (g x) ∂ν) ≤ 1 := by
    have heq : (fun x => exp (g x)) = fun x => exp (-c) * exp (Q x) := by
      funext x
      change exp (Q x - c) = _
      rw [sub_eq_add_neg, exp_add, mul_comm]
    rw [heq, integral_const_mul]
    have hmgf : (∫ x, exp (Q x) ∂ν) = mgf Q ν 1 := by simp [mgf]
    rw [hmgf]
    exact (mul_le_mul_of_nonneg_left hex (exp_pos _).le).trans_eq
      (by rw [← exp_add]; simp)
  have hv := entropy_variational hD (g.integrable μ) he
  have hi : (∫ x, g x ∂μ) = (∫ x, hopfLax f 1 x ∂μ) - c := by
    change (∫ x, Q x - c ∂μ) = _
    rw [integral_sub (Q.integrable μ) (integrable_const c)]
    simp [Q]
  rw [hi] at hv
  change (∫ x, hopfLax f 1 x ∂μ) - c ≤ _
  linarith

/-- Every probability law admits an actual coupling to a one-strongly convex
Gibbs reference with squared Euclidean cost bounded by twice its KL divergence.
The infinite-entropy case is included. -/
theorem strongConvex_exists_coupling_cost_le_two_klDiv {ι : Type*} [Fintype ι]
    (U : EuclideanSpace ℝ ι → ℝ) (hUm : Measurable U)
    (hU : StrongConvexOn univ 1 U) [IsProbabilityMeasure (expPotentialLaw U)]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] :
    ∃ q : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι),
      IsProbabilityMeasure q ∧ q.map Prod.fst = μ ∧
      q.map Prod.snd = expPotentialLaw U ∧
      (∫⁻ p, edist p.1 p.2 ^ 2 ∂q) ≤ 2 * klDiv μ (expPotentialLaw U) := by
  by_cases hD : klDiv μ (expPotentialLaw U) = ⊤
  · refine ⟨μ.prod (expPotentialLaw U), inferInstance, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp [hD]
  · obtain ⟨q, hq, hfst, hsnd, hcost⟩ :=
      exists_proper_coupling_cost_of_hopf_bound μ (expPotentialLaw U)
        (2 * (klDiv μ (expPotentialLaw U)).toReal) (fun f _ => by
          simpa only [mul_div_cancel_left₀ _ (show (2 : ℝ) ≠ 0 by norm_num)] using
            strongConvex_hopf_entropy_bound U hUm hU μ hD f)
    refine ⟨q, hq, hfst, hsnd, ?_⟩
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal hD] using hcost

end SKConstants.Transport
