module

public import SKConstants.Completion.LGram.Population
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators RealInnerProductSpace
namespace SKConstants.Completion.LGram
open SKConstantsOAI.ZeroTemperatureSK
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem momentVector_norm_le_one {Ξ : Type*} [MeasurableSpace Ξ] {k : ℕ}
    (μ : Measure Ξ) (X : Ξ → EuclideanSpace ℝ (Fin k)) (S : Ξ → ℝ)
    (hM : ∀ a : EuclideanSpace ℝ (Fin k), MemLp (fun w => inner (𝕜 := ℝ) (X w) a) 2 μ)
    (hI : ∀ a : EuclideanSpace ℝ (Fin k),
      (∫ w, (inner (𝕜 := ℝ) (X w) a)^2 ∂μ) = ‖a‖^2)
    (hS : MemLp S 2 μ) (hS1 : (∫ w, S w^2 ∂μ) ≤ 1) :
    ‖WithLp.toLp 2 (fun i => ∫ w, X w i * S w ∂μ)‖ ≤ 1 := by
  let a := WithLp.toLp 2 (fun i => ∫ w, X w i * S w ∂μ)
  let Y := fun w => inner (𝕜 := ℝ) (X w) a
  have hXi (i : Fin k) : MemLp (fun w => X w i) 2 μ := by
    simpa only [EuclideanSpace.inner_single_right, RCLike.conj_to_real, one_mul] using
      hM (EuclideanSpace.single i 1)
  have hInt (i : Fin k) : Integrable (fun w => X w i * S w) μ := (hXi i).integrable_mul hS
  have he (w : Ξ) : Y w * S w = ∑ i, a i * (X w i * S w) := by
    simp [Y, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Finset.sum_mul, mul_assoc]
  have hYS : Integrable (fun w => Y w * S w) μ := (hM a).integrable_mul hS
  have hEY : (∫ w, Y w * S w ∂μ) = ‖a‖^2 := by
    simp_rw [he]
    rw [integral_finsetSum _ (fun i _ => (hInt i).const_mul (a i))]
    simp only [integral_const_mul]
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    change (a i)*(a i) = (a i)^2
    ring
  have hY2 : Integrable (fun w => Y w^2) μ := (hM a).integrable_sq
  have hS2 : Integrable (fun w => S w^2) μ := hS.integrable_sq
  have hpos : 0 ≤ ∫ w, (Y w^2+S w^2)-2*(Y w*S w) ∂μ :=
    integral_nonneg fun w => by
      change (0:ℝ) ≤ (Y w^2+S w^2)-2*(Y w*S w)
      nlinarith [sq_nonneg (Y w-S w)]
  have hsub := integral_sub (hY2.add hS2) (hYS.const_mul 2)
  have hadd := integral_add hY2 hS2
  simp only [Pi.add_apply] at hsub hadd
  rw [hsub, hadd, integral_const_mul, hEY, hI a] at hpos
  change ‖a‖ ≤ 1
  nlinarith [norm_nonneg a]

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
local instance populationNorms_primary_probability (W : BrownianSystem Ω) : IsProbabilityMeasure W.law := W.isProbability
local instance populationNorms_aux_probability (Z : BrownianSystem A) : IsProbabilityMeasure Z.law := Z.isProbability

theorem populationTargetSpin_norm_le_one (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (ht : StrictMono t)
    (g : ℕ → ℝ≥0) (k : ℕ) (H : ℝ≥0) :
    ‖populationTargetSpin W Z β hβ t g k H‖ ≤ 1 := by
  let μ := actualParisiFullQuerySpinLaw W Z β H
  let X := fun u : (Bool × Ω) × A => actualParisiNormalizedPosteriorRow W β t k u.1.2
  let S := fun u : (Bool × Ω) × A => scalarHiddenSign u.1.1
  have hM (a : EuclideanSpace ℝ (Fin k)) : MemLp (fun u => inner (𝕜 := ℝ) (X u) a) 2 μ := by
    have h := HasSubgaussianMGF.of_map
      (X:=fun w => inner (𝕜 := ℝ) (actualParisiNormalizedPosteriorRow W β t k w) a)
      (actualParisiFullQuerySpinLaw_path_hasLaw W Z β H).aemeasurable
      (by rw [(actualParisiFullQuerySpinLaw_path_hasLaw W Z β H).map_eq]
          exact normalizedPosteriorRow_hasSubgaussianMGF W β hβ t ht k a)
    exact h.memLp 2
  have hI (a : EuclideanSpace ℝ (Fin k)) : (∫ u, (inner (𝕜 := ℝ) (X u) a)^2 ∂μ) = ‖a‖^2 := by
    have hm : Measurable (fun w => (inner (𝕜 := ℝ) (actualParisiNormalizedPosteriorRow W β t k w) a)^2) := by
      exact (((measurable_actualParisiNormalizedPosteriorRow W β t k).inner_const (c:=a)).pow_const 2)
    exact ((actualParisiFullQuerySpinLaw_path_hasLaw W Z β H).integral_comp hm.aestronglyMeasurable).trans
      (actualParisiNormalizedPosteriorRow_secondMoment W β hβ t ht k a)
  have hS : MemLp S 2 μ := by
    apply MemLp.of_bound ((measurable_of_finite scalarHiddenSign).comp
      (measurable_fst.comp measurable_fst)).aestronglyMeasurable 1
    exact ae_of_all _ (fun u => (scalarHiddenSign_norm_one u.1.1).le)
  have hS1 : (∫ u, S u^2 ∂μ) ≤ 1 := by
    have he (u : (Bool × Ω) × A) : S u^2 = 1 := by cases h : u.1.1 <;> simp [S, scalarHiddenSign, h]
    simp_rw [he]
    simp [μ]
  simpa only [populationTargetSpin, mixedPopulation, populationGram, mixedRow_posterior,
    mixedRow_spin] using momentVector_norm_le_one μ X S hM hI hS hS1

theorem populationQuerySpin_norm_le_one (W : BrownianSystem Ω) (Z : BrownianSystem A)
    (β : ℝ) (hβ : 1 < β) (t : ℕ → ℝ≥0) (g : ℕ → ℝ≥0) (hg : StrictMono g)
    (k : ℕ) (H : ℝ≥0) : ‖populationQuerySpin W Z β hβ t g k H‖ ≤ 1 := by
  let Q := actualParisiQueryBrownianSystem W Z β hβ
  let μ := actualParisiFullQuerySpinLaw W Z β H
  let X := fun u : (Bool × Ω) × A => scalarNormalizedBrownianRow (d:=k) Q.B g (u.1.2,u.2)
  let S := fun u : (Bool × Ω) × A => scalarHiddenSign u.1.1
  have hM (a : EuclideanSpace ℝ (Fin k)) : MemLp (fun u => inner (𝕜 := ℝ) (X u) a) 2 μ := by
    have h := HasSubgaussianMGF.of_map
      (X:=fun w => inner (𝕜 := ℝ) (scalarNormalizedBrownianRow (d:=k) Q.B g w) a)
      (actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).aemeasurable
      (by rw [(actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).map_eq]
          exact scalarNormalizedBrownianRow_linearForm_hasSubgaussianMGF _ _ Q.brownian.toIsPreBrownianReal g hg a)
    exact h.memLp 2
  have hI (a : EuclideanSpace ℝ (Fin k)) : (∫ u, (inner (𝕜 := ℝ) (X u) a)^2 ∂μ) = ‖a‖^2 := by
    have hm : Measurable (fun w => (inner (𝕜 := ℝ) (scalarNormalizedBrownianRow (d:=k) Q.B g w) a)^2) :=
      (((measurable_scalarNormalizedBrownianRow Q.B Q.measurable g).inner_const (c:=a)).pow_const 2)
    exact ((actualParisiFullQuerySpinLaw_drivers_hasLaw W Z β H).integral_comp hm.aestronglyMeasurable).trans
      (scalarNormalizedBrownianRow_linearForm_secondMoment _ _ Q.brownian.toIsPreBrownianReal g hg a)
  have hS : MemLp S 2 μ := by
    apply MemLp.of_bound ((measurable_of_finite scalarHiddenSign).comp
      (measurable_fst.comp measurable_fst)).aestronglyMeasurable 1
    exact ae_of_all _ (fun u => (scalarHiddenSign_norm_one u.1.1).le)
  have hS1 : (∫ u, S u^2 ∂μ) ≤ 1 := by
    have he (u : (Bool × Ω) × A) : S u^2 = 1 := by cases h : u.1.1 <;> simp [S, scalarHiddenSign, h]
    simp_rw [he]
    simp [μ]
  simpa only [populationQuerySpin, mixedPopulation, populationGram, mixedRow_query,
    mixedRow_spin] using momentVector_norm_le_one μ X S hM hI hS hS1

end SKConstants.Completion.LGram
