module

public import SKConstants.Completion.N13d.Variance
public import SKConstants.Completion.LM5.CompletionIntegrability
import Mathlib.Tactic

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace SKConstants.Completion.N13d
open GaussianProposal LC5 LM5

theorem completion_tail_of_variance_le {n k : ℕ}
    (N : ℝ) (hN : 0 < N) (c : Fin k → ℝ) (y : Fin n → ℝ)
    (V u : ℝ) (hV : 0 < V) (hu : 0 < u)
    (hvar : completionVariance N c y ≤ V) :
    (completionNoiseLaw n k).real {z | u ≤ |completionEnergy N c y z|} ≤
      2*Real.exp (-u^2/(2*V)) := by
  have hg := (completion_law N hN c y).hasGaussianLaw
  have hv := completion_variance N hN c y
  by_cases hz : completionVariance N c y = 0
  · have hae := ae_eq_integral_of_variance_eq_zero hg.memLp_two (hv.trans hz)
    simp only [completion_mean N hN c y] at hae
    have hevent : {z | u ≤ |completionEnergy N c y z|} =ᵐ[completionNoiseLaw n k]
        (∅ : Set _) := by
      filter_upwards [hae] with z hz
      simp [hz, hu.not_ge]
    rw [measureReal_congr hevent, measureReal_empty]
    positivity
  · have hpos : 0 < completionVariance N c y := lt_of_le_of_ne
      (by unfold completionVariance; positivity) (Ne.symm hz)
    refine (gaussian_centered_two_sided_tail _ _ hg (completion_mean N hN c y)
      (completionVariance N c y) u hpos hu hv).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    have hratio : u^2/(2*V) ≤ u^2/(2*completionVariance N c y) :=
      div_le_div_of_nonneg_left (sq_nonneg u) (by positivity) (by linarith)
    convert neg_le_neg hratio using 1 <;> ring

theorem completion_tail_sharp {n k : ℕ} (N : ℝ) (hN : 0 < N)
    (c s : EuclideanSpace ℝ (Fin k)) (y : Fin n → ℝ) (M τ p u : ℝ)
    (hM : 0 < M) (hτ : 0 ≤ τ) (hp : 0 ≤ p) (hu : 0 < u)
    (hc : ‖c‖ ≤ 1) (hclose : ‖c-s‖ ≤ τ)
    (hscoord : ∀ j, (s j)^2 ≤ M) (hs : ‖s‖^2 = 1-p)
    (hy : N⁻¹*dot y y = 1-∑ j, (c j)^2) :
    (completionNoiseLaw n k).real
      {z | u ≤ |completionEnergy N (fun j => c j) y z|} ≤
      2*Real.exp (-N*u^2/(2*(M+5*τ^2+p^2))) := by
  have hB : 0 < M+5*τ^2+p^2 := by positivity
  have h := completion_tail_of_variance_le N hN (fun j => c j) y
    (N⁻¹*(M+5*τ^2+p^2)) u (by positivity) hu
    (completionVariance_sharp_le N hN c s y M τ p hM.le hτ hp hc hclose hscoord hs hy)
  convert h using 1
  congr 2
  field_simp

theorem completionEnergy_product_tail_on {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsProbabilityMeasure μ] {n k : ℕ}
    (N : ℝ) (hN : 0 < N) (c : U → Fin k → ℝ) (y : U → Fin n → ℝ)
    (hc : Measurable c) (hy : Measurable y) (E : Set U) (hE : MeasurableSet E)
    (V u : ℝ) (hV : 0 < V) (hu : 0 < u)
    (hvar : ∀ a ∈ E, completionVariance N (c a) (y a) ≤ V) :
    (μ.prod (completionNoiseLaw n k)).real
      {z | z.1 ∈ E ∧ u ≤ |completionEnergy N (c z.1) (y z.1) z.2|} ≤
      2*Real.exp (-u^2/(2*V)) := by
  have hm : MeasurableSet {z : U × _ |
      z.1 ∈ E ∧ u ≤ |completionEnergy N (c z.1) (y z.1) z.2|} :=
    (hE.preimage measurable_fst).inter
      (measurableSet_le measurable_const (measurable_completionEnergy N c y hc hy).abs)
  have hsection (a : U) : (completionNoiseLaw n k)
      {z | a ∈ E ∧ u ≤ |completionEnergy N (c a) (y a) z|} ≤
        ENNReal.ofReal (2*Real.exp (-u^2/(2*V))) := by
    by_cases ha : a ∈ E
    · simp only [ha, true_and]
      rw [← ofReal_measureReal]
      exact ENNReal.ofReal_le_ofReal
        (completion_tail_of_variance_le N hN _ _ V u hV hu (hvar a ha))
    · simp [ha]
  have hle : (μ.prod (completionNoiseLaw n k))
      {z | z.1 ∈ E ∧ u ≤ |completionEnergy N (c z.1) (y z.1) z.2|} ≤
        ENNReal.ofReal (2*Real.exp (-u^2/(2*V))) := by
    rw [Measure.prod_apply hm]
    calc
      _ ≤ ∫⁻ _a, ENNReal.ofReal (2*Real.exp (-u^2/(2*V))) ∂μ :=
        lintegral_mono hsection
      _ = _ := by simp
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hle).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

end SKConstants.Completion.N13d
