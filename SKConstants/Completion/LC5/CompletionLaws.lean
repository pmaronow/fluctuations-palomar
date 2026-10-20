module

public import SKConstants.GaussianProposalSKNormalization
public import SKConstants.GaussianHamiltonian
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace Matrix ENNReal
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.Completion.LC5
open GaussianProposal

def completionNoiseLaw (n k : ℕ) :
    Measure (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin n × Fin n)) :=
  (primitiveGaussian (Fin k)).prod (primitiveGaussian (Fin n × Fin n))

instance completionNoiseLaw_probability (n k : ℕ) : IsProbabilityMeasure (completionNoiseLaw n k) := by
  unfold completionNoiseLaw
  infer_instance

def completionEnergy {n k : ℕ} (N : ℝ) (c : Fin k → ℝ) (y : Fin n → ℝ)
    (z : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin n × Fin n)) : ℝ :=
  discardedDiagonalEnergy (2*skSigma N) c z.1 +
    quadraticEnergy N y (goeMatrix (skSigma N) z.2)

def completionVariance {n k : ℕ} (N : ℝ) (c : Fin k → ℝ) (y : Fin n → ℝ) : ℝ :=
  (1/2 : ℝ)*N⁻¹*((∑ j, c j^4) + (N⁻¹*dot y y)^2)

theorem diagonal_gaussian {k : ℕ} (N : ℝ) (c : Fin k → ℝ) :
    HasGaussianLaw (discardedDiagonalEnergy (2*skSigma N) c) (primitiveGaussian (Fin k)) :=
  linearForm_gaussian _

theorem residual_gaussian {n : ℕ} (N : ℝ) (y : Fin n → ℝ) :
    HasGaussianLaw (fun z => quadraticEnergy N y (goeMatrix (skSigma N) z))
      (primitiveGaussian (Fin n × Fin n)) := by
  have h := (goeBilinear_gaussian (skSigma N) y y).map_fun
    (((1/2 : ℝ)*N⁻¹) • ContinuousLinearMap.id ℝ ℝ)
  simpa only [quadraticEnergy_goe, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul] using h

theorem diagonal_variance {k : ℕ} (N : ℝ) (hN : 0 < N) (c : Fin k → ℝ) :
    Var[discardedDiagonalEnergy (2*skSigma N) c; primitiveGaussian (Fin k)] =
      (1/2 : ℝ)*N⁻¹*∑ j, c j^4 := by
  rw [discardedDiagonal_energy_variance]
  have hσ : skSigma N^2 = (1/2 : ℝ)*N⁻¹ := by nlinarith [skSigma_offVariance N hN]
  calc
    _ = skSigma N^2*(∑ j, c j^4) := by ring
    _ = _ := by rw [hσ]

theorem residual_variance {n : ℕ} (N : ℝ) (hN : 0 < N) (y : Fin n → ℝ) :
    Var[fun z => quadraticEnergy N y (goeMatrix (skSigma N) z);
      primitiveGaussian (Fin n × Fin n)] = (1/2 : ℝ)*N⁻¹*(N⁻¹*dot y y)^2 := by
  rw [residualGOE_energy_variance]
  have hσ : skSigma N^2 = (1/2 : ℝ)*N⁻¹ := by nlinarith [skSigma_offVariance N hN]
  rw [hσ]
  ring

theorem diagonal_law {k : ℕ} (N : ℝ) (hN : 0 < N) (c : Fin k → ℝ) :
    HasLaw (discardedDiagonalEnergy (2*skSigma N) c)
      (gaussianReal 0 (((1/2 : ℝ)*N⁻¹*∑ j, c j^4).toNNReal)) (primitiveGaussian (Fin k)) := by
  refine ⟨(diagonal_gaussian N c).aemeasurable, ?_⟩
  simpa only [discardedDiagonal_energy_mean, diagonal_variance N hN c] using
    (diagonal_gaussian N c).map_eq_gaussianReal

theorem residual_law {n : ℕ} (N : ℝ) (hN : 0 < N) (y : Fin n → ℝ) :
    HasLaw (fun z => quadraticEnergy N y (goeMatrix (skSigma N) z))
      (gaussianReal 0 (((1/2 : ℝ)*N⁻¹*(N⁻¹*dot y y)^2).toNNReal))
      (primitiveGaussian (Fin n × Fin n)) := by
  refine ⟨(residual_gaussian N y).aemeasurable, ?_⟩
  simpa only [residualGOE_energy_mean, residual_variance N hN y] using
    (residual_gaussian N y).map_eq_gaussianReal

theorem completion_independent {n k : ℕ} (N : ℝ) (c : Fin k → ℝ) (y : Fin n → ℝ) :
    IndepFun (fun z => discardedDiagonalEnergy (2*skSigma N) c z.1)
      (fun z => quadraticEnergy N y (goeMatrix (skSigma N) z.2)) (completionNoiseLaw n k) := by
  unfold completionNoiseLaw
  apply indepFun_prod (X := discardedDiagonalEnergy (2*skSigma N) c)
    (Y := fun z => quadraticEnergy N y (goeMatrix (skSigma N) z))
    (μ := primitiveGaussian (Fin k)) (ν := primitiveGaussian (Fin n × Fin n))
  · unfold discardedDiagonalEnergy linearForm
    fun_prop
  · simp only [quadraticEnergy_goe, goeBilinear]
    simpa only [linearFormCLM_apply] using ((linearFormCLM
      (fun p : Fin n × Fin n => skSigma N*(y p.1*y p.2+y p.2*y p.1))).measurable).const_mul
        ((1/2 : ℝ)*N⁻¹)

theorem completion_law {n k : ℕ} (N : ℝ) (hN : 0 < N) (c : Fin k → ℝ) (y : Fin n → ℝ) :
    HasLaw (completionEnergy N c y) (gaussianReal 0 (completionVariance N c y).toNNReal)
      (completionNoiseLaw n k) := by
  have hD := (diagonal_law N hN c).comp
    (measurePreserving_fst (μ := primitiveGaussian (Fin k))
      (ν := primitiveGaussian (Fin n × Fin n))).hasLaw
  have hR := (residual_law N hN y).comp
    (measurePreserving_snd (μ := primitiveGaussian (Fin k))
      (ν := primitiveGaussian (Fin n × Fin n))).hasLaw
  have hd : 0 ≤ (1/2 : ℝ)*N⁻¹*∑ j, c j^4 := by positivity
  have hr : 0 ≤ (1/2 : ℝ)*N⁻¹*(N⁻¹*dot y y)^2 := by positivity
  have hvar : ((1/2 : ℝ)*N⁻¹*∑ j, c j^4).toNNReal +
      ((1/2 : ℝ)*N⁻¹*(N⁻¹*dot y y)^2).toNNReal = (completionVariance N c y).toNNReal := by
    rw [← Real.toNNReal_add hd hr]
    congr 1
    unfold completionVariance
    ring
  refine ⟨hD.aemeasurable.add hR.aemeasurable, ?_⟩
  have h := gaussianReal_add_gaussianReal_of_indepFun (completion_independent N c y) hD hR
  unfold completionEnergy
  simpa only [zero_add, hvar, Pi.add_def] using h

theorem completion_mean {n k : ℕ} (N : ℝ) (hN : 0 < N) (c : Fin k → ℝ) (y : Fin n → ℝ) :
    ∫ z, completionEnergy N c y z ∂completionNoiseLaw n k = 0 := by
  have h := (completion_law N hN c y).integral_eq
  simpa using h

theorem completion_variance {n k : ℕ} (N : ℝ) (hN : 0 < N) (c : Fin k → ℝ) (y : Fin n → ℝ) :
    Var[completionEnergy N c y; completionNoiseLaw n k] = completionVariance N c y := by
  rw [(completion_law N hN c y).variance_eq, variance_id_gaussianReal]
  exact Real.coe_toNNReal _ (show 0 ≤ completionVariance N c y by
    unfold completionVariance
    positivity)

theorem completionVariance_le {n k : ℕ} (N : ℝ) (hN : 0 < N) (c : Fin k → ℝ) (y : Fin n → ℝ)
    (hc : (∑ j, c j^2) ≤ 1) (hy : N⁻¹*dot y y = 1-∑ j, c j^2) :
    completionVariance N c y ≤ (1/2 : ℝ)*N⁻¹ := by
  have hA : 0 ≤ ∑ j, c j^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfourth : (∑ j, c j^4) ≤ (∑ j, c j^2)^2 := by
    have h := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (f := fun j => c j^2) (fun j _ => sq_nonneg (c j))
    simpa only [← pow_mul] using h
  unfold completionVariance
  rw [hy]
  have h : (∑ j, c j^4) + (1-∑ j, c j^2)^2 ≤ 1 := by nlinarith
  simpa using mul_le_mul_of_nonneg_left h (show 0 ≤ (1/2 : ℝ)*N⁻¹ by positivity)

theorem completion_tail {n k : ℕ} (N : ℝ) (hN : 0 < N) (c : Fin k → ℝ) (y : Fin n → ℝ)
    (hc : (∑ j, c j^2) ≤ 1) (hy : N⁻¹*dot y y = 1-∑ j, c j^2)
    (u : ℝ) (hu : 0 < u) :
    (completionNoiseLaw n k).real {z | u ≤ |completionEnergy N c y z|} ≤
      2*Real.exp (-N*u^2) := by
  have hg := (completion_law N hN c y).hasGaussianLaw
  have hv := completion_variance N hN c y
  have hbound := completionVariance_le N hN c y hc hy
  by_cases hz : completionVariance N c y = 0
  · have hae := ae_eq_integral_of_variance_eq_zero hg.memLp_two (hv.trans hz)
    simp only [completion_mean N hN c y] at hae
    have hevent : {z | u ≤ |completionEnergy N c y z|} =ᵐ[completionNoiseLaw n k] (∅ : Set _) := by
      filter_upwards [hae] with z hz
      simp [hz, hu.not_ge]
    rw [measureReal_congr hevent, measureReal_empty]
    positivity
  · have hpos : 0 < completionVariance N c y := lt_of_le_of_ne
      (by unfold completionVariance; positivity) (Ne.symm hz)
    have ht := gaussian_centered_two_sided_tail _ _ hg (completion_mean N hN c y)
      (completionVariance N c y) u hpos hu hv
    apply ht.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hbound hN.le
    have hi : N⁻¹*N = 1 := inv_mul_cancel₀ hN.ne'
    have hNV : N*(2*completionVariance N c y) ≤ 1 := by nlinarith
    have hratio : N*u^2 ≤ u^2/(2*completionVariance N c y) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hNV (sq_nonneg u)]
    convert neg_le_neg hratio using 1 <;> ring

theorem transcript_completion_centered_test {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] {n k : ℕ} (N : ℝ) (hN : 0 < N)
    (c : Ω → Fin k → ℝ) (y : Ω → Fin n → ℝ) (φ : Ω → ℝ)
    (hint : Integrable (fun z : Ω × _ => φ z.1*completionEnergy N (c z.1) (y z.1) z.2)
      (μ.prod (completionNoiseLaw n k))) :
    ∫ z, φ z.1*completionEnergy N (c z.1) (y z.1) z.2 ∂μ.prod (completionNoiseLaw n k) = 0 := by
  rw [integral_prod _ hint]
  simp only [integral_const_mul, completion_mean N hN, mul_zero, integral_zero]

theorem linked_completion_product {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (L : Ω → ℝ≥0∞) (hL : Measurable L) (n k : ℕ) :
    (μ.prod (completionNoiseLaw n k)).withDensity (fun z => L z.1) =
      (μ.withDensity L).prod (completionNoiseLaw n k) :=
  (prod_withDensity_left hL).symm

theorem linked_completion_centered_test {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (L : Ω → ℝ≥0∞) (hL : Measurable L)
    [SFinite (μ.withDensity L)] {n k : ℕ} (N : ℝ) (hN : 0 < N)
    (c : Ω → Fin k → ℝ) (y : Ω → Fin n → ℝ) (φ : Ω → ℝ)
    (hint : Integrable (fun z : Ω × _ => φ z.1*completionEnergy N (c z.1) (y z.1) z.2)
      ((μ.prod (completionNoiseLaw n k)).withDensity (fun z => L z.1))) :
    ∫ z, φ z.1*completionEnergy N (c z.1) (y z.1) z.2
      ∂(μ.prod (completionNoiseLaw n k)).withDensity (fun z => L z.1) = 0 := by
  rw [linked_completion_product μ L hL] at hint ⊢
  exact transcript_completion_centered_test (μ.withDensity L) N hN c y φ hint

end SKConstants.Completion.LC5
