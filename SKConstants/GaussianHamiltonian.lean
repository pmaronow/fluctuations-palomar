module

public import SKConstants.SKModel
public import SKConstants.GibbsComparison
public import SKConstants.ConcentrationMGF
public import Mathlib.Probability.Moments.Variance

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical

namespace SKConstants

theorem gaussian_centered_two_sided_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : HasGaussianLaw X μ) (hmean : ∫ ω, X ω ∂μ = 0)
    (V u : ℝ) (hV : 0 < V) (hu : 0 < u) (hvariance : Var[X; μ] = V) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * Real.exp (-u ^ 2 / (2 * V)) := by
  have hlaw : HasLaw X (gaussianReal 0 V.toNNReal) μ := by
    refine ⟨hX.aemeasurable, ?_⟩
    simpa only [hmean, hvariance] using hX.map_eq_gaussianReal
  have hlocal : Concentration.LocalQuadraticMGF X μ (V / 2) (u / V) := by
    constructor
    · intro t _
      simpa only [Function.comp_def] using
        hlaw.integrable_comp (integrable_exp_mul_gaussianReal t)
    · intro t _
      rw [mgf_gaussianReal hlaw, Real.toNNReal_of_nonneg hV.le]
      simp only [NNReal.coe_mk, zero_mul, zero_add]
      apply le_of_eq
      congr 1
      ring
  have h := Concentration.localQuadraticMGF_two_sided hlocal
    (by positivity) (by positivity) hu
  have heq : min (u ^ 2 / (4 * (V / 2))) ((u / V) * u / 2) =
      u ^ 2 / (2 * V) := by
    have ha : u ^ 2 / (4 * (V / 2)) = u ^ 2 / (2 * V) := by ring
    have hb : (u / V) * u / 2 = u ^ 2 / (2 * V) := by ring
    rw [ha, hb, min_self]
  rw [heq] at h
  simpa only [neg_div] using h

@[expose] def goeSpinHamiltonian {n : ℕ} (sigma : ℝ) (x : Spin n)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) : ℝ :=
  quadraticHamiltonian (GaussianProposal.goeMatrix sigma z) x

theorem goeSpinHamiltonian_eq_half_bilinear {n : ℕ} (sigma : ℝ) (x : Spin n) :
    goeSpinHamiltonian sigma x = fun z ↦ (1 / 2 : ℝ) *
      GaussianProposal.goeBilinear sigma (signedSpin x) (signedSpin x) z := by
  funext z
  rw [GaussianProposal.goeBilinear_eq_matrix]
  rfl

theorem goeSpinHamiltonian_gaussian {n : ℕ} (sigma : ℝ) (x : Spin n) :
    HasGaussianLaw (goeSpinHamiltonian sigma x)
      (GaussianProposal.primitiveGaussian (Fin n × Fin n)) := by
  rw [goeSpinHamiltonian_eq_half_bilinear]
  exact (GaussianProposal.goeBilinear_gaussian sigma (signedSpin x) (signedSpin x)).fun_smul
    (1 / 2)

theorem goeSpinHamiltonian_mean {n : ℕ} (sigma : ℝ) (x : Spin n) :
    ∫ z, goeSpinHamiltonian sigma x z
      ∂GaussianProposal.primitiveGaussian (Fin n × Fin n) = 0 := by
  rw [goeSpinHamiltonian_eq_half_bilinear, integral_const_mul,
    GaussianProposal.goeBilinear_mean, mul_zero]

theorem signedSpin_dot_self {n : ℕ} (x : Spin n) :
    GaussianProposal.dot (signedSpin x) (signedSpin x) = n := by
  unfold GaussianProposal.dot
  simp only [← pow_two, signedSpin_sq]
  simp

theorem goeSpinHamiltonian_variance {n : ℕ} (sigma : ℝ) (x : Spin n) :
    Var[goeSpinHamiltonian sigma x;
      GaussianProposal.primitiveGaussian (Fin n × Fin n)] = sigma ^ 2 * (n : ℝ) ^ 2 := by
  rw [goeSpinHamiltonian_eq_half_bilinear, variance_const_mul]
  rw [← covariance_self (GaussianProposal.goeBilinear_gaussian sigma
    (signedSpin x) (signedSpin x)).aemeasurable,
    GaussianProposal.goeBilinear_covariance, signedSpin_dot_self]
  ring

theorem sk_seed_hamiltonian_variance {n : ℕ} (hn : 0 < n) (x : Spin n) :
    Var[goeSpinHamiltonian (1 / Real.sqrt (2 * (n : ℝ))) x;
      GaussianProposal.primitiveGaussian (Fin n × Fin n)] = (n : ℝ) / 2 := by
  rw [goeSpinHamiltonian_variance, div_pow, one_pow, Real.sq_sqrt (by positivity)]
  have hnR : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  field_simp

theorem sk_seed_hamiltonian_tail {n : ℕ} (hn : 0 < n) (x : Spin n)
    (u : ℝ) (hu : 0 < u) :
    (GaussianProposal.primitiveGaussian (Fin n × Fin n)).real
      {z | u ≤ |goeSpinHamiltonian (1 / Real.sqrt (2 * (n : ℝ))) x z|} ≤
      2 * Real.exp (-u ^ 2 / (n : ℝ)) := by
  have h := gaussian_centered_two_sided_tail
    (GaussianProposal.primitiveGaussian (Fin n × Fin n))
    (goeSpinHamiltonian (1 / Real.sqrt (2 * (n : ℝ))) x)
    (goeSpinHamiltonian_gaussian _ _) (goeSpinHamiltonian_mean _ _)
    ((n : ℝ) / 2) u (by positivity) hu (sk_seed_hamiltonian_variance hn x)
  convert h using 1 <;> congr 2 <;> ring

theorem sk_seed_hamiltonian_uniform_tail {n : ℕ} (hn : 0 < n)
    (u : ℝ) (hu : 0 < u) :
    (GaussianProposal.primitiveGaussian (Fin n × Fin n)).real
      {z | ∃ x : Spin n, u ≤ |goeSpinHamiltonian (1 / Real.sqrt (2 * (n : ℝ))) x z|} ≤
      (2 ^ n : ℝ) * (2 * Real.exp (-u ^ 2 / (n : ℝ))) := by
  have hevent : {z | ∃ x : Spin n,
      u ≤ |goeSpinHamiltonian (1 / Real.sqrt (2 * (n : ℝ))) x z|} =
      ⋃ x : Spin n, {z | u ≤ |goeSpinHamiltonian (1 / Real.sqrt (2 * (n : ℝ))) x z|} := by
    ext z
    simp
  rw [hevent]
  calc
    _ ≤ ∑ x : Spin n, (GaussianProposal.primitiveGaussian (Fin n × Fin n)).real
        {z | u ≤ |goeSpinHamiltonian (1 / Real.sqrt (2 * (n : ℝ))) x z|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _x : Spin n, 2 * Real.exp (-u ^ 2 / (n : ℝ)) := by
      exact Finset.sum_le_sum (fun x _ ↦ sk_seed_hamiltonian_tail hn x u hu)
    _ = _ := by simp [Spin, Fintype.card_fun]

end SKConstants
