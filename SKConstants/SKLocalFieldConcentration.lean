module

public import SKConstants.ConditionalGibbsConcentration
public import SKConstants.SpinGeometry
public import SKConstants.SKGibbsGauge

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set WithLp
open scoped ENNReal NNReal Topology BigOperators RealInnerProductSpace Classical
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

def goeSpinFieldCoefficient {n : ℕ} (sigma : ℝ) (x : Spin n) (u : Fin n → ℝ)
    (p : Fin n × Fin n) : ℝ :=
  sigma * (u p.1 * signedSpin x p.2 + u p.2 * signedSpin x p.1)

def goeSignedSpinField {n : ℕ} (sigma : ℝ) (x : Spin n) (u : Fin n → ℝ)
    (z : EuclideanSpace ℝ (Fin n × Fin n)) : ℝ :=
  ∑ i, u i * ∑ j, GaussianProposal.goeMatrix sigma z i j * signedSpin x j

theorem goeSignedSpinField_eq_linearForm {n : ℕ} (sigma : ℝ) (x : Spin n)
    (u : Fin n → ℝ) :
    goeSignedSpinField sigma x u = GaussianProposal.linearForm
      (goeSpinFieldCoefficient sigma x u) := by
  funext z
  have h := GaussianProposal.goeBilinear_eq_matrix sigma u (signedSpin x) z
  unfold goeSpinFieldCoefficient
  simpa only [goeSignedSpinField, Finset.mul_sum, GaussianProposal.goeBilinear, mul_assoc] using h.symm

theorem goeSpinFieldCoefficient_norm_sq {n : ℕ} (sigma : ℝ) (x : Spin n)
    (u : Fin n → ℝ) :
    ‖toLp 2 (goeSpinFieldCoefficient sigma x u)‖^2 =
      2 * sigma^2 * (‖toLp 2 u‖^2 * (n : ℝ) +
        (inner (𝕜 := ℝ) (toLp 2 u) (spinEuclidean x))^2) := by
  have hd (v w : EuclideanSpace ℝ (Fin n)) : GaussianProposal.dot v w =
      inner (𝕜 := ℝ) v w := by
    simp [GaussianProposal.dot, EuclideanSpace.inner_eq_star_dotProduct,
      dotProduct, mul_comm]
  have hc := GaussianProposal.goeBilinear_covariance sigma (toLp 2 u)
    (spinEuclidean x) (toLp 2 u) (spinEuclidean x)
  unfold GaussianProposal.goeBilinear at hc
  rw [GaussianProposal.linearForm_covariance] at hc
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ p, goeSpinFieldCoefficient sigma x u p ^ 2) = _
  simp only [goeSpinFieldCoefficient, pow_two] at ⊢
  simp_rw [hd, real_inner_self_eq_norm_sq] at hc
  rw [spinEuclidean_norm_sq] at hc
  simpa only [pow_two, spinEuclidean, real_inner_comm] using hc

theorem goeSpinFieldCoefficient_norm_sq_le {n : ℕ} (sigma : ℝ) (x : Spin n)
    (u : Fin n → ℝ) :
    ‖toLp 2 (goeSpinFieldCoefficient sigma x u)‖^2 ≤
      4 * sigma^2 * (n : ℝ) * ‖toLp 2 u‖^2 := by
  rw [goeSpinFieldCoefficient_norm_sq]
  have hi := abs_real_inner_le_norm (toLp 2 u) (spinEuclidean x)
  have hsq : (inner (𝕜 := ℝ) (toLp 2 u) (spinEuclidean x))^2 ≤
      ‖toLp 2 u‖^2 * (n : ℝ) := by
    have h := mul_self_le_mul_self (abs_nonneg _) hi
    have h' : |inner (𝕜 := ℝ) (toLp 2 u) (spinEuclidean x)|^2 ≤
        (‖toLp 2 u‖ * ‖spinEuclidean x‖)^2 := by simpa only [pow_two] using h
    rw [sq_abs] at h'
    rwa [mul_pow, spinEuclidean_norm_sq] at h'
  nlinarith [mul_nonneg (sq_nonneg sigma) (sub_nonneg.mpr hsq)]

theorem goeSpinFieldCoefficient_abs_sum_le {n : ℕ} (sigma : ℝ) (x : Spin n)
    (u : Fin n → ℝ) :
    (∑ p, |goeSpinFieldCoefficient sigma x u p|) ≤
      2 * |sigma| * (n : ℝ) * ∑ i, |u i| := by
  have hs (i : Fin n) : |signedSpin x i| = 1 := by
    cases hx : x i <;> simp [signedSpin, hx]
  calc
    _ ≤ ∑ p : Fin n × Fin n, |sigma| * (|u p.1| + |u p.2|) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [goeSpinFieldCoefficient, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg sigma)
      simpa only [abs_mul, hs, mul_one] using
        abs_add_le (u p.1 * signedSpin x p.2) (u p.2 * signedSpin x p.1)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem abs_conditionalGibbs_signedSpinField_mean_le {n : ℕ} (beta sigma : ℝ)
    (x : Spin n) (u : Fin n → ℝ) :
    |∫ z, goeSignedSpinField sigma x u z ∂conditionalGibbsGaussianLaw beta sigma x| ≤
      4 * |beta| * sigma^2 * (n : ℝ) * ∑ i, |u i| := by
  rw [goeSignedSpinField_eq_linearForm]
  have h := (abs_conditionalGibbs_linearForm_mean_le beta sigma x
    (goeSpinFieldCoefficient sigma x u)).trans
    (mul_le_mul_of_nonneg_left (goeSpinFieldCoefficient_abs_sum_le sigma x u) (by positivity))
  convert h using 1
  rw [← sq_abs sigma]
  ring

theorem skFieldNormalization_sq {n : ℕ} (hn : 0 < n) :
    (1 / Real.sqrt (2 * (n : ℝ)))^2 = 1 / (2 * (n : ℝ)) := by
  rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]

theorem sk_signedSpinField_hasSubgaussianMGF {n : ℕ} (hn : 0 < n) (beta : ℝ)
    (x : Spin n) (u : Fin n → ℝ) :
    HasSubgaussianMGF (fun z =>
      goeSignedSpinField (1 / Real.sqrt (2 * (n : ℝ))) x u z -
        ∫ y, goeSignedSpinField (1 / Real.sqrt (2 * (n : ℝ))) x u y
          ∂conditionalGibbsGaussianLaw beta (1 / Real.sqrt (2 * (n : ℝ))) x)
      (2 * ‖toLp 2 u‖₊^2)
      (conditionalGibbsGaussianLaw beta (1 / Real.sqrt (2 * (n : ℝ))) x) := by
  rw [goeSignedSpinField_eq_linearForm]
  have hsg := conditionalGibbs_linearForm_hasSubgaussianMGF beta
    (1 / Real.sqrt (2 * (n : ℝ))) x (goeSpinFieldCoefficient (1 / Real.sqrt (2 * (n : ℝ))) x u)
  have hp : (‖toLp 2 (goeSpinFieldCoefficient (1 / Real.sqrt (2 * (n : ℝ))) x u)‖₊^2 : ℝ≥0) ≤
      2 * ‖toLp 2 u‖₊^2 := by
    change ‖toLp 2 (goeSpinFieldCoefficient (1 / Real.sqrt (2 * (n : ℝ))) x u)‖^2 ≤
      2 * ‖toLp 2 u‖^2

    have h := goeSpinFieldCoefficient_norm_sq_le (1 / Real.sqrt (2 * (n : ℝ))) x u
    rw [skFieldNormalization_sq hn] at h
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have he : 4 * (1 / (2 * (n : ℝ))) * (n : ℝ) = 2 := by field_simp; ring
    rw [he] at h
    exact h
  refine ⟨hsg.integrable_exp_mul, fun t => (hsg.mgf_le t).trans ?_⟩
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp (sq_nonneg t)) (by norm_num)

theorem abs_sk_signedSpinField_mean_le {n : ℕ} (hn : 0 < n) (beta : ℝ)
    (x : Spin n) (u : Fin n → ℝ) :
    |∫ z, goeSignedSpinField (1 / Real.sqrt (2 * (n : ℝ))) x u z
      ∂conditionalGibbsGaussianLaw beta (1 / Real.sqrt (2 * (n : ℝ))) x| ≤
      2 * |beta| * ∑ i, |u i| := by
  have h := abs_conditionalGibbs_signedSpinField_mean_le beta
    (1 / Real.sqrt (2 * (n : ℝ))) x u
  rw [skFieldNormalization_sq hn] at h
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  convert h using 1 <;> field_simp <;> ring

end SKConstants
