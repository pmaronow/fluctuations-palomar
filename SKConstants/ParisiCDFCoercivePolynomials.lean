module

public import SKConstants.ParisiFiniteCDFCurvature

@[expose] public section

/-!
Polynomial conversion and bounds adapted from OpenAI math, Apache-2.0, commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,
Density/CoerciveMoments.lean.  These generic algebraic lemmas are used for the
literal finite-temperature feedback curvature limit.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section

namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat

lemma scaled_jet {f : ℝ → ℝ} (_hf : ContDiff ℝ ∞ f) (c : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => c*f y) x=c*iteratedDeriv n f x :=
  iteratedDeriv_const_mul_field c f

def coerciveJetPolynomial (c A B C : ℝ) : ℝ := c^2*C^2-12*c^3*A*B^2+6*c^4*A^4

def quarticJetPolynomial (c A : ℝ) : ℝ := c^4*A^4

lemma quarticMoment_scaled {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (c x : ℝ) :
    quarticMoment (fun y => c*deriv f y) x=quarticJetPolynomial c (iteratedDeriv 2 f x) := by
  have hd := contDiff_infty_iff_deriv.mp hf |>.2
  have he := scaled_jet hd c 1 x
  simp only [iteratedDeriv_one] at he
  simp only [quarticMoment,certV,he,quarticJetPolynomial,iteratedDeriv_succ,iteratedDeriv_zero]
  ring

lemma coercivePolynomial_scaled {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (c x : ℝ) :
    coercivePolynomial (fun y => c*deriv f y) x=coerciveJetPolynomial c
      (iteratedDeriv 2 f x) (iteratedDeriv 3 f x) (iteratedDeriv 4 f x) := by
  have hd := contDiff_infty_iff_deriv.mp hf |>.2
  have he := scaled_jet hd c 1 x
  simp only [iteratedDeriv_one] at he
  simp only [coercivePolynomial,certV,certW,certZ,he,scaled_jet hd,
    coerciveJetPolynomial,iteratedDeriv_succ,iteratedDeriv_zero]
  ring

lemma quarticJetPolynomial_bound {c A D E : ℝ} (hc : |c| ≤ D) (hA : |A| ≤ E) :
    |quarticJetPolynomial c A| ≤ D^4*E^4 := by
  simp only [quarticJetPolynomial,abs_mul,abs_pow]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hc 4) (pow_le_pow_left₀ (abs_nonneg _) hA 4)
    (by positivity) (by positivity)

lemma coerciveJetPolynomial_bound {c A B C D E F G : ℝ}
    (hc : |c| ≤ D) (hA : |A| ≤ E) (hB : |B| ≤ F) (hC : |C| ≤ G) :
    |coerciveJetPolynomial c A B C| ≤ D^2*G^2+12*D^3*E*F^2+6*D^4*E^4 := by
  have hD : 0 ≤ D := (abs_nonneg _).trans hc
  have hE : 0 ≤ E := (abs_nonneg _).trans hA
  have hF : 0 ≤ F := (abs_nonneg _).trans hB
  have hG : 0 ≤ G := (abs_nonneg _).trans hC
  have h1 : |c^2*C^2| ≤ D^2*G^2 := by
    simp only [abs_mul,abs_pow]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hc 2) (pow_le_pow_left₀ (abs_nonneg _) hC 2) (by positivity) (by positivity)
  have h2 : |12*c^3*A*B^2| ≤ 12*D^3*E*F^2 := by
    simp only [abs_mul,abs_pow,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 12)]
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hc 3) (by norm_num)) hA (abs_nonneg _) (by positivity))
      (pow_le_pow_left₀ (abs_nonneg _) hB 2) (by positivity) (by positivity)
  have h3 : |6*c^4*A^4| ≤ 6*D^4*E^4 := by
    simp only [abs_mul,abs_pow,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hc 4) (by norm_num))
      (pow_le_pow_left₀ (abs_nonneg _) hA 4) (by positivity) (by positivity)
  exact (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add h1 h2)) h3)

end SKConstants.ParisiFullSupport
