module
public import SKConstants.ConcentrationMoments
public import SKConstants.ScalarObservationPredictableSums

public section
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.Concentration

lemma subGaussian_integrable_abs_pow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (V : ℝ≥0) (hX : HasSubgaussianMGF X V μ) (p : ℕ) :
    Integrable (fun ω => |X ω| ^ p) μ :=
  integrable_pow_abs_of_integrable_exp_mul (t := 1) (by norm_num)
    (hX.integrable_exp_mul 1) (hX.integrable_exp_mul (-1)) p

lemma subGaussian_even_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (V : ℝ≥0)
    (hV : 0 < V) (hX : HasSubgaussianMGF X V μ) (p : ℕ) :
    (∫ ω, |X ω| ^ (2*p) ∂μ) ≤ 2 * (p.factorial : ℝ) * (Real.exp 1 * (V : ℝ)) ^ p := by
  by_cases hp : p = 0
  · simp [hp]
  have hpR : 0 < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hp
  have hVR : 0 < (V : ℝ) := NNReal.coe_pos.mpr hV
  let θ := Real.sqrt (2 * (p : ℝ) / (V : ℝ))
  have hθ : 0 < θ := Real.sqrt_pos.mpr (by positivity)
  have hθsq : θ ^ 2 = 2 * (p : ℝ) / (V : ℝ) := Real.sq_sqrt (by positivity)
  let C : ℝ := ((2*p).factorial : ℝ) / θ ^ (2*p)
  have hC : 0 ≤ C := by positivity
  have hdom (ω : Ω) : |X ω| ^ (2*p) ≤ C * (Real.exp (θ * X ω) + Real.exp (-θ * X ω)) := by
    have he := Real.pow_div_factorial_le_exp (θ * |X ω|) (mul_nonneg hθ.le (abs_nonneg (X ω))) (2*p)
    have hf : 0 < ((2*p).factorial : ℝ) := by positivity
    have hc : |X ω| ^ (2*p) ≤ C * Real.exp (θ * |X ω|) := by
      dsimp only [C]
      rw [mul_pow] at he
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ (pow_pos hθ _)).mpr
      calc
        _ ≤ ((2*p).factorial : ℝ) * Real.exp (θ * |X ω|) := by
          have he' := (div_le_iff₀ hf).mp he
          nlinarith
        _ = _ := by ring
    apply hc.trans
    apply mul_le_mul_of_nonneg_left _ hC
    simpa only [abs_mul, abs_of_pos hθ, neg_mul] using Real.exp_abs_le (θ * X ω)
  have hbound := integral_mono (subGaussian_integrable_abs_pow μ X V hX (2*p))
    (((hX.integrable_exp_mul θ).add (hX.integrable_exp_mul (-θ))).const_mul C) hdom
  simp only [Pi.add_apply] at hbound
  rw [integral_const_mul, integral_add (hX.integrable_exp_mul θ) (hX.integrable_exp_mul (-θ))] at hbound
  have hfac : ((2*p).factorial : ℝ) ≤ (2 * (p : ℝ)) ^ p * (p.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_two_mul_le p
  have hθpow : θ ^ (2*p) = (2 * (p : ℝ)) ^ p / (V : ℝ) ^ p := by
    rw [pow_mul, hθsq, div_pow]
  have hCB : C ≤ (p.factorial : ℝ) * (V : ℝ) ^ p := by
    dsimp only [C]
    apply (div_le_iff₀ (pow_pos hθ _)).mpr
    rw [hθpow]
    have he : (p.factorial : ℝ) * (V : ℝ) ^ p * ((2 * (p : ℝ)) ^ p / (V : ℝ) ^ p) =
        (2 * (p : ℝ)) ^ p * (p.factorial : ℝ) := by
      field_simp
    rwa [he]
  have hmgf : mgf X μ θ + mgf X μ (-θ) ≤ 2 * Real.exp (p : ℝ) := by
    have h1 := hX.mgf_le θ
    have h2 := hX.mgf_le (-θ)
    have he : (V : ℝ) * θ ^ 2 / 2 = (p : ℝ) := by rw [hθsq]; field_simp
    rw [he] at h1
    rw [neg_sq, he] at h2
    linarith
  calc
    _ ≤ C * (mgf X μ θ + mgf X μ (-θ)) := hbound
    _ ≤ C * (2 * Real.exp (p : ℝ)) := mul_le_mul_of_nonneg_left hmgf hC
    _ ≤ ((p.factorial : ℝ) * (V : ℝ) ^ p) * (2 * Real.exp (p : ℝ)) :=
      mul_le_mul_of_nonneg_right hCB (by positivity)
    _ = _ := by
      rw [mul_pow]
      have he : Real.exp (p : ℝ) = Real.exp 1 ^ p := by simp
      rw [he]
      ring
@[expose] def centeredObservable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ) (ω : Ω) : ℝ := Y ω - ∫ u, Y u ∂μ

lemma factorial_moments_centered {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : Measurable Y)
    (B : ℝ) (hB : 0 < B)
    (hInt : ∀ p, Integrable (fun ω => |Y ω| ^ p) μ)
    (hMom : ∀ p, (∫ ω, |Y ω| ^ p ∂μ) ≤ (p.factorial : ℝ) * B ^ p) :
    (∀ p, Integrable (fun ω => centeredObservable μ Y ω ^ p) μ) ∧
    (∀ p, 1 ≤ p → (∫ ω, |centeredObservable μ Y ω| ^ p ∂μ) ≤
      (p.factorial : ℝ) * (2 * B) ^ p) := by
  have hmean : |∫ ω, Y ω ∂μ| ≤ B := by
    apply (norm_integral_le_integral_norm Y).trans
    simpa only [Real.norm_eq_abs, pow_one, Nat.factorial_one, Nat.cast_one, one_mul] using hMom 1
  have hdom (p : ℕ) (ω : Ω) : |centeredObservable μ Y ω| ^ p ≤
      2 ^ (p-1) * (|Y ω| ^ p + B ^ p) := by
    unfold centeredObservable
    apply (pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) p).trans
    apply (pow_le_pow_left₀ (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (show |Y ω| + |∫ u, Y u ∂μ| ≤ |Y ω| + B by linarith) p).trans
    exact add_pow_le (abs_nonneg _) hB.le p
  have hAbsInt (p : ℕ) : Integrable (fun ω => |centeredObservable μ Y ω| ^ p) μ := by
    apply (((hInt p).add (integrable_const (B ^ p))).const_mul (2 ^ (p-1))).mono' ((((continuous_abs.measurable.comp (hY.sub_const _)).pow_const p).aestronglyMeasurable))
    apply Filter.Eventually.of_forall
    intro ω
    simpa only [Real.norm_eq_abs, abs_pow, abs_abs, Pi.add_apply, centeredObservable, Function.comp_def] using hdom p ω
  refine ⟨fun p => ?_, ?_⟩
  · apply (hAbsInt p).mono' ((hY.sub_const _).pow_const p).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by simp [Real.norm_eq_abs, centeredObservable])
  intro p hp
  have hf : 1 ≤ (p.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos p
  calc
    _ ≤ ∫ ω, 2 ^ (p-1) * (|Y ω| ^ p + B ^ p) ∂μ :=
      integral_mono (hAbsInt p) (((hInt p).add (integrable_const (B ^ p))).const_mul _) (hdom p)
    _ = 2 ^ (p-1) * ((∫ ω, |Y ω| ^ p ∂μ) + B ^ p) := by
      rw [integral_const_mul, integral_add (hInt p) (integrable_const _)]
      simp
    _ ≤ 2 ^ (p-1) * ((p.factorial : ℝ) * B ^ p + (p.factorial : ℝ) * B ^ p) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (hMom p) (by nlinarith [pow_nonneg hB.le p])
    _ = _ := by
      have he : (2 : ℝ) ^ (p-1) * 2 = 2 ^ p := by
        rw [← pow_succ]
        congr 1
        omega
      rw [mul_pow]
      calc
        _ = (p.factorial : ℝ) * B ^ p * (2 ^ (p-1) * 2) := by ring
        _ = _ := by rw [he]; ring

lemma subGaussian_square_factorial_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (V : ℝ≥0)
    (hV : 0 < V) (hX : HasSubgaussianMGF X V μ) (p : ℕ) :
    (∫ ω, |X ω ^ 2| ^ p ∂μ) ≤ (p.factorial : ℝ) * (2 * Real.exp 1 * (V : ℝ)) ^ p := by
  by_cases hp : p = 0
  · simp [hp]
  have h2 : (2 : ℝ) ≤ 2 ^ p := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.one_le_iff_ne_zero.mpr hp)
    simpa only [pow_one] using h
  calc
    _ = ∫ ω, |X ω| ^ (2*p) ∂μ := by simp_rw [abs_pow, ← pow_mul]
    _ ≤ 2 * (p.factorial : ℝ) * (Real.exp 1 * (V : ℝ)) ^ p :=
      subGaussian_even_moment_bound μ X V hV hX p
    _ ≤ (p.factorial : ℝ) * (2 * (Real.exp 1 * (V : ℝ))) ^ p := by
      rw [mul_pow (2 : ℝ)]
      nlinarith [mul_le_mul_of_nonneg_right h2 (mul_nonneg (by positivity : (0 : ℝ) ≤ (p.factorial : ℝ))
        (pow_nonneg (mul_nonneg (Real.exp_pos 1).le V.coe_nonneg) p))]
    _ = _ := by congr 2; ring

lemma subGaussian_centered_square_localMGF {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hMeas : Measurable X)
    (V : ℝ≥0) (hV : 0 < V) (hX : HasSubgaussianMGF X V μ) :
    LocalQuadraticMGF (centeredObservable μ (fun ω => X ω ^ 2)) μ
      (2 * (4 * Real.exp 1 * (V : ℝ)) ^ 2) (1 / (8 * Real.exp 1 * (V : ℝ))) := by
  have hVR : 0 < (V : ℝ) := NNReal.coe_pos.mpr hV
  have hInt (p : ℕ) : Integrable (fun ω => |X ω ^ 2| ^ p) μ := by
    simpa only [abs_pow, ← pow_mul] using subGaussian_integrable_abs_pow μ X V hX (2*p)
  have hcenter := factorial_moments_centered μ (fun ω => X ω ^ 2) (by fun_prop)
    (2 * Real.exp 1 * (V : ℝ)) (by positivity) hInt (subGaussian_square_factorial_moments μ X V hV hX)
  have hMean : (∫ ω, centeredObservable μ (fun ω => X ω ^ 2) ω ∂μ) = 0 := by
    unfold centeredObservable
    rw [integral_sub (by simpa only [pow_one, abs_pow, sq_abs] using hInt 1) (integrable_const _)]
    simp
  convert localQuadraticMGF_of_factorial_moments (X := centeredObservable μ (fun ω => X ω ^ 2))
    (v := (4 * Real.exp 1 * (V : ℝ)) ^ 2) (B := 4 * Real.exp 1 * (V : ℝ))
    (hMeas.pow_const 2 |>.sub_const _) (by positivity) (by positivity) hcenter.1 hMean (fun p hp => ?_) using 1
  · ring
  · have hm := hcenter.2 p (by omega)
    have he : 2 * (2 * Real.exp 1 * (V : ℝ)) = 4 * Real.exp 1 * (V : ℝ) := by ring
    rw [he] at hm
    rw [mul_assoc, ← pow_add]
    simpa only [show 2 + (p - 2) = p by omega] using hm
end SKConstants.Concentration
