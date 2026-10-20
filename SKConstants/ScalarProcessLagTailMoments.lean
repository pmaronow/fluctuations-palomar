module
public import SKConstants.ScalarProcessLagTail
public import SKConstants.ConcentrationMoments
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Convex.Integral

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

lemma factorial_moment_le_of_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (C B : ℝ) (hC : 0 ≤ C) (hB : 0 < B)
    (htail : ∀ x : ℝ, 0 ≤ x → μ.real {ω | x ≤ |X ω|} ≤ C * Real.exp (-(x/B)))
    (k : ℕ) :
    Integrable (fun ω => |X ω|^(k+1)) μ ∧
    (∫ ω, |X ω|^(k+1) ∂μ) ≤ C * ((k+1).factorial : ℝ) * B^(k+1) := by
  have hk : 0 < (k : ℝ)+1 := by positivity
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi hk (show 0 < 1/B by positivity)
  have hrpow : B^((k : ℝ)+1) = B^(k+1) := by
    rw [← Nat.cast_one, ← Nat.cast_add, Real.rpow_natCast]
  have hkernel : (∫ t : ℝ in Ioi 0, t^k * Real.exp (-(t/B))) =
      (k.factorial : ℝ) * B^(k+1) := by
    simpa [Real.Gamma_nat_eq_factorial, Real.rpow_natCast, mul_comm, div_eq_mul_inv, hrpow] using hgamma
  have hInt : IntegrableOn (fun t : ℝ => t^k * Real.exp (-(t/B))) (Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [hkernel]; positivity)
  have habs : Measurable (fun ω => |X ω|) := continuous_abs.measurable.comp hX
  have hp : 0 < ((k+1 : ℕ) : ℝ) := by positivity
  have hlayer := lintegral_rpow_eq_lintegral_meas_le_mul μ (p := ((k+1 : ℕ) : ℝ))
    (ae_of_all _ (fun ω => abs_nonneg (X ω))) habs.aemeasurable hp
  simp only [Real.rpow_natCast] at hlayer
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Real.rpow_natCast] at hlayer
  have hL : (∫⁻ ω, ENNReal.ofReal (|X ω|^(k+1)) ∂μ) ≤
      ENNReal.ofReal (C * ((k+1).factorial : ℝ) * B^(k+1)) := by
    rw [hlayer]
    calc
      _ ≤ ENNReal.ofReal ((k : ℝ)+1) *
          ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (C * (t^k * Real.exp (-(t/B)))) := by
        apply mul_le_mul' le_rfl
        apply setLIntegral_mono' measurableSet_Ioi
        intro t ht
        rw [← ofReal_measureReal, ← ENNReal.ofReal_mul measureReal_nonneg]
        apply ENNReal.ofReal_le_ofReal
        calc
          μ.real {ω | t ≤ |X ω|} * t^k ≤ (C * Real.exp (-(t/B))) * t^k :=
            mul_le_mul_of_nonneg_right (htail t ht.le) (pow_nonneg ht.le _)
          _ = _ := by ring
      _ = _ := by
        have hnonneg : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
            0 ≤ C * (t^k * Real.exp (-(t/B))) := by
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          exact mul_nonneg hC (mul_nonneg (pow_nonneg ht.le _) (Real.exp_pos _).le)
        rw [← ofReal_integral_eq_lintegral_ofReal (hInt.const_mul C) hnonneg]
        rw [integral_const_mul, hkernel, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (k : ℝ)+1)]
        congr 1
        rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        ring
  have hnn : ∀ᵐ ω ∂μ, 0 ≤ |X ω|^(k+1) := ae_of_all _ (fun ω => pow_nonneg (abs_nonneg _) _)
  have hm : AEStronglyMeasurable (fun ω => |X ω|^(k+1)) μ :=
    (habs.pow_const (k+1)).aestronglyMeasurable
  constructor
  · exact (lintegral_ofReal_ne_top_iff_integrable hm hnn).mp
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL)
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hm]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top hL |>.trans_eq
      (ENNReal.toReal_ofReal (by positivity))

lemma scalarLagInnovationSum_factorial_moments (z : ℝ) (dt : ℕ → ℝ≥0)
    (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (n : ℕ)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1)
    (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h) (p : ℕ) :
    Integrable (fun q => |scalarLagInnovationSum z dt n q|^p) (scalarObservationHistoryLaw z dt n) ∧
    (∫ q, |scalarLagInnovationSum z dt n q|^p ∂scalarObservationHistoryLaw z dt n) ≤
      (4 * Real.exp 1) * (p.factorial : ℝ) * (16*h)^p := by
  cases p with
  | zero =>
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one]
    constructor
    · exact integrable_const 1
    · simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      have he : 1 ≤ Real.exp 1 := by
        simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 1)
      linarith
  | succ k =>
    apply factorial_moment_le_of_exponential_tail _ _
      (measurable_scalarPredictableInnovationSum z dt (scalarLagCoefficient z)
        (measurable_scalarLagCoefficient z) n) (4*Real.exp 1) (16*h) (by positivity) (by positivity)
    intro x hx
    have htail := scalarLagInnovationSum_exponential_tail z dt h hh hh1 n hdt hduration x hx
    simpa only [scalarLagInnovationSum, sub_eq_add_neg, Real.exp_add, mul_assoc] using htail

lemma integral_eq_zero_of_subgaussian_mgf {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (V : ℝ≥0)
    (hV : 0 < V) (hX : HasSubgaussianMGF X V μ) : (∫ ω, X ω ∂μ) = 0 := by
  have hVR : 0 < (V : ℝ) := by exact_mod_cast hV
  have hInt : Integrable X μ := by
    simpa only [pow_one] using integrable_pow_of_integrable_exp_mul
      (by norm_num : (1 : ℝ) ≠ 0) (hX.integrable_exp_mul 1) (hX.integrable_exp_mul (-1)) 1
  let m : ℝ := ∫ ω, X ω ∂μ
  let θ : ℝ := m/(V : ℝ)
  have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => mem_univ _)) (hInt.const_mul θ) (hX.integrable_exp_mul θ)
  rw [integral_const_mul] at hj
  have hs := Real.exp_le_exp.mp (hj.trans (hX.mgf_le θ))
  have hs' := mul_le_mul_of_nonneg_right hs hVR.le
  have he1 : (θ*m)*(V : ℝ) = m^2 := by dsimp [θ]; field_simp
  have he2 : ((V : ℝ)*θ^2/2)*(V : ℝ) = m^2/2 := by dsimp [θ]; field_simp
  change (θ*m)*(V : ℝ) ≤ ((V : ℝ)*θ^2/2)*(V : ℝ) at hs'
  rw [he1, he2] at hs'
  change m = 0
  nlinarith [sq_nonneg m]

lemma scalarLagInnovationSum_subgaussian (z : ℝ) (dt : ℕ → ℝ≥0)
    (h : ℝ) (hh : 0 < h) (n : ℕ)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1)
    (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h) :
    HasSubgaussianMGF (scalarLagInnovationSum z dt n) ⟨8*h, by positivity⟩
      (scalarObservationHistoryLaw z dt n) := by
  apply scalarPredictableInnovationSum_subgaussian z dt (scalarLagCoefficient z)
    (measurable_scalarLagCoefficient z) n
  apply ae_of_all
  intro p
  change scalarPredictableInnovationProxy dt (scalarLagCoefficient z) n p ≤ 8*h
  have hcoef (k : ℕ) (_ : k < n) (q : ScalarObservationHistory k) :
      scalarLagCoefficient z k q ^ 2 ≤ 2^2 := by
    have hb := scalarPosteriorIncrement_abs_le_two z (scalarLastField z k q)
    simpa only [scalarPosteriorIncrement, scalarLagCoefficient, sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) hb 2
  convert scalarPredictableInnovationProxy_le_duration dt (scalarLagCoefficient z)
    n 2 h hcoef hdt hduration p using 1
  norm_num

lemma integral_scalarLagInnovationSum_eq_zero (z : ℝ) (dt : ℕ → ℝ≥0)
    (h : ℝ) (hh : 0 < h) (n : ℕ)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1)
    (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h) :
    (∫ q, scalarLagInnovationSum z dt n q ∂scalarObservationHistoryLaw z dt n) = 0 :=
  integral_eq_zero_of_subgaussian_mgf _ _ ⟨8*h, by positivity⟩ (by change 0 < 8*h; positivity)
    (scalarLagInnovationSum_subgaussian z dt h hh n hdt hduration)

lemma scalarLagInnovationSum_local_mgf (z : ℝ) (dt : ℕ → ℝ≥0)
    (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (n : ℕ)
    (hdt : ∀ k < n, (dt k : ℝ) ≤ 1)
    (hduration : (∑ k ∈ Finset.range n, (dt k : ℝ)) ≤ h) :
    Concentration.LocalQuadraticMGF (scalarLagInnovationSum z dt n)
      (scalarObservationHistoryLaw z dt n) (2048*Real.exp 1*h^2) (1/(32*h)) := by
  have hm := scalarLagInnovationSum_factorial_moments z dt h hh hh1 n hdt hduration
  have hPowers (p : ℕ) : Integrable (fun q => scalarLagInnovationSum z dt n q^p)
      (scalarObservationHistoryLaw z dt n) := by
    apply (integrable_norm_iff ((measurable_scalarPredictableInnovationSum z dt (scalarLagCoefficient z)
      (measurable_scalarLagCoefficient z) n).pow_const p).aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs, abs_pow, scalarLagInnovationSum] using (hm p).1
  have hMoments (p : ℕ) (hp : 2 ≤ p) :
      (∫ q, |scalarLagInnovationSum z dt n q|^p ∂scalarObservationHistoryLaw z dt n) ≤
      (p.factorial : ℝ) * ((4*Real.exp 1)*(16*h)^2) * (16*h)^(p-2) := by
    apply (hm p).2.trans_eq
    have he : (16*h)^p = (16*h)^2 * (16*h)^(p-2) := by
      rw [← pow_add]
      congr 1
      omega
    rw [he]
    ring
  have hmgf := Concentration.localQuadraticMGF_of_factorial_moments
    (measurable_scalarPredictableInnovationSum z dt (scalarLagCoefficient z)
      (measurable_scalarLagCoefficient z) n)
    (by positivity : 0 ≤ (4*Real.exp 1)*(16*h)^2) (by positivity : 0 < 16*h)
    hPowers (integral_scalarLagInnovationSum_eq_zero z dt h hh n hdt hduration) hMoments
  have heV : 2*((4*Real.exp 1)*(16*h)^2) = 2048*Real.exp 1*h^2 := by ring
  have heR : 1/(2*(16*h)) = 1/(32*h) := by congr 1; ring
  simpa only [scalarLagInnovationSum, heV, heR] using hmgf

end SKConstants
