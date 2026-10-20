module

public import SKConstants.Completion.LM4.LinkedRowLaw
public import SKConstants.ScalarProcessLagTailMoments

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SKConstants.Completion.LM4

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem log_moments_of_lower_tail [IsProbabilityMeasure μ]
    {L : Ω → ℝ} (hL : Measurable L)
    (hUpper : ∀ᵐ ω ∂μ, L ω ≤ 1)
    (hLower : ∀ t : ℝ, 0 ≤ t → μ.real {ω | L ω ≤ -t} ≤ Real.exp (-t)) :
    ∀ p : ℕ, Integrable (fun ω => |L ω| ^ p) μ ∧
      (∫ ω, |L ω| ^ p ∂μ) ≤ 2 * (p.factorial : ℝ) := by
  let N : Ω → ℝ := fun ω => max (-L ω) 0
  have hN : Measurable N := hL.neg.max measurable_const
  have habsN (ω : Ω) : |N ω| = N ω := abs_of_nonneg (le_max_right (-L ω) 0)
  have hTail (t : ℝ) (ht : 0 ≤ t) :
      μ.real {ω | t ≤ |N ω|} ≤ 1 * Real.exp (-(t / 1)) := by
    by_cases ht0 : t = 0
    · simp only [ht0, zero_div, neg_zero, Real.exp_zero, one_mul]
      exact measureReal_le_one
    have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    apply (measureReal_mono (s₂ := {ω | L ω ≤ -t}) ?_).trans (by simpa using hLower t ht)
    intro ω hω
    change L ω ≤ -t
    change t ≤ |N ω| at hω
    rw [habsN, show N ω = max (-L ω) 0 from rfl, le_max_iff] at hω
    rcases hω with hω | hω
    · linarith
    · linarith
  intro p
  cases p with
  | zero => simp
  | succ k =>
    have hNm := factorial_moment_le_of_exponential_tail μ N hN 1 1
      (by norm_num) (by norm_num) hTail k
    simp only [one_mul, one_pow, mul_one] at hNm
    have hdom : ∀ᵐ ω ∂μ, |L ω| ^ (k + 1) ≤ N ω ^ (k + 1) + 1 := by
      filter_upwards [hUpper] with ω hω
      by_cases hneg : L ω ≤ 0
      · simp only [abs_of_nonpos hneg, N, max_eq_left (neg_nonneg.mpr hneg)]
        linarith
      · have hpos : 0 ≤ L ω := le_of_not_ge hneg
        have hh := pow_le_pow_left₀ hpos hω (k + 1)
        simp only [one_pow] at hh
        rw [abs_of_nonneg hpos]
        have hnn : 0 ≤ N ω ^ (k + 1) := pow_nonneg (le_max_right (-L ω) 0) _
        linarith
    have hNI : Integrable (fun ω => N ω ^ (k + 1)) μ := by
      simpa only [habsN] using hNm.1
    have hI : Integrable (fun ω => |L ω| ^ (k + 1)) μ := by
      apply (hNI.add (integrable_const 1)).mono' (by fun_prop)
      simpa only [Real.norm_eq_abs, abs_pow, abs_abs, Pi.add_apply] using hdom
    refine ⟨hI, (integral_mono_ae hI (hNI.add (integrable_const 1)) hdom).trans ?_⟩
    simp only [Pi.add_apply]
    rw [integral_add hNI (integrable_const 1)]
    have hm : (∫ ω, N ω ^ (k + 1) ∂μ) ≤ ((k + 1).factorial : ℝ) := by
      simpa only [habsN] using hNm.2
    have hf : 1 ≤ ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (k + 1)
    simpa using (show (∫ ω, N ω ^ (k + 1) ∂μ) + 1 ≤ 2 * ((k + 1).factorial : ℝ) by linarith)

theorem linkedRowLaw_log_moments [IsProbabilityMeasure μ]
    {ell : Ω → ℝ} (hell : Measurable ell)
    (hbound : ∀ᵐ ω ∂μ, 0 ≤ ell ω ∧ ell ω ≤ 2)
    (hnorm : ∫ ω, ell ω ∂μ = 1) (p : ℕ) :
    Integrable (fun ω => |Real.log (ell ω)| ^ p) (linkedRowLaw μ ell) ∧
      (∫ ω, |Real.log (ell ω)| ^ p ∂linkedRowLaw μ ell) ≤ 2 * (p.factorial : ℝ) := by
  have := linkedRowLaw_isProbability hell hbound hnorm
  apply log_moments_of_lower_tail hell.log
    ((linkedRowLaw_log_le_log_two hell hbound).mono (fun _ hω => hω.trans ?_))
    (fun t _ => linkedRowLaw_log_lower_tail hell t) p
  have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

theorem subgaussian_upper_exponential_tail [IsProbabilityMeasure μ]
    {J : Ω → ℝ} (V : ℝ≥0) (hJ : HasSubgaussianMGF J (4 * V) μ) (x : ℝ) :
    μ.real {ω | x ≤ J ω} ≤
      Real.exp (1 / 8 : ℝ) * Real.exp (-(x / (2 * (1 + (V : ℝ))))) := by
  let S := 1 + (V : ℝ)
  let t := 1 / (2 * S)
  have hS : 0 < S := by dsimp [S]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hcap : (2 * (V : ℝ)) * t ^ 2 ≤ 1 / 8 := by
    dsimp [t]
    rw [div_pow, one_pow, ← mul_div_assoc, mul_one]
    apply (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < 2 * S))).mpr
    dsimp [S]
    nlinarith [sq_nonneg ((V : ℝ) - 1)]
  calc
    _ ≤ Real.exp (-t * x) * mgf J μ t :=
      measure_ge_le_exp_mul_mgf x ht (hJ.integrable_exp_mul t)
    _ ≤ Real.exp (-t * x) * Real.exp ((2 * (V : ℝ)) * t ^ 2) := by
      gcongr
      have hm := hJ.mgf_le t
      push_cast at hm
      convert hm using 1
      congr 1
      ring
    _ ≤ Real.exp (-t * x) * Real.exp (1 / 8 : ℝ) := by gcongr
    _ = _ := by
      rw [mul_comm]
      congr 2
      dsimp [t, S]
      ring

theorem linkedRowLaw_integral_exponential_tail [IsProbabilityMeasure μ]
    {ell J : Ω → ℝ} (hbound : ∀ᵐ ω ∂μ, ell ω ≤ 2)
    (V : ℝ≥0) (hJ : HasSubgaussianMGF J (4 * V) μ) (x : ℝ) :
    (linkedRowLaw μ ell).real {ω | x ≤ |J ω|} ≤
      5 * Real.exp (-(x / (2 * (1 + (V : ℝ))))) := by
  have he : {ω | x ≤ |J ω|} = {ω | x ≤ J ω} ∪ {ω | x ≤ -J ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  have hExp : Real.exp (1 / 8 : ℝ) ≤ 5 / 4 :=
    (Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)).trans (by norm_num)
  calc
    _ ≤ 2 * μ.real {ω | x ≤ |J ω|} := linkedRowLaw_real_le_two hbound _
    _ ≤ 2 * (μ.real {ω | x ≤ J ω} + μ.real {ω | x ≤ -J ω}) := by
      rw [he]
      gcongr
      exact measureReal_union_le _ _
    _ ≤ 2 * (Real.exp (1 / 8 : ℝ) * Real.exp (-(x / (2 * (1 + (V : ℝ))))) +
        Real.exp (1 / 8 : ℝ) * Real.exp (-(x / (2 * (1 + (V : ℝ)))))) := by
      gcongr
      · exact subgaussian_upper_exponential_tail V hJ x
      · exact subgaussian_upper_exponential_tail V hJ.neg x
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hExp
        (Real.exp_pos (-(x / (2 * (1 + (V : ℝ)))))).le
      nlinarith

theorem linkedRowLaw_integral_moments [IsProbabilityMeasure μ]
    {ell J : Ω → ℝ} (hell : Measurable ell) (hJm : Measurable J)
    (hbound : ∀ᵐ ω ∂μ, 0 ≤ ell ω ∧ ell ω ≤ 2)
    (hnorm : ∫ ω, ell ω ∂μ = 1)
    (V : ℝ≥0) (hJ : HasSubgaussianMGF J (4 * V) μ) (p : ℕ) :
    Integrable (fun ω => |J ω| ^ p) (linkedRowLaw μ ell) ∧
      (∫ ω, |J ω| ^ p ∂linkedRowLaw μ ell) ≤
        5 * (p.factorial : ℝ) * (2 * (1 + (V : ℝ))) ^ p := by
  have := linkedRowLaw_isProbability hell hbound hnorm
  cases p with
  | zero => simp
  | succ k =>
    exact factorial_moment_le_of_exponential_tail _ J hJm 5 (2 * (1 + (V : ℝ)))
      (by norm_num) (by positivity)
      (fun x _ => linkedRowLaw_integral_exponential_tail (hbound.mono (fun _ h => h.2)) V hJ x) k

end SKConstants.Completion.LM4
