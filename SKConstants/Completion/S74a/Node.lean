module

public import SKConstants.Completion.Blueprint5a.Statements
public import SKConstants.ScalarProcessLagTailMoments
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators Topology

namespace SKConstants.Completion.S74a

variable {U : Type*} [MeasurableSpace U] {μ : Measure U} [IsProbabilityMeasure μ]
  {X : U → ℝ} {v : ℝ}

lemma gaussianTail_evenMoments (hv : 0 < v) (hX : Measurable X)
    (htail : ∀ ε : ℝ, 0 ≤ ε → μ.real {w | ε ≤ |X w|} ≤
      2 * Real.exp (-(ε ^ 2) / (2 * v))) (p : ℕ) :
    Integrable (fun w => X w ^ (2 * p)) μ ∧
      (∫ w, X w ^ (2 * p) ∂μ) ≤ 2 * (p.factorial : ℝ) * (2 * v) ^ p := by
  cases p with
  | zero => simp
  | succ k =>
    have hsquare : ∀ x : ℝ, 0 ≤ x →
        μ.real {w | x ≤ |X w ^ 2|} ≤ 2 * Real.exp (-(x / (2 * v))) := by
      intro x hx
      have hset : {w | x ≤ |X w ^ 2|} = {w | Real.sqrt x ≤ |X w|} := by
        ext w
        simp only [mem_ofPred_eq, Real.sqrt_le_iff, abs_nonneg, true_and,
          sq_abs, abs_of_nonneg (sq_nonneg (X w))]
      rw [hset]
      simpa only [Real.sq_sqrt hx, neg_div] using htail (Real.sqrt x) (Real.sqrt_nonneg x)
    have hm := SKConstants.factorial_moment_le_of_exponential_tail μ
      (fun w => X w ^ 2) (hX.pow_const 2) 2 (2 * v) (by norm_num) (by positivity) hsquare k
    simpa only [abs_pow, sq_abs, ← pow_mul] using hm

lemma evenMoments_cosh (hv : 0 ≤ v)
    (hMom : ∀ p : ℕ, Integrable (fun w => X w ^ (2 * p)) μ ∧
      (∫ w, X w ^ (2 * p) ∂μ) ≤ 2 * (p.factorial : ℝ) * (2 * v) ^ p)
    (t : ℝ) :
    Integrable (fun w => Real.cosh (t * X w)) μ ∧
      (∫ w, Real.cosh (t * X w) ∂μ) ≤ 2 * Real.exp (2 * v * t ^ 2) - 1 := by
  let F : ℕ → U → ℝ := fun p w => (t * X w) ^ (2 * p) / ((2 * p).factorial : ℝ)
  let G : ℕ → ℝ := fun p => 2 * (2 * v * t ^ 2) ^ p / (p.factorial : ℝ)
  have hFInt (p : ℕ) : Integrable (F p) μ := by
    simpa only [F, mul_pow, mul_div_assoc] using
      ((hMom p).1.const_mul (t ^ (2 * p))).div_const ((2 * p).factorial : ℝ)
  have hFnonneg (p : ℕ) (w : U) : 0 ≤ F p w := by
    dsimp only [F]
    rw [pow_mul]
    positivity
  have hTerm (p : ℕ) : (∫ w, F p w ∂μ) ≤ G p := by
    have hfacN : p.factorial * p.factorial ≤ (2 * p).factorial := by
      simpa only [two_mul] using
        Nat.le_of_dvd (Nat.factorial_pos (p + p))
          (Nat.factorial_mul_factorial_dvd_factorial_add p p)
    have hfac : (p.factorial : ℝ) * (p.factorial : ℝ) ≤ ((2 * p).factorial : ℝ) := by
      exact_mod_cast hfacN
    have hff : 0 < (p.factorial : ℝ) := by positivity
    have hf2 : 0 < ((2 * p).factorial : ℝ) := by positivity
    calc
      _ = (t ^ (2 * p) / ((2 * p).factorial : ℝ)) * (∫ w, X w ^ (2 * p) ∂μ) := by
        simp only [F, mul_pow, integral_div, integral_const_mul]
        ring
      _ ≤ (t ^ (2 * p) / ((2 * p).factorial : ℝ)) *
          (2 * (p.factorial : ℝ) * (2 * v) ^ p) :=
        mul_le_mul_of_nonneg_left (hMom p).2 (by rw [pow_mul]; positivity)
      _ = (2 * (2 * v * t ^ 2) ^ p) *
          ((p.factorial : ℝ) / ((2 * p).factorial : ℝ)) := by
        rw [mul_pow, pow_mul]
        ring
      _ ≤ (2 * (2 * v * t ^ 2) ^ p) * (1 / (p.factorial : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (div_le_div_iff₀ hf2 hff).mpr (by simpa using hfac)
      _ = G p := by dsimp [G]; ring
  have hGS : HasSum G (2 * Real.exp (2 * v * t ^ 2)) := by
    have hh : HasSum (fun p : ℕ => (2 * v * t ^ 2) ^ p / (p.factorial : ℝ))
        (Real.exp (2 * v * t ^ 2)) := by
      simpa only [Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp (2 * v * t ^ 2))
    convert hh.mul_left (2 : ℝ) using 1
    funext p
    dsimp [G]
    ring
  have hNorm : Summable (fun p => ∫ w, ‖F p w‖ ∂μ) := by
    apply hGS.summable.of_nonneg_of_le
      (fun p => integral_nonneg (fun w => norm_nonneg _))
    intro p
    have hn : (fun w => ‖F p w‖) = F p := by
      funext w
      exact Real.norm_of_nonneg (hFnonneg p w)
    rw [hn]
    exact hTerm p
  have hSI := hasSum_integral_of_summable_integral_norm hFInt hNorm
  have hCosh : (fun w => ∑' p, F p w) = fun w => Real.cosh (t * X w) := by
    funext w
    exact (Real.hasSum_cosh (t * X w)).tsum_eq
  have hSum : (∫ w, Real.cosh (t * X w) ∂μ) = ∑' p, ∫ w, F p w ∂μ := by
    rw [← hCosh]
    exact hSI.tsum_eq.symm
  have hTail := (summable_nat_add_iff 1).mpr hSI.summable
  have hGTail := (summable_nat_add_iff 1).mpr hGS.summable
  have hTailLe := hTail.tsum_le_tsum (fun p => hTerm (p + 1)) hGTail
  have hSplitF := hSI.summable.sum_add_tsum_nat_add 1
  have hSplitG := hGS.summable.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, F, mul_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, integral_const, probReal_univ, smul_eq_mul, mul_one] at hSplitF
  simp only [Finset.sum_range_one, G, pow_zero, mul_one, Nat.factorial_zero,
    Nat.cast_one, div_one] at hSplitG
  rw [hGS.tsum_eq] at hSplitG
  have hPositive : 0 < ∫ w, Real.cosh (t * X w) ∂μ := by
    have hnn : 0 ≤ ∑' p, ∫ w, F (p + 1) w ∂μ :=
      tsum_nonneg (fun p => integral_nonneg (hFnonneg (p + 1)))
    rw [hSum]
    linarith
  refine ⟨Integrable.of_integral_ne_zero (ne_of_gt hPositive), ?_⟩
  rw [hSum]
  linarith

lemma centered_mgf_le_cosh (hX : Measurable X)
    (hCosh : ∀ t : ℝ, Integrable (fun w => Real.cosh (t * X w)) μ) (t : ℝ) :
    Integrable (fun w => Real.exp (t * (X w - ∫ w', X w' ∂μ))) μ ∧
      mgf (fun w => X w - ∫ w', X w' ∂μ) μ t ≤
        ∫ w, Real.cosh ((2 * t) * X w) ∂μ := by
  have hExp (s : ℝ) : Integrable (fun w => Real.exp (s * X w)) μ := by
    apply ((hCosh s).const_mul 2).mono' (by fun_prop)
    filter_upwards with w
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.cosh_eq]
    linarith [Real.exp_pos (-(s * X w))]
  have hXI : Integrable X μ := by
    simpa only [pow_one] using integrable_pow_of_integrable_exp_mul
      (by norm_num : (1 : ℝ) ≠ 0) (hExp 1) (hExp (-1)) 1
  let m : ℝ := ∫ w, X w ∂μ
  have hCenter : Integrable (fun w => Real.exp (t * (X w - m))) μ := by
    simpa only [mul_sub, Real.exp_sub] using (hExp t).div_const (Real.exp (t * m))
  have hYoung (w : U) : Real.exp (t * (X w - m)) ≤
      (Real.exp ((2 * t) * X w) + Real.exp (-(2 * t) * m)) / 2 := by
    have he : Real.exp (t * (X w - m)) =
        Real.exp (t * X w) * Real.exp (-t * m) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have he1 : Real.exp ((2 * t) * X w) = Real.exp (t * X w) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have he2 : Real.exp (-(2 * t) * m) = Real.exp (-t * m) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [he, he1, he2]
    nlinarith [sq_nonneg (Real.exp (t * X w) - Real.exp (-t * m))]
  have hBoundInt : Integrable (fun w =>
      (Real.exp ((2 * t) * X w) + Real.exp (-(2 * t) * m)) / 2) μ :=
    ((hExp (2 * t)).add (integrable_const _)).div_const 2
  have hBound := integral_mono hCenter hBoundInt hYoung
  rw [integral_div, integral_add (hExp (2 * t)) (integrable_const _)] at hBound
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hBound
  have hJ := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ (fun _ => mem_univ _)) (hXI.const_mul (-(2 * t))) (hExp (-(2 * t)))
  rw [integral_const_mul] at hJ
  have hCosheq : (∫ w, Real.cosh ((2 * t) * X w) ∂μ) =
      (mgf X μ (2 * t) + mgf X μ (-(2 * t))) / 2 := by
    simp only [Real.cosh_eq]
    rw [integral_div]
    have hi : Integrable (fun w => Real.exp (-((2 * t) * X w))) μ := by
      simpa only [neg_mul] using hExp (-(2 * t))
    rw [integral_add (hExp (2 * t)) hi]
    simp only [mgf, neg_mul]
  refine ⟨hCenter, ?_⟩
  rw [hCosheq]
  change (∫ w, Real.exp (t * (X w - m)) ∂μ) ≤ _
  change Real.exp (-(2 * t) * m) ≤ mgf X μ (-(2 * t)) at hJ
  change (∫ w, Real.exp (t * (X w - m)) ∂μ) ≤
    (mgf X μ (2 * t) + Real.exp (-(2 * t) * m)) / 2 at hBound
  linarith

theorem gaussianTail_centered_mgf (hv : 0 < v) (hX : Measurable X)
    (htail : ∀ ε : ℝ, 0 ≤ ε → μ.real {w | ε ≤ |X w|} ≤
      2 * Real.exp (-(ε ^ 2) / (2 * v))) (t : ℝ) :
    Integrable (fun w => Real.exp (t * (X w - ∫ w', X w' ∂μ))) μ ∧
      mgf (fun w => X w - ∫ w', X w' ∂μ) μ t ≤ Real.exp (16 * v * t ^ 2) := by
  have hCosh := evenMoments_cosh hv.le (gaussianTail_evenMoments hv hX htail)
  have hCenter := centered_mgf_le_cosh hX (fun s => (hCosh s).1) t
  refine ⟨hCenter.1, ?_⟩
  calc
    _ ≤ ∫ w, Real.cosh ((2 * t) * X w) ∂μ := hCenter.2
    _ ≤ 2 * Real.exp (2 * v * (2 * t) ^ 2) - 1 := (hCosh (2 * t)).2
    _ ≤ Real.exp (2 * (2 * v * (2 * t) ^ 2)) := by
      have he : Real.exp (2 * (2 * v * (2 * t) ^ 2)) =
          Real.exp (2 * v * (2 * t) ^ 2) ^ 2 := by
        rw [pow_two (Real.exp (2 * v * (2 * t) ^ 2)), ← Real.exp_add]
        congr 1
        ring
      rw [he]
      nlinarith [sq_nonneg (Real.exp (2 * v * (2 * t) ^ 2) - 1)]
    _ = Real.exp (16 * v * t ^ 2) := by congr 1; ring

end SKConstants.Completion.S74a

namespace SKConstants.Blueprint5a

theorem signSymmetrization_holds : SignSymmetrizationStatement := by
  intro U _ μ _ X v hv hX htail radius
  constructor
  · intro t _
    exact (Completion.S74a.gaussianTail_centered_mgf hv hX htail t).1
  · intro t _
    apply (Completion.S74a.gaussianTail_centered_mgf hv hX htail t).2.trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hv.le (sq_nonneg t)]

end SKConstants.Blueprint5a
