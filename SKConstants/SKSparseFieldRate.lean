module

public import SKConstants.SKSparseFields
public import SKConstants.ConditionalGibbsAnnealed
public import SKConstants.Asymptotics
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
set_option backward.isDefEq.respectTransparency false

namespace SKConstants

theorem sparseField_entropy_bound (n r : ℕ) (hr : 0 < r) (hrn : r ≤ n) :
    Real.log (((r + 1) * (n + 1)^r : ℕ)^2 : ℝ) ≤
      4 * (r : ℝ) * Real.log (n + 1 : ℕ) := by
  have hrp : (0 : ℝ) < (r + 1 : ℕ) := by positivity
  have hnp : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hlog : Real.log (r + 1 : ℕ) ≤ Real.log (n + 1 : ℕ) :=
    Real.log_le_log hrp (by exact_mod_cast Nat.add_le_add_right hrn 1)
  have hnlog : 0 ≤ Real.log (n + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast Nat.le_add_left 1 n)
  simp only [Nat.cast_pow, Nat.cast_mul, Real.log_pow, Real.log_mul hrp.ne' (pow_pos hnp r).ne']
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  norm_num only [Nat.cast_ofNat]
  nlinarith [mul_le_mul_of_nonneg_right hrR hnlog]

theorem primitiveJointGibbs_sparseFieldBadSet_tail_of_entropy {n r : ℕ}
    (hn : 0 < n) (hr : 0 < r) (beta A : ℝ) (hA : 8 * |beta| * (r : ℝ) ≤ A)
    (hentropy : Real.log (((r + 1) * (n + 1)^r : ℕ)^2 : ℝ) ≤ A^2 / (64 * (r : ℝ))) :
    (primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).real
      (annealedSparseFieldBadSet n r A) ≤ Real.exp (-A^2 / (64 * (r : ℝ))) := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hA0 : 0 ≤ A := le_trans (by positivity) hA
  have hb := primitiveJointGibbs_sparseFieldBadSet_tail hn hr beta A (by nlinarith)
  have hv : (0 : ℝ) < (((r + 1) * (n + 1)^r : ℕ)^2 : ℝ) := by positivity
  have hhalf : A / 2 ≤ A - 4 * |beta| * (r : ℝ) := by linarith
  have hsq := mul_self_le_mul_self (show (0 : ℝ) ≤ A / 2 by positivity) hhalf
  have hs : A^2 / (32 * (r : ℝ)) ≤
      (A - 4 * |beta| * (r : ℝ))^2 / (8 * (r : ℝ)) := by
    calc
      _ = (A / 2)^2 / (8 * (r : ℝ)) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (by simpa only [pow_two] using hsq) (by positivity)
  apply hb.trans
  rw [← Real.exp_log hv, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he : A^2 / (32 * (r : ℝ)) = 2 * (A^2 / (64 * (r : ℝ))) := by ring
  rw [he] at hs
  simp only [neg_div]
  linarith

theorem power_dominates_shifted_log (a C : ℝ) (ha : 0 < a) (hC : 0 < C) :
    ∀ᶠ n : ℕ in atTop, C * Real.log ((n : ℝ) + 1) ≤ (n : ℝ)^a := by
  have hlo := (isLittleO_log_rpow_atTop ha).bound
    (show 0 < 1 / (2 * C) by positivity)
  have hp := (tendsto_rpow_atTop ha).eventually (eventually_ge_atTop (2 * C * Real.log 2))
  have hx : ∀ᶠ x : ℝ in atTop, C * Real.log (x + 1) ≤ x^a := by
    filter_upwards [hlo, hp, eventually_ge_atTop (1 : ℝ)] with x hl hp hx
    have hx0 : 0 < x := by linarith
    have hlog := Real.log_le_log (by positivity : 0 < x + 1)
      (show x + 1 ≤ 2 * x by linarith)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx0.ne'] at hlog
    have hpow : 0 ≤ x^a := Real.rpow_nonneg hx0.le _
    simp only [Real.norm_eq_abs, abs_of_nonneg hpow] at hl
    have hl' : C * Real.log x ≤ x^a / 2 := by
      have h := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hl) hC.le
      field_simp at h
      nlinarith
    nlinarith
  exact tendsto_natCast_atTop_atTop.eventually hx

def sparseFieldRadius (rho : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ)^(1 - rho)⌉₊

theorem sparseFieldRadius_bounds (rho : ℝ) (hrho : 0 ≤ rho) (hrho1 : rho ≤ 1)
    {n : ℕ} (hn : 0 < n) :
    0 < sparseFieldRadius rho n ∧ sparseFieldRadius rho n ≤ n ∧
      (sparseFieldRadius rho n : ℝ) ≤ 2 * (n : ℝ)^(1 - rho) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hp : 1 ≤ (n : ℝ)^(1 - rho) := Real.one_le_rpow hn1 (by linarith)
  refine ⟨Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hn0 _), Nat.ceil_le.mpr ?_, ?_⟩
  · have h := Real.rpow_le_rpow_of_exponent_le hn1 (show 1 - rho ≤ (1 : ℝ) by linarith)
    simpa only [Real.rpow_one] using h
  · have h := Nat.ceil_lt_add_one (Real.rpow_nonneg hn0.le (1 - rho))
    change (⌈(n : ℝ)^(1 - rho)⌉₊ : ℝ) ≤ _
    linarith

theorem sparseField_scaling_conditions (beta rho u : ℝ) (hrho : 0 < rho)
    (hrho1 : rho < 1) (hu : u < rho) :
    ∀ᶠ n : ℕ in atTop,
      0 < n ∧ 0 < sparseFieldRadius rho n ∧
      8 * |beta| * (sparseFieldRadius rho n : ℝ) ≤ (n : ℝ)^(1 - u) ∧
      Real.log (((sparseFieldRadius rho n + 1) * (n + 1)^(sparseFieldRadius rho n) : ℕ)^2 : ℝ) ≤
        ((n : ℝ)^(1 - u))^2 / (64 * (sparseFieldRadius rho n : ℝ)) := by
  have hp := ((tendsto_rpow_atTop (show 0 < rho - u by linarith)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (16 * |beta|))
  have hl := power_dominates_shifted_log (2 * (rho - u)) 1024 (by linarith) (by norm_num)
  filter_upwards [hp, hl, eventually_ge_atTop (1 : ℕ)] with n hp hl hn
  change 16 * |beta| ≤ (n : ℝ)^(rho - u) at hp
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  obtain ⟨hr, hrn, hrb⟩ := sparseFieldRadius_bounds rho hrho.le hrho1.le hn0
  have hx : 0 ≤ (n : ℝ)^(1 - rho) := Real.rpow_nonneg hnR.le _
  have he : (n : ℝ)^(1 - rho) * (n : ℝ)^(rho - u) = (n : ℝ)^(1 - u) := by
    rw [← Real.rpow_add hnR]
    congr 1
    ring
  have hm : 8 * |beta| * (sparseFieldRadius rho n : ℝ) ≤ (n : ℝ)^(1 - u) := by
    have h1 := mul_le_mul_of_nonneg_left hrb (show 0 ≤ 8 * |beta| by positivity)
    have h2 := mul_le_mul_of_nonneg_left hp hx
    rw [he] at h2
    nlinarith
  have hsq : (sparseFieldRadius rho n : ℝ)^2 ≤ 4 * ((n : ℝ)^(1 - rho))^2 := by
    have h := mul_self_le_mul_self (Nat.cast_nonneg _) hrb
    nlinarith
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hpow : ((n : ℝ)^(1 - rho))^2 * (n : ℝ)^(2 * (rho - u)) =
      ((n : ℝ)^(1 - u))^2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le, ← Real.rpow_add hnR,
      ← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    congr 1
    norm_num
    ring
  have hnum : 256 * (sparseFieldRadius rho n : ℝ)^2 * Real.log ((n : ℝ) + 1) ≤
      ((n : ℝ)^(1 - u))^2 := by
    have h1 := mul_le_mul_of_nonneg_right hsq hlog
    have h2 := mul_le_mul_of_nonneg_left hl (sq_nonneg ((n : ℝ)^(1 - rho)))
    rw [hpow] at h2
    nlinarith
  have hden : 0 < (sparseFieldRadius rho n : ℝ) := by exact_mod_cast hr
  refine ⟨hn0, hr, hm, (sparseField_entropy_bound n _ hr hrn).trans ?_⟩
  rw [le_div_iff₀ (by positivity : 0 < 64 * (sparseFieldRadius rho n : ℝ))]
  simp only [Nat.cast_add, Nat.cast_one]
  convert hnum using 1 <;> ring

theorem primitiveJointGibbs_sparseFieldBadSet_stretched_tail
    (beta rho u s : ℝ) (hrho : 0 < rho) (hrho1 : rho < 1)
    (hu : u < rho) (hs : 2 * u - rho < s) :
    ∀ᶠ n : ℕ in atTop,
      (primitiveJointGibbsLaw n beta (1 / Real.sqrt (2 * (n : ℝ)))).real
        (annealedSparseFieldBadSet n (sparseFieldRadius rho n) ((n : ℝ)^(1 - u))) ≤
        Real.exp (-(n : ℝ)^(1 - s)) := by
  have hp := ((tendsto_rpow_atTop (show 0 < s + rho - 2 * u by linarith)).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (128 : ℝ))
  filter_upwards [sparseField_scaling_conditions beta rho u hrho hrho1 hu, hp]
    with n hc hp
  obtain ⟨hn, hr, hA, he⟩ := hc
  change 128 ≤ (n : ℝ)^(s + rho - 2 * u) at hp
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hrR : (0 : ℝ) < (sparseFieldRadius rho n : ℝ) := by exact_mod_cast hr
  obtain ⟨_, _, hrb⟩ := sparseFieldRadius_bounds rho hrho.le hrho1.le hn
  have hnum : 128 * (n : ℝ)^(1 - s) ≤
      (n : ℝ)^(1 + rho - 2 * u) := by
    have h := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hnR.le (1 - s))
    rw [← Real.rpow_add hnR] at h
    calc
      _ = (n : ℝ)^(1 - s) * 128 := by ring
      _ ≤ (n : ℝ)^(1 - s + (s + rho - 2 * u)) := h
      _ = _ := by congr 1; ring
  have hpow : (n : ℝ)^(1 + rho - 2 * u) * (n : ℝ)^(1 - rho) =
      ((n : ℝ)^(1 - u))^2 := by
    rw [← Real.rpow_add hnR, ← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
    congr 1
    norm_num
    ring
  have hrate : (n : ℝ)^(1 - s) ≤
      ((n : ℝ)^(1 - u))^2 / (64 * (sparseFieldRadius rho n : ℝ)) := by
    rw [le_div_iff₀ (by positivity : 0 < 64 * (sparseFieldRadius rho n : ℝ))]
    have h1 := mul_le_mul_of_nonneg_left hrb
      (show 0 ≤ 64 * (n : ℝ)^(1 - s) by positivity)
    have h2 := mul_le_mul_of_nonneg_right hnum (Real.rpow_nonneg hnR.le (1 - rho))
    rw [hpow] at h2
    nlinarith
  apply (primitiveJointGibbs_sparseFieldBadSet_tail_of_entropy hn hr beta _ hA he).trans
  apply Real.exp_le_exp.mpr
  simpa only [neg_div] using neg_le_neg hrate

end SKConstants
