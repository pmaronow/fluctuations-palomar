module
public import SKConstants.SubGaussianSquares
import Mathlib.Tactic

@[expose] public section
noncomputable section
open Real
set_option backward.isDefEq.respectTransparency false
namespace SKConstants.Concentration

def squareVarianceCutoff (k s : ℝ) : ℝ :=
  4 * k * max 0 (Real.log (2 * Real.exp 1 * k / s))

def squareVarianceScale (k s : ℝ) : ℝ :=
  max s (max (2 * Real.exp 1 * k) (squareVarianceCutoff k s))

lemma square_truncated_moment_cutoff_bound
    {k s a B : ℝ} (hk : 0 < k) (hs : 0 < s) (ha : 0 ≤ a) (hB : 0 < B)
    (_hsB : s ≤ B) (haB : a ≤ B) (hkB : 2 * Real.exp 1 * k ≤ B)
    (hCutoff : (2 * Real.exp 1 * k) * Real.exp (-a / (4 * k)) ≤ s)
    (p : ℕ) (hp : 1 ≤ p) :
    s * a ^ (p - 1) +
        2 * (p.factorial : ℝ) * (2 * Real.exp 1 * k) ^ p *
          Real.exp (-a / (4 * k)) ≤
      3 * s * (p.factorial : ℝ) * B ^ (p - 1) := by
  have hpos : 0 ≤ 2 * Real.exp 1 * k := by positivity
  have hfac : 1 ≤ (p.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos p
  have hpow : p - 1 + 1 = p := by omega
  have hlow : s * a ^ (p - 1) ≤ s * (p.factorial : ℝ) * B ^ (p - 1) := by
    calc
      _ ≤ s * B ^ (p - 1) := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg hs.le (pow_nonneg hB.le (p - 1))]
  have hhigh : (2 * Real.exp 1 * k) ^ p * Real.exp (-a / (4 * k)) ≤
      s * B ^ (p - 1) := by
    calc
      _ = (2 * Real.exp 1 * k) ^ (p - 1) *
          ((2 * Real.exp 1 * k) * Real.exp (-a / (4 * k))) := by
        conv_lhs => rw [← hpow, pow_succ]
        ring
      _ ≤ (2 * Real.exp 1 * k) ^ (p - 1) * s :=
        mul_le_mul_of_nonneg_left hCutoff (pow_nonneg hpos _)
      _ ≤ B ^ (p - 1) * s := by gcongr
      _ = _ := by ring
  have hhigh' := mul_le_mul_of_nonneg_left hhigh
    (show 0 ≤ 2 * (p.factorial : ℝ) by positivity)
  nlinarith

lemma squareVarianceCutoff_nonneg {k s : ℝ} (hk : 0 < k) :
    0 ≤ squareVarianceCutoff k s := by
  unfold squareVarianceCutoff
  exact mul_nonneg (by positivity) (le_max_left _ _)

lemma squareVarianceScale_pos {k s : ℝ} (hs : 0 < s) :
    0 < squareVarianceScale k s :=
  hs.trans_le (le_max_left _ _)

lemma squareVarianceScale_second_le (k s : ℝ) : s ≤ squareVarianceScale k s :=
  le_max_left _ _

lemma squareVarianceScale_cutoff_le (k s : ℝ) :
    squareVarianceCutoff k s ≤ squareVarianceScale k s :=
  (le_max_right _ _).trans (le_max_right _ _)

lemma squareVarianceScale_gaussian_le (k s : ℝ) :
    2 * Real.exp 1 * k ≤ squareVarianceScale k s :=
  (le_max_left _ _).trans (le_max_right _ _)

lemma squareVarianceCutoff_exponential_bound {k s : ℝ} (hk : 0 < k) (hs : 0 < s) :
    (2 * Real.exp 1 * k) * Real.exp (-squareVarianceCutoff k s / (4 * k)) ≤ s := by
  have hr : 0 < 2 * Real.exp 1 * k / s := by positivity
  have hnorm : -squareVarianceCutoff k s / (4 * k) =
      -max 0 (Real.log (2 * Real.exp 1 * k / s)) := by
    unfold squareVarianceCutoff
    field_simp
  rw [hnorm]
  calc
    _ ≤ (2 * Real.exp 1 * k) * Real.exp (-Real.log (2 * Real.exp 1 * k / s)) := by
      gcongr
      exact le_max_right _ _
    _ = s := by
      rw [Real.exp_neg, Real.exp_log hr]
      field_simp

lemma squareVarianceCutoff_conditions {k s : ℝ} (hk : 0 < k) (hs : 0 < s) :
    0 ≤ squareVarianceCutoff k s ∧
      0 < squareVarianceScale k s ∧
      s ≤ squareVarianceScale k s ∧
      squareVarianceCutoff k s ≤ squareVarianceScale k s ∧
      2 * Real.exp 1 * k ≤ squareVarianceScale k s ∧
      (2 * Real.exp 1 * k) * Real.exp (-squareVarianceCutoff k s / (4 * k)) ≤ s :=
  ⟨squareVarianceCutoff_nonneg hk, squareVarianceScale_pos hs,
    squareVarianceScale_second_le k s, squareVarianceScale_cutoff_le k s,
    squareVarianceScale_gaussian_le k s, squareVarianceCutoff_exponential_bound hk hs⟩

lemma square_truncated_moment_logarithmic_cutoff_bound
    {k s : ℝ} (hk : 0 < k) (hs : 0 < s) (p : ℕ) (hp : 1 ≤ p) :
    s * squareVarianceCutoff k s ^ (p - 1) +
        2 * (p.factorial : ℝ) * (2 * Real.exp 1 * k) ^ p *
          Real.exp (-squareVarianceCutoff k s / (4 * k)) ≤
      3 * s * (p.factorial : ℝ) * squareVarianceScale k s ^ (p - 1) :=
  square_truncated_moment_cutoff_bound hk hs (squareVarianceCutoff_nonneg hk)
    (squareVarianceScale_pos hs) (squareVarianceScale_second_le k s)
    (squareVarianceScale_cutoff_le k s) (squareVarianceScale_gaussian_le k s)
    (squareVarianceCutoff_exponential_bound hk hs) p hp

lemma squareVarianceScale_one_le {k : ℝ} (hk : 1 ≤ k) :
    squareVarianceScale k 1 ≤
      k * (1 + 2 * Real.exp 1 + 4 * Real.log (2 * Real.exp 1 * k)) := by
  have hk0 : 0 ≤ k := by linarith
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
  have harg : 1 ≤ 2 * Real.exp 1 * k := by nlinarith
  have hlog : 0 ≤ Real.log (2 * Real.exp 1 * k) := Real.log_nonneg harg
  unfold squareVarianceScale squareVarianceCutoff
  simp only [div_one, max_eq_right hlog]
  have ht0 : 0 ≤ 2 * Real.exp 1 * k := by positivity
  have hc0 : 0 ≤ 4 * k * Real.log (2 * Real.exp 1 * k) := by positivity
  have hsum : max 1 (max (2 * Real.exp 1 * k)
      (4 * k * Real.log (2 * Real.exp 1 * k))) ≤
      1 + 2 * Real.exp 1 * k + 4 * k * Real.log (2 * Real.exp 1 * k) := by
    apply max_le
    · linarith
    · apply max_le <;> linarith
  exact hsum.trans (by nlinarith)

end SKConstants.Concentration
