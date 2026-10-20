module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

public section
set_option maxHeartbeats 1000000
open Filter
open scoped Topology
namespace SKConstants

theorem polynomial_stretched_decay (a t B : ℝ) (ha : 0 < a) (hB : 0 < B) :
    Tendsto (fun x : ℝ => x ^ t * Real.exp (-B * x ^ a)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (t / a) B hB).comp
    (tendsto_rpow_atTop ha)
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  change (x ^ a) ^ (t / a) * Real.exp (-B * x ^ a) =
    x ^ t * Real.exp (-B * x ^ a)
  rw [← Real.rpow_mul hx]
  have he : a * (t / a) = t := by field_simp
  rw [he]

theorem flow_bound_decay (c q d C : ℝ) (hcq : c < q) (hq : q < 1) (hd : 0 < d) :
    Tendsto (fun x : ℝ =>
      C * x * Real.exp (x ^ (1 - q) - x ^ (1 - c) / 2) + 2 * x ^ (-d))
      atTop (𝓝 0) := by
  have ha : 0 < 1 - c := by linarith
  have hr : Tendsto (fun x : ℝ => x ^ (c - q)) atTop (𝓝 0) :=
    by simpa only [neg_sub] using
      (tendsto_rpow_neg_atTop (show 0 < q - c by linarith))
  have hsmall := hr.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hpoly := polynomial_stretched_decay (1 - c) 1 (1 / 4) ha (by norm_num)
  have hmain : Tendsto
      (fun x : ℝ => x * Real.exp (x ^ (1 - q) - x ^ (1 - c) / 2))
      atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (by simpa using hpoly)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      positivity
    · filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with x hsmall hx
      have hpow : x ^ (1 - q) = x ^ (c - q) * x ^ (1 - c) := by
        rw [← Real.rpow_add hx]
        congr 1
        ring
      have hxp : 0 ≤ x ^ (1 - c) := Real.rpow_nonneg hx.le _
      have he : x ^ (1 - q) - x ^ (1 - c) / 2 ≤ -(1 / 4) * x ^ (1 - c) := by
        rw [hpow]
        nlinarith [mul_le_mul_of_nonneg_right hsmall.le hxp]
      simpa using mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hx.le
  have htail : Tendsto (fun x : ℝ => x ^ (-d)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hd
  have h := (hmain.const_mul C).add (htail.const_mul 2)
  simpa [mul_assoc] using h

theorem flow_bound_decay_nat (c q d C : ℝ) (hcq : c < q) (hq : q < 1) (hd : 0 < d) :
    Tendsto (fun n : ℕ =>
      C * (n : ℝ) * Real.exp ((n : ℝ) ^ (1 - q) - (n : ℝ) ^ (1 - c) / 2)
        + 2 * (n : ℝ) ^ (-d)) atTop (𝓝 0) := by
  exact (flow_bound_decay c q d C hcq hq hd).comp tendsto_natCast_atTop_atTop

theorem convergence_of_flow_bound (c q d C : ℝ) (hcq : c < q) (hq : q < 1)
    (hd : 0 < d) (err : ℝ → ℝ)
    (hzero : ∀ᶠ x in atTop, 0 ≤ err x)
    (hbound : ∀ᶠ x in atTop, err x ≤
      C * x * Real.exp (x ^ (1 - q) - x ^ (1 - c) / 2) + 2 * x ^ (-d)) :
    Tendsto err atTop (𝓝 0) :=
  squeeze_zero' hzero hbound (flow_bound_decay c q d C hcq hq hd)

end SKConstants
