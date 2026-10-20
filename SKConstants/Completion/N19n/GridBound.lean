module

public import SKConstants.Completion.N19.Grid
import Mathlib.Tactic

@[expose] public section
noncomputable section
open Filter
open scoped Topology
namespace SKConstants.Completion.N19n
open Blueprint N19
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem nat_mul_exp_neg_rpow_eventually (g : ℝ) (hg : 0 < g) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) * Real.exp (-((n : ℝ)^g)) ≤ 1/4 := by
  filter_upwards [amplification_log_le 0 g 1 (1/2) hg (by norm_num) (by norm_num),
    constant_rpow_le_small_rpow 0 g (2*Real.log 4) 1 hg (by positivity) (by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hlog hfour hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  simp only [Real.rpow_zero, mul_one, one_mul] at hlog hfour
  calc
    _ = Real.exp (Real.log n - (n : ℝ)^g) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hn0]
    _ ≤ Real.exp (-Real.log 4) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]; norm_num

theorem grid_replay_estimate_eventually (p : Parameters) (ha : 0 ≤ p.a)
    (hag : p.a < p.grid) (u k : ℝ) (hu : 0 ≤ u) (hk : 0 ≤ k) :
    ∀ᶠ n : ℕ in atTop, ∀ (q : ℕ), (q : ℝ) ≤ 8*(n : ℝ)^p.a →
      ∀ (F E : ℝ), 0 ≤ F → 0 ≤ E → F ≤ (n : ℝ)^k → E ≤ (n : ℝ)^k →
      ∀ j : ℕ,
      (n : ℝ) * (4 * (2 * ((n : ℝ)^u * |gridAngle p n (j+1)-gridAngle p n j|) * F^q +
        (n : ℝ)^u * |gridAngle p n (j+1)-gridAngle p n j|) * E)^2 ≤ 1/4 := by
  let C := u+k+1+8*k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  filter_upwards [grid_amplification_le p C hC hag,
    nat_mul_exp_neg_rpow_eventually p.grid (ha.trans_lt hag),
    eventually_ge_atTop (12 : ℕ)] with n hgrid hdec hn q hq F E hF0 hE0 hF hE j
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h12 : (12 : ℝ) ≤ n := by exact_mod_cast hn
  have hnlog : 0 ≤ Real.log n := Real.log_nonneg hnR
  have hna : 1 ≤ (n : ℝ)^p.a := Real.one_le_rpow hnR ha
  have hnk : 1 ≤ (n : ℝ)^k := Real.one_le_rpow hnR hk
  have hpow : 1 ≤ ((n : ℝ)^k)^q := one_le_pow₀ hnk
  have hfp := pow_le_pow_left₀ hF0 hF q
  have hpoweq : ((n : ℝ)^k)^q = Real.exp ((q : ℝ)*(Real.log n*k)) := by
    rw [Real.rpow_def_of_pos hn0, Real.exp_nat_mul]
  have hpref : 12*(n : ℝ)^u*(n : ℝ)^k*((n : ℝ)^k)^q ≤
      Real.exp (C*(n : ℝ)^p.a*Real.log n) := by
    calc
      _ ≤ (n : ℝ)*(n : ℝ)^u*(n : ℝ)^k*((n : ℝ)^k)^q := by gcongr
      _ = Real.exp ((u+k+1+k*q)*Real.log n) := by
        rw [← Real.exp_log hn0, Real.rpow_def_of_pos (Real.exp_pos _),
          Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, ← Real.exp_nat_mul,
          ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ hnlog
        dsimp [C]
        have h1 := mul_le_mul_of_nonneg_left hna (show 0 ≤ u+k+1 by positivity)
        have h2 := mul_le_mul_of_nonneg_left hq hk
        nlinarith
  let d := |gridAngle p n (j+1)-gridAngle p n j|
  let η := (n : ℝ)^u*d
  have hd : 0 ≤ d := abs_nonneg _
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hB0 : 0 ≤ 4*(2*η*F^q+η)*E := by positivity
  have hB : 4*(2*η*F^q+η)*E ≤ Real.exp (-((n : ℝ)^p.grid)/2) := by
    calc
      _ ≤ 4*(2*η*((n : ℝ)^k)^q+η)*(n : ℝ)^k := by gcongr
      _ ≤ 4*(2*η*((n : ℝ)^k)^q+η*((n : ℝ)^k)^q)*(n : ℝ)^k := by
        gcongr
        exact le_mul_of_one_le_right hη hpow
      _ = (12*(n : ℝ)^u*(n : ℝ)^k*((n : ℝ)^k)^q)*d := by dsimp [η]; ring
      _ ≤ Real.exp (C*(n : ℝ)^p.a*Real.log n)*d :=
        mul_le_mul_of_nonneg_right hpref hd
      _ ≤ _ := hgrid j
  calc
    _ ≤ (n : ℝ) * (Real.exp (-((n : ℝ)^p.grid)/2))^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB0 hB 2) (Nat.cast_nonneg n)
    _ = (n : ℝ) * Real.exp (-((n : ℝ)^p.grid)) := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring
    _ ≤ _ := hdec

end SKConstants.Completion.N19n
