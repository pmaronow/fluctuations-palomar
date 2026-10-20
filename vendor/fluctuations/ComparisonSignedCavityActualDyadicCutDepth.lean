module

public import ComparisonSignedCavityActualBufferDyadicCount
public import ComparisonPhysicalDyadicSum
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy Cavity
open scoped Topology BigOperators
set_option maxHeartbeats 8000000

def nativeDyadicCutDepth (a : ℝ) : ℕ := Nat.ceil (Real.logb 2 a⁻¹)+1

theorem nativeDyadicCutDepth_pos (a : ℝ) : 0 < nativeDyadicCutDepth a := by
  unfold nativeDyadicCutDepth
  omega

theorem nativeDyadicCutDepth_le_two_add_logb {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (nativeDyadicCutDepth a:ℝ) ≤ 2+Real.logb 2 a⁻¹ := by
  have hinv : 1 ≤ a⁻¹:=(one_le_inv₀ ha).mpr ha1
  have H:=Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1:ℝ) < 2) hinv)
  dsimp only [nativeDyadicCutDepth]
  push_cast
  linarith

theorem nativeDyadicCutDepth_one_le_two_pow_mul_half {a : ℝ} (ha : 0 < a) :
    1 ≤ (2:ℝ)^nativeDyadicCutDepth a*(a/2) := by
  have HC:=Nat.le_ceil (Real.logb 2 a⁻¹)
  have HR:=(Real.logb_le_iff_le_rpow (by norm_num : (1:ℝ) < 2) (inv_pos.mpr ha)).mp HC
  rw [Real.rpow_natCast] at HR
  have HM:=mul_le_mul_of_nonneg_right HR ha.le
  rw [inv_mul_cancel₀ ha.ne'] at HM
  dsimp only [nativeDyadicCutDepth]
  rw [pow_succ]
  nlinarith

theorem nativeDyadicCutDepth_le_log_of_polynomial_lower {a N exponent : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hN : 0 < N) (hlog : 1 ≤ Real.log N)
    (hlower : N^(-exponent) ≤ a) :
    (nativeDyadicCutDepth a:ℝ) ≤ (2+exponent/Real.log 2)*Real.log N := by
  have H:=nativeDyadicCutDepth_le_two_add_logb ha ha1
  have Hlog:=Real.log_le_log (Real.rpow_pos_of_pos hN (-exponent)) hlower
  rw [Real.log_rpow hN] at Hlog
  have Hdiv:=div_le_div_of_nonneg_right (neg_le_neg Hlog)
    (Real.log_pos (by norm_num : (1:ℝ) < 2)).le
  rw [Real.logb,Real.log_inv] at H
  have HE : -(-exponent*Real.log N)/Real.log 2=exponent/Real.log 2*Real.log N:=by ring
  rw [HE] at Hdiv
  nlinarith only [H,Hdiv,hlog]

theorem native_dyadic_layer_sum_le {a B : ℝ} (cost : ℕ → ℝ)
    (H : ∀j < nativeDyadicCutDepth a,cost j ≤ B) :
    ((List.range (nativeDyadicCutDepth a)).map cost).sum ≤ (nativeDyadicCutDepth a:ℝ)*B := by
  apply (List.sum_le_sum (fun j hj=>H j (List.mem_range.mp hj))).trans_eq
  simp

end OAI.SKFluctuations.LaplaceWindowFormalization
