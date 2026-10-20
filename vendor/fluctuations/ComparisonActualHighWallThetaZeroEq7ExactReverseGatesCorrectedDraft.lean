module

public import ComparisonActualHighWallThetaZeroBroadBudgets
public import ComparisonActualHighWallThetaZeroCapLocalPhysical
public import ComparisonReverseInterpolationSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000

theorem comparison_eq7_post_energy_coarse_lower_draft
    {N m C0 d E : ℝ} (hN : 1 ≤ N) (hm : 0 ≤ m)
    (hC0 : 0 < C0) (hC0N : C0 ≤ N)
    (hd : 0 < d) (hd1 : d ≤ 1) (hE : 0 < E)
    (hlower : N^(-(2:ℝ)/3+m)*d ≤ C0*E) :
    N^(-(2:ℝ))*d^3 ≤ E := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hpow : N^(-(1:ℝ)) ≤ N^(-(2:ℝ)/3+m) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have hd3 : d^3 ≤ d := by
    have hd2 : d^2 ≤ 1 := pow_le_one₀ hd.le hd1
    calc
      d^3 = d*d^2 := by ring
      _ ≤ d*1 := mul_le_mul_of_nonneg_left hd2 hd.le
      _ = d := by ring
  have hpre : N^(-(1:ℝ))*d^3 ≤ C0*E := by
    have H := mul_le_mul hpow hd3 (by positivity : 0 ≤ d^3)
      (Real.rpow_nonneg hNp.le (-(2:ℝ)/3+m))
    exact H.trans hlower
  have hCE : C0*E ≤ N*E := mul_le_mul_of_nonneg_right hC0N hE.le
  have H := mul_le_mul_of_nonneg_left (hpre.trans hCE)
    (Real.rpow_nonneg hNp.le (-(1:ℝ)))
  have hpow2 : N^(-(1:ℝ))*(N^(-(1:ℝ))*d^3) =
      N^(-(2:ℝ))*d^3 := by
    rw [←mul_assoc, ←Real.rpow_add hNp]
    norm_num
  have hunit : N^(-(1:ℝ))*(N*E) = E := by
    rw [Real.rpow_neg_one, ←mul_assoc, inv_mul_cancel₀ hNp.ne', one_mul]
  rw [hpow2, hunit] at H
  exact H

theorem comparison_eq7_post_local_diameter_lower_draft
    {N delta d E v L : ℝ}
    (hN : 1 ≤ N) (hdelta : 0 ≤ delta)
    (hd : 0 < d) (hE : 0 < E)
    (hElow : N^(-(2:ℝ))*d^3 ≤ E)
    (hv : 0 < v) (hvBound : v ≤ N^(6+delta))
    (hL : 1 ≤ L) :
    N^(-(8+2*delta)) ≤ 144*L*E/(N^delta*d^3*v) := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hden : 0 < N^delta*d^3*v := by positivity
  have hpow : N^(-(8+2*delta))*N^delta*N^(6+delta) =
      N^(-(2:ℝ)) := by
    rw [←Real.rpow_add hNp, ←Real.rpow_add hNp]
    congr 1
    ring
  have H1 := mul_le_mul_of_nonneg_left hvBound
    (show 0 ≤ N^(-(8+2*delta))*N^delta by positivity)
  have H2 : N^(-(8+2*delta))*(N^delta*d^3*v) ≤
      N^(-(2:ℝ))*d^3 := by
    calc
      _ = (N^(-(8+2*delta))*N^delta*v)*d^3 := by ring
      _ ≤ (N^(-(8+2*delta))*N^delta*N^(6+delta))*d^3 :=
        mul_le_mul_of_nonneg_right (by nlinarith only [H1])
          (pow_nonneg hd.le 3)
      _ = _ := by rw [hpow]
  have H3 : N^(-(2:ℝ))*d^3 ≤ 144*L*E := by
    calc
      _ ≤ E := hElow
      _ ≤ L*E := by
        have HL := mul_le_mul_of_nonneg_right hL hE.le
        nlinarith only [HL]
      _ ≤ 144*L*E := by
        have hLE : 0 ≤ L*E := by positivity
        nlinarith only [hLE]
  exact (le_div_iff₀ hden).mpr (H2.trans H3)

theorem comparison_eq7_post_local_reverse_ratio_draft
    {N delta d E v L y : ℝ}
    (hN : 1 ≤ N) (hdelta : 0 ≤ delta)
    (hd : 0 < d) (hE : 0 < E)
    (hElow : N^(-(2:ℝ))*d^3 ≤ E)
    (hv : 0 < v) (hvBound : v ≤ N^(6+delta))
    (hL : 1 ≤ L) (hy : 0 ≤ y) (hyBound : y ≤ N^(6+delta)) :
    y/(144*L*E/(N^delta*d^3*v)) ≤ N^(14+3*delta) := by
  have hD : 0 < 144*L*E/(N^delta*d^3*v) := by positivity
  have Hlow := comparison_eq7_post_local_diameter_lower_draft
    hN hdelta hd hE hElow hv hvBound hL
  have H := comparison_reverse_ratio_of_scales
    (zero_lt_one.trans_le hN) hD hy Hlow hyBound
  have hexp : (8+2*delta)+(6+delta)=14+3*delta := by ring
  simpa only [hexp] using H

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem eq7_inner_post_exact_reverse_ratio_of_raw_gate_draft
    (hm : 0 ≤ m) (hdelta : 0 ≤ delta) (hC0 : 0 < C0)
    (hN : 1 ≤ Q.data.N) (hC0N : C0 ≤ Q.data.N)
    (hlog : 1 ≤ Real.log Q.data.N)
    (hA : Q.xs ≤ Q.data.N^(5+delta))
    {C v y : ℝ} (hC : 0 ≤ C) (hCN : C ≤ Q.data.N)
    (hv : 0 < v) (hvA : v ≤ C*Q.xs)
    (hy : 0 ≤ y) (hyN : y ≤ Q.data.N^(6+delta)) :
    y/(Q.localCapDiameter v 16) ≤ Q.data.N^(14+3*delta) := by
  have hElow := comparison_eq7_post_energy_coarse_lower_draft
    hN hm hC0 hC0N Q.data.hd Q.data.hd1 Q.data.hE Q.hlower
  have hvBound : v ≤ Q.data.N^(6+delta) := by
    have HC := mul_le_mul hCN hA Q.hxs.le
      (zero_lt_one.trans_le hN).le
    have Hpow : Q.data.N*Q.data.N^(5+delta)=
        Q.data.N^(6+delta) := by
      calc
        _ = Q.data.N^(1:ℝ)*Q.data.N^(5+delta) := by rw [Real.rpow_one]
        _ = Q.data.N^((1:ℝ)+(5+delta)) := (Real.rpow_add Q.data.hN _ _).symm
        _ = _ := by congr 1 <;> ring
    nlinarith only [hvA,HC,Hpow]
  have H := comparison_eq7_post_local_reverse_ratio_draft
    hN hdelta Q.data.hd Q.data.hE hElow hv hvBound hlog hy hyN
  convert H using 1 <;> simp only [localCapDiameter] <;> ring

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
