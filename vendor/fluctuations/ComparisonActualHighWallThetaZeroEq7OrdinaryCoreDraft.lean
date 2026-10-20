module

public import ComparisonConditionalOptimizedSize
public import ComparisonConditionalErrorSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 12000000

theorem comparison_eq7_ordinary_optimized_core_draft
    {N delta E lam e K M y Y q : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hlam : 0 < lam)
    (he : 0 < e) (hK : 1 ≤ K)
    (hstrength : N^(-delta)*lam ≤ K*e)
    (hM : comparisonSmallMass N E ≤ M)
    (hy : 0 ≤ y) (hY : 0 ≤ Y)
    (hyA : y ≤ Y*comparisonConditionalScale N delta E lam)
    (hq : 1 ≤ q) :
    lam*M*(2*((q^2*y)/(N*e*M^2))^((2:ℝ)/3)) ≤
      2*(q^2*Y*K)^((2:ℝ)/3)*N^(4*delta/3)*E := by
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hMp : 0 < M := (comparisonSmallMass_pos hN hE).trans_le hM
  have hq0 : 0 ≤ q^2 := sq_nonneg q
  have hC : 0 ≤ q^2*Y*K := by positivity
  have hy' : 0 ≤ q^2*K*y := by positivity
  have hyA' : q^2*K*y ≤
      (q^2*Y*K)*comparisonConditionalScale N delta E lam := by
    have H := mul_le_mul_of_nonneg_left hyA
      (show 0 ≤ q^2*K by positivity)
    nlinarith only [H]
  have H := comparison_conditional_inner_optimized_enlarged
    hN hE hlam hstrength hM hy' hC hyA'
  have heq : (q^2*K*y)/(N*(K*e)*M^2) =
      (q^2*y)/(N*e*M^2) := by
    field_simp [hN.ne',he.ne',hKp.ne',hMp.ne']
    <;> ring
  rw [heq] at H
  have H2 := mul_le_mul_of_nonneg_left H
    (by norm_num : (0:ℝ) ≤ 2)
  nlinarith only [H2]

theorem comparison_eq7_ordinary_inverse_core_draft
    {N delta E lam e K M : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hlam : 0 < lam)
    (he : 0 < e) (hK : 1 ≤ K)
    (hstrength : N^(-delta)*lam ≤ K*e)
    (hM : comparisonSmallMass N E ≤ M) :
    lam*M*(3/(N*e*M^2)) ≤ 3*K*N^delta*E := by
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hMp : 0 < M := (comparisonSmallMass_pos hN hE).trans_le hM
  have H := comparison_conditional_inverse_trace_cost
    hN hE hlam hstrength hM
  have heq : lam*M*(3/(N*e*M^2)) =
      3*K*(lam/(N*(K*e)*M)) := by
    field_simp [hN.ne',he.ne',hKp.ne',hMp.ne']
    <;> ring
  rw [heq]
  have H3 := mul_le_mul_of_nonneg_left H
    (show 0 ≤ 3*K by positivity)
  nlinarith only [H3]

end OAI.SKFluctuations.LaplaceWindowFormalization
