module

public import ComparisonPhysicalCapScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 7200000

theorem comparison_outer_optimized_balance {N P s v y C K : ℝ}
    (hN : 0 < N) (hP : 0 < P) (hs : 0 < s) (hv : 0 < v)
    (hy : 0 ≤ y) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hyv : y ≤ C*v) (hstrength : N*s ≤ K*P) :
    s*v*(y/(P*v^2))^((2:ℝ)/3) ≤ 
      (K*C)^((2:ℝ)/3)*N^(-(2:ℝ)/3)*(s*v)^((1:ℝ)/3) := by
  have hs2 := pow_le_pow_left₀ (mul_pos hN hs).le hstrength 2
  have hy2 := pow_le_pow_left₀ hy hyv 2
  have hprod := mul_le_mul hs2 hy2 (sq_nonneg y) (sq_nonneg (K*P))
  have hmul := mul_le_mul_of_nonneg_right hprod hs.le
  have hbase : N^2*s^3*y^2 ≤ (K*C)^2*s*v^2*P^2 := by nlinarith
  have hcube : (s*v*(y/(P*v^2))^((2:ℝ)/3))^3=s^3*y^2/(P^2*v) := by
    rw [mul_pow,←Real.rpow_mul_natCast (show 0 ≤ y/(P*v^2) by positivity)]
    norm_num
    field_simp  <;>  ring
  have hNcube : (N^(-(2:ℝ)/3))^3=1/N^2 := by
    rw [←Real.rpow_mul_natCast hN.le]
    norm_num
  have htarget : ((K*C)^((2:ℝ)/3)*N^(-(2:ℝ)/3)*(s*v)^((1:ℝ)/3))^3=
      (K*C)^2*s*v/N^2 := by
    rw [mul_pow,mul_pow,hNcube,
      ←Real.rpow_mul_natCast (mul_nonneg hK hC),←Real.rpow_mul_natCast (mul_pos hs hv).le]
    norm_num
    ring
  have hratio : s^3*y^2/(P^2*v) ≤ (K*C)^2*s*v/N^2 := by
    apply (div_le_div_iff₀ (by positivity : 0 < P^2*v) (sq_pos_of_pos hN)).mpr
    nlinarith [hbase]
  have hh : (s*v*(y/(P*v^2))^((2:ℝ)/3))^3 ≤ 
      ((K*C)^((2:ℝ)/3)*N^(-(2:ℝ)/3)*(s*v)^((1:ℝ)/3))^3 := by
    rw [hcube,htarget]
    exact hratio
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 3≠0)).mp hh

def comparisonOuterPhysicalCore (N delta m gamma E Q C K G J L eps : ℝ) : ℝ :=
  2*(K*(Q^2*C))^((2:ℝ)/3)*(1/gamma)*N^(-m)*L^((1:ℝ)/3)*E+
  3*K*E+G*J*L*N^(-delta)*E+(2*Q)^4*C*J*L*N^(eps-delta)*E

theorem comparison_outer_ledger_physical_cost {l : ℕ} (hl : 2 < l)
    {N delta m gamma E d P s v y D Q C K G J L T eps : ℝ}
    (hN : 1 ≤ N) (hgamma : 0 < gamma) (hE : 0 < E) (hd : 0 < d)
    (hlower : gamma*N^(-(2:ℝ)/3+m)*d ≤ E)
    (hP : 0 < P) (hs : 0 < s) (hv : comparisonSmallMass N E ≤ v)
    (hy : 0 < y) (hC : 0 ≤ C) (hK : 0 ≤ K) (hQ : 1 ≤ Q)
    (hyv : y ≤ C*v) (hstrength : N*s ≤ K*P)
    (hL : 0 ≤ L) (hsv : s*v ≤ d^3*L)
    (hD : 0 < D) (hG : 0 ≤ G) (hJ : 0 ≤ J)
    (hglobal : D ≤ G*v) (hlocal : D ≤ J*N^(-delta)*E/(d^3*v))
    (hratio : y/D ≤ N^T) (horder : T/((l:ℝ)-1) ≤ eps) :
    s*v*(2*((Q^2*y)/(P*v^2))^((2:ℝ)/3)+3/(P*v^2)+D^2+
      comparisonReverseMoment l D Q y) ≤ 
        comparisonOuterPhysicalCore N delta m gamma E Q C K G J L eps := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hvp : 0 < v := (comparisonSmallMass_pos hNp hE).trans_le hv
  have hyQ : Q^2*y ≤ (Q^2*C)*v := by
    have hh := mul_le_mul_of_nonneg_left hyv (sq_nonneg Q)
    simpa only [mul_assoc] using hh
  have hopt := comparison_outer_optimized_balance hNp hP hs hvp
    (mul_nonneg (sq_nonneg Q) hy.le) (mul_nonneg (sq_nonneg Q) hC) hK hyQ hstrength
  have henergy := comparison_conditional_outer_optimized_cost hNp hgamma hd hE
    (mul_pos hs hvp).le hL hsv hlower
  have henergy' := mul_le_mul_of_nonneg_left henergy (Real.rpow_nonneg (mul_nonneg hK (mul_nonneg (sq_nonneg Q) hC)) ((2:ℝ)/3))
  have hopt' : s*v*((Q^2*y)/(P*v^2))^((2:ℝ)/3) ≤ 
      (K*(Q^2*C))^((2:ℝ)/3)*(1/gamma)*N^(-m)*L^((1:ℝ)/3)*E := by
    nlinarith
  have hNv : 1 ≤ N*E*v := by
    have hh := mul_le_mul_of_nonneg_left hv (mul_pos hNp hE).le
    have heq : (N*E)*comparisonSmallMass N E=1 := by unfold comparisonSmallMass;field_simp
    rw [heq] at hh
    simpa only [mul_assoc] using hh
  have hinv : s/(P*v) ≤ K*E := by
    apply (div_le_iff₀ (mul_pos hP hvp)).mpr
    have ht := mul_le_mul_of_nonneg_left hNv (mul_nonneg hK hP.le)
    have hh := mul_le_mul_of_nonneg_right hstrength (mul_pos hE hvp).le
    nlinarith
  have hinv' : s*v*(3/(P*v^2)) ≤ 3*K*E := by
    have heq : s*v*(3/(P*v^2))=3*(s/(P*v)) := by field_simp  <;>  ring
    rw [heq]
    nlinarith
  have hlocal' := (le_div_iff₀ (mul_pos (pow_pos hd 3) hvp)).mp hlocal
  have hcap : s*v^2*D ≤ J*L*N^(-delta)*E := by
    have h1 := mul_le_mul_of_nonneg_left hlocal' (mul_pos hs hvp).le
    have h2 := mul_le_mul_of_nonneg_left hsv (show 0 ≤ J*N^(-delta)*E by positivity)
    apply le_of_mul_le_mul_right (a:=d^3) _ (pow_pos hd 3)
    nlinarith
  have hsquare : s*v*D^2 ≤ G*J*L*N^(-delta)*E := by
    have h1 := mul_le_mul_of_nonneg_left hglobal (show 0 ≤ s*v*D by positivity)
    have h2 := mul_le_mul_of_nonneg_left hcap hG
    nlinarith
  have hr := comparison_reverse_polynomial_loss hl hN hD hQ hy hratio horder
  have hrev : s*v*comparisonReverseMoment l D Q y ≤ (2*Q)^4*C*J*L*N^(eps-delta)*E := by
    calc
      _ ≤ s*v*((2*Q)^4*D*y*N^eps) := mul_le_mul_of_nonneg_left hr (mul_pos hs hvp).le
      _ ≤ (2*Q)^4*C*N^eps*(s*v^2*D) := by
        have hh := mul_le_mul_of_nonneg_left hyv (show 0 ≤ s*v*(2*Q)^4*D*N^eps by positivity)
        nlinarith
      _ ≤ (2*Q)^4*C*N^eps*(J*L*N^(-delta)*E) :=
        mul_le_mul_of_nonneg_left hcap (by positivity)
      _=(2*Q)^4*C*J*L*N^(eps-delta)*E := by
        calc
          _=(2*Q)^4*C*J*L*(N^eps*N^(-delta))*E := by ring
          _=_ := by rw [←Real.rpow_add hNp,sub_eq_add_neg]
  unfold comparisonOuterPhysicalCore
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
