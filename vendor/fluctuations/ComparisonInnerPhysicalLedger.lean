module

public import ComparisonPhysicalCapScale

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option maxHeartbeats 6400000

def comparisonInnerPhysicalCore (N delta E Q C J eps : ℝ) : ℝ :=
  2*(Q^2*C)^((2:ℝ)/3)*N^(4*delta/3)*E+3*N^delta*E+
  J^2*C*N^(2*delta)*E+(2*Q)^4*J*C^2*N^(2*delta+eps)*E

theorem comparison_inner_ledger_physical_cost {l : ℕ} (hl : 2<l)
    {N delta E lam P v y D Q C J L T eps : ℝ}
    (hN : 1≤N) (hE : 0<E) (hlam : 0<lam) (hP : 0<P)
    (hstrength : N*(N^(-delta)*lam)≤P)
    (hv : comparisonSmallMass N E≤v)
    (hvA : v≤C*comparisonConditionalScale N delta E lam)
    (hy : 0<y) (hyA : y≤C*comparisonConditionalScale N delta E lam)
    (hD : 0<D) (hQ : 1≤Q) (hC : 0≤C) (hJ : 0≤J)
    (hL : 0≤L) (hLU : L≤comparisonSmallMass N E)
    (hUA : comparisonSmallMass N E≤comparisonConditionalScale N delta E lam)
    (hDJ : D≤J*L) (hratio : y/D≤N^T) (horder : T/((l:ℝ)-1)≤eps) :
    lam*v*(2*((Q^2*y)/(P*v^2))^((2:ℝ)/3)+3/(P*v^2)+D^2+
      comparisonReverseMoment l D Q y)≤comparisonInnerPhysicalCore N delta E Q C J eps := by
  let A := comparisonConditionalScale N delta E lam
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hA : 0<A := comparison_conditional_scale_pos hNp hE hlam
  have hU := comparisonSmallMass_pos hNp hE
  have hvp : 0<v := hU.trans_le hv
  have hPN : N*(P/N)=P := by field_simp
  have he : N^(-delta)*lam≤P/N := (le_div_iff₀ hNp).mpr (by nlinarith [hstrength])
  have hyQ : Q^2*y≤(Q^2*C)*A := by
    have hh := mul_le_mul_of_nonneg_left hyA (sq_nonneg Q)
    simpa only [mul_assoc] using hh
  have hopt := comparison_conditional_inner_optimized_enlarged hNp hE hlam he hv
    (mul_nonneg (sq_nonneg Q) hy.le) (mul_nonneg (sq_nonneg Q) hC) hyQ
  rw [hPN] at hopt
  have hinv := comparison_conditional_inverse_trace_cost hNp hE hlam he hv
  rw [hPN] at hinv
  have hinv' : lam*v*(3/(P*v^2))≤3*N^delta*E := by
    have heq : lam*v*(3/(P*v^2))=3*(lam/(P*v)) := by field_simp <;> ring
    rw [heq]
    nlinarith
  have hlength := comparison_conditional_inner_length_cost hNp hE hlam hC hvp.le hvA hL hLU
  have hDs : D^2≤J^2*A*L := by
    have hh := pow_le_pow_left₀ hD.le hDJ 2
    have hLA : L≤A := hLU.trans hUA
    have ht := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLA hL) (sq_nonneg J)
    nlinarith
  have hsquare : lam*v*D^2≤J^2*C*N^(2*delta)*E := by
    have hh := mul_le_mul_of_nonneg_left hDs (mul_pos hlam hvp).le
    have ht := mul_le_mul_of_nonneg_left hlength (sq_nonneg J)
    nlinarith
  have hr := comparison_reverse_polynomial_loss hl hN hD hQ hy hratio horder
  have hdy := mul_le_mul hDJ hyA hy.le (mul_nonneg hJ hL)
  have hrev : lam*v*comparisonReverseMoment l D Q y≤(2*Q)^4*J*C^2*N^(2*delta+eps)*E := by
    calc
      _≤lam*v*((2*Q)^4*D*y*N^eps) := mul_le_mul_of_nonneg_left hr (mul_pos hlam hvp).le
      _≤(2*Q)^4*J*C*N^eps*(lam*v*A*L) := by
        have hh := mul_le_mul_of_nonneg_left hdy
          (show 0≤lam*v*(2*Q)^4*N^eps by positivity)
        nlinarith
      _≤(2*Q)^4*J*C*N^eps*(C*N^(2*delta)*E) :=
        mul_le_mul_of_nonneg_left hlength (by positivity)
      _=(2*Q)^4*J*C^2*N^(2*delta+eps)*E := by
        calc
          _=(2*Q)^4*J*C^2*(N^eps*N^(2*delta))*E := by ring
          _=_ := by rw [←Real.rpow_add hNp];congr 2;ring
  unfold comparisonInnerPhysicalCore
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
