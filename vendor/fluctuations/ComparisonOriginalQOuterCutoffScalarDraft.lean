module

public import ComparisonConditionalErrorSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter
open scoped Topology
set_option autoImplicit false

namespace OriginalQOuterCutoffDraft

theorem payload_le_fixed_linear
    {N P q y M H K : ℝ}
    (hN : 1 ≤ N) (hP0 : 0 ≤ P) (hP : P ≤ N)
    (hy0 : 0 ≤ y) (hy : y ≤ H)
    (hM0 : 0 ≤ M) (hM : M ≤ K)
    (hH : 0 ≤ H) (hK : 0 ≤ K) :
    (q^2*y)^2*P*M^2 ≤ (q^4*H^2*K^2)*N := by
  have hqY : q^2*y ≤ q^2*H :=
    mul_le_mul_of_nonneg_left hy (sq_nonneg q)
  have hqY2 := pow_le_pow_left₀
    (mul_nonneg (sq_nonneg q) hy0) hqY 2
  have hM2 := pow_le_pow_left₀ hM0 hM 2
  have hstep : (q^2*y)^2*P*M^2 ≤ (q^2*H)^2*N*K^2 := by
    gcongr
  calc
    _ ≤ (q^2*H)^2*N*K^2 := hstep
    _ = (q^4*H^2*K^2)*N := by ring

theorem cutoff_atom_of_linear_payload
    {N E delta e Z B : ℝ}
    (hN : 1 ≤ N) (hdelta : 0 ≤ delta) (hdelta2 : delta/2 ≤ 1)
    (hE : 0 ≤ E) (hEfloor : 1/N ≤ E)
    (he : 0 ≤ e) (he1 : e ≤ 1)
    (hZ : 0 ≤ Z) (hB : 0 ≤ B) (hZB : Z ≤ B*N)
    (hgate : 18*(B+3)*N^(-(29:ℝ)) ≤ N^(-(2:ℝ))) :
    e*18*(Z^((1:ℝ)/3)+2)*N^(-(30:ℝ)) ≤
      N^(-delta/2)*E := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hroot : Z^((1:ℝ)/3) ≤ Z+1 := by
    by_cases hZ1 : Z ≤ 1
    · have H := Real.rpow_le_rpow hZ hZ1
        (by norm_num : (0:ℝ) ≤ 1/3)
      calc
        Z^((1:ℝ)/3) ≤ (1:ℝ)^((1:ℝ)/3) := H
        _ = 1 := by simp
        _ ≤ Z+1 := by linarith
    · have H := Real.rpow_le_rpow_of_exponent_le
        (by linarith : 1 ≤ Z)
        (by norm_num : (1:ℝ)/3 ≤ 1)
      calc
        Z^((1:ℝ)/3) ≤ Z^(1:ℝ) := H
        _ = Z := by simp
        _ ≤ Z+1 := by linarith
  have hplus : Z^((1:ℝ)/3)+2 ≤ (B+3)*N := by
    have H3 := mul_le_mul_of_nonneg_left hN
      (by norm_num : (0:ℝ) ≤ 3)
    nlinarith only [hroot,hZB,H3]
  have hB3 : 0 ≤ B+3 := by linarith
  have hcut : e*18*(Z^((1:ℝ)/3)+2)*N^(-(30:ℝ)) ≤
      18*(B+3)*N^(-(29:ℝ)) := by
    have H := mul_le_mul hplus he1 he
      (by positivity : 0 ≤ (B+3)*N)
    have H' := mul_le_mul_of_nonneg_right H
      (show 0 ≤ 18*N^(-(30:ℝ)) by positivity)
    have Hpow : N*N^(-(30:ℝ))=N^(-(29:ℝ)) := by
      calc
        N*N^(-(30:ℝ)) = N^(1:ℝ)*N^(-(30:ℝ)) := by
          simp only [Real.rpow_one]
        _ = N^((1:ℝ)+(-(30:ℝ))) := by rw [Real.rpow_add hNp]
        _ = N^(-(29:ℝ)) := by congr 1; ring
    calc
      e*18*(Z^((1:ℝ)/3)+2)*N^(-(30:ℝ)) =
          ((Z^((1:ℝ)/3)+2)*e)*(18*N^(-(30:ℝ))) := by ring
      _ ≤ ((B+3)*N)*(18*N^(-(30:ℝ))) := by
        simpa only [mul_one] using H'
      _ = 18*(B+3)*(N*N^(-(30:ℝ))) := by ring
      _ = 18*(B+3)*N^(-(29:ℝ)) := by rw [Hpow]
  have hpow : N^(-(1:ℝ)) ≤ N^(-delta/2) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hdelta2])
  have hEfloor' : N^(-(1:ℝ)) ≤ E := by
    simpa only [Real.rpow_neg_one, one_div] using hEfloor
  have htarget : N^(-(2:ℝ)) ≤ N^(-delta/2)*E := by
    have H := mul_le_mul hpow hEfloor'
      (Real.rpow_nonneg hNp.le (-(1:ℝ)))
      (Real.rpow_nonneg hNp.le (-delta/2))
    have Heq : N^(-(1:ℝ))*N^(-(1:ℝ))=N^(-(2:ℝ)) := by
      rw [←Real.rpow_add hNp]
      congr 1
      ring
    simpa only [Heq] using H
  exact hcut.trans (hgate.trans htarget)

end OriginalQOuterCutoffDraft
end OAI.SKFluctuations.LaplaceWindowFormalization
