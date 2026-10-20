module

public import ComparisonConditionalOptimizedSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 18000000

namespace OriginalQOuterVarianceDraft

theorem literal_variance_atom_le_outer_cube_root_draft
    {N e ez v y K J H q : ℝ}
    (hN : 0 < N) (he : 0 ≤ e) (hez : 0 < ez)
    (hv : 0 < v) (hy : 0 ≤ y)
    (hK : 1 ≤ K) (hJ : 0 ≤ J) (hH : 0 ≤ H)
    (hshape : e ≤ J*ez) (hheight : y ≤ H*v) :
    e*(K*v)*(2*((q^2*y)/(N*ez*(K*v)^2))^((2:ℝ)/3)) ≤
      2*(q^2*H*J)^((2:ℝ)/3)*N^(-(2:ℝ)/3)*
        (e*v)^((1:ℝ)/3) := by
  let X := e*(K*v)*(2*((q^2*y)/(N*ez*(K*v)^2))^((2:ℝ)/3))
  let Y := 2*(q^2*H*J)^((2:ℝ)/3)*N^(-(2:ℝ)/3)*
    (e*v)^((1:ℝ)/3)
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hM : 0 < K*v := mul_pos hK0 hv
  have hbase : 0 ≤ (q^2*y)/(N*ez*(K*v)^2) := by positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have he2 := pow_le_pow_left₀ he hshape 2
  have hy2 := pow_le_pow_left₀ hy hheight 2
  have hprod := mul_le_mul he2 hy2 (sq_nonneg y)
    (sq_nonneg (J*ez))
  have hprodE := mul_le_mul_of_nonneg_left hprod he
  have hprodK := mul_le_mul_of_nonneg_left hK
    (show 0 ≤ e*(J*ez)^2*(H*v)^2 by positivity)
  have hbound : e^3*y^2 ≤ J^2*ez^2*H^2*v^2*e*K := by
    nlinarith only [hprodE,hprodK]
  have hcubeX : X^3 =
      8*q^4*e^3*y^2/(N^2*ez^2*K*v) := by
    dsimp [X]
    simp only [mul_pow]
    have hbase2 : 0 ≤ (q^2*y)/(N*ez*(K^2*v^2)) := by
      positivity
    rw [←Real.rpow_mul_natCast hbase2]
    norm_num
    field_simp [hN.ne',hez.ne',hK0.ne',hv.ne'] <;> ring
  have hcubeY : Y^3 =
      8*q^4*H^2*J^2*(e*v)/N^2 := by
    dsimp [Y]
    rw [mul_pow,mul_pow,mul_pow,
      ←Real.rpow_mul_natCast (show 0 ≤ q^2*H*J by positivity),
      ←Real.rpow_mul_natCast hN.le,
      ←Real.rpow_mul_natCast (mul_nonneg he hv.le)]
    norm_num
    field_simp [hN.ne'] <;> ring
  have hcube : X^3 ≤ Y^3 := by
    rw [hcubeX,hcubeY]
    have hden : 0 < N^2*ez^2*K*v := by positivity
    apply (div_le_iff₀ hden).mpr
    have Hbound := mul_le_mul_of_nonneg_left hbound
      (show 0 ≤ 8*q^4 by positivity)
    have htarget :
        (8*q^4*H^2*J^2*(e*v)/N^2)*(N^2*ez^2*K*v) =
          8*q^4*(J^2*ez^2*H^2*v^2*e*K) := by
      field_simp [hN.ne'] <;> ring
    rw [htarget]
    nlinarith only [Hbound]
  exact (pow_le_pow_iff_left₀ hX hY (by decide : 3 ≠ 0)).mp hcube

end OriginalQOuterVarianceDraft
end OAI.SKFluctuations.LaplaceWindowFormalization
