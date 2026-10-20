module

public import ComparisonActualHighWallThetaZeroBroadBudgets
public import ComparisonActualHighWallMesoscopicBroadNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
section Radius
variable (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)

theorem high_mass_scale_critical_lower
    (hC0 : 0 < C0) :
    (1/C0)*a.data.N^(-(1:ℝ)/6+m) ≤ a.xs := by
  have Hupper : a.data.E ≤ a.data.d^2/Real.sqrt a.data.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr a.data.hN)).mpr (by simpa only [mul_comm] using a.hupper)
  have Hlower : (1/C0)*a.data.N^(-(2:ℝ)/3+m)*a.data.d ≤ a.data.E := by
    have H := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using a.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  exact (comparison_parent_scale_lower_bounds a.data.hN (one_div_pos.mpr hC0)
    a.data.hd Hlower Hupper).2.2.trans a.hscale

theorem high_mass_inverse_power (hC0 : 0 < C0) (k : ℕ) :
    1/(a.data.N^((k:ℝ)/6)*a.xs^k) ≤ C0^k*a.data.N^(-(k:ℝ)*m):=
  mass_critical_inverse_power a.data.hN a.hxs hC0 (a.high_mass_scale_critical_lower hC0) k

end Radius

theorem high_mass_inverse_four_coarse
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hC0 : 0 < C0) (hN : 1 ≤ a.data.N) :
    1/a.xs^4 ≤ C0^4*a.data.N^4 := by
  have H:=a.high_mass_inverse_power hC0 4
  simp only [Nat.cast_ofNat,show (4:ℝ)/6=(2:ℝ)/3 by norm_num] at H
  have HH:=mul_le_mul_of_nonneg_left H (Real.rpow_nonneg a.data.hN.le ((2:ℝ)/3))
  have HE : a.data.N^((2:ℝ)/3)*(1/(a.data.N^((2:ℝ)/3)*a.xs^4))=1/a.xs^4:=by
    field_simp
  have HR : a.data.N^((2:ℝ)/3)*(C0^4*a.data.N^(-(4:ℝ)*m))=
      C0^4*a.data.N^((2:ℝ)/3-4*m):=by
    rw [show a.data.N^((2:ℝ)/3)*(C0^4*a.data.N^(-(4:ℝ)*m))=
      C0^4*(a.data.N^((2:ℝ)/3)*a.data.N^(-4*m)) by ring_nf,←Real.rpow_add a.data.hN]
    rw [show (2:ℝ)/3 + -(4:ℝ)*m=(2:ℝ)/3-4*m by ring_nf]
  rw [HE,HR] at HH
  apply HH.trans
  have Hpow:=Real.rpow_le_rpow_of_exponent_le hN (show (2:ℝ)/3-4*m ≤ 4 by linarith)
  simpa only [Real.rpow_ofNat] using mul_le_mul_of_nonneg_left Hpow (pow_nonneg hC0.le 4)

theorem mesoscopic_broad_normalization_weight_le
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hC0 : 0 < C0) (hN : 1 ≤ a.data.N)
    {c v : ℝ} (hc : 0 < c) (hxs1 : a.xs ≤ 1) (hv : 0 < v) (hvlo : c*a.xs ≤ v) :
    1/(a.xs^2*v)≤(C0^4/c)*a.data.N^4 := by
  have Hx : a.xs^4≤a.xs^3 := by
    have H:=mul_le_mul_of_nonneg_left hxs1 (show 0≤a.xs^3 by positivity [a.hxs])
    nlinarith only [H]
  have H1:=mul_le_mul_of_nonneg_left Hx hc.le
  have H2:=mul_le_mul_of_nonneg_left hvlo (sq_nonneg a.xs)
  have Hden : c*a.xs^4≤a.xs^2*v := by nlinarith only [H1,H2]
  have Hgeom : 1/(a.xs^2*v)≤(1/c)*(1/a.xs^4) := by
    have Hdirect : 1/(a.xs^2*v)≤1/(c*a.xs^4) :=
      (div_le_div_iff₀ (show 0<a.xs^2*v by positivity [a.hxs])
        (show 0<c*a.xs^4 by positivity [a.hxs])).mpr (by nlinarith only [Hden])
    convert Hdirect using 1 <;> field_simp
  have Hinv:=a.high_mass_inverse_four_coarse hm hC0 hN
  have H:=Hgeom.trans (mul_le_mul_of_nonneg_left Hinv (show 0≤1/c by positivity))
  convert H using 1 <;> ring

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
