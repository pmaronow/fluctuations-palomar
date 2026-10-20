module

public import ComparisonNativeActualMinimumLocalDiameterBudgets
public import ComparisonNativeActualMassBudgetRates

@[expose] public section

noncomputable section
set_option maxHeartbeats 9000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators

theorem laplaceComparisonStrength_le_log_cubic
    {N d lam x : ℝ} (hN : 1 ≤ N) (hd : 0 < d) (hnd : 1/N ≤ d)
    (hlam : 0 < lam) (hld : lam ≤ d^2) (hx : 0 < x) (hx1 : x ≤ 1) :
    laplaceComparisonStrength d lam x ≤ (1+Real.log N)*d^3/x := by
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hp : 0 < d^3 := pow_pos hd 3
  have ha : 0 < lam*x/d^3 := div_pos (mul_pos hlam hx) hp
  have hnx : lam*x ≤ d^2 := by
    have H := mul_le_mul_of_nonneg_left hx1 hlam.le
    have H' : lam*x ≤ lam := by simpa only [mul_one] using H
    exact H'.trans hld
  have hdn : 1 ≤ N*d := by simpa only [mul_comm] using (div_le_iff₀ hN0).mp hnd
  have harg : lam*x/d^3 ≤ N := by
    apply (div_le_iff₀ hp).mpr
    have H := mul_le_mul_of_nonneg_right hdn (sq_nonneg d)
    nlinarith
  change lam*laplaceComparisonShape (lam*x/d^3) ≤ _
  by_cases hflat : lam*x/d^3 ≤ 1
  · rw [laplaceComparisonShape,ite_eq_left hflat,mul_one]
    have H : lam*x ≤ d^3 := by simpa only [one_mul] using (div_le_iff₀ hp).mp hflat
    apply (le_div_iff₀ hx).mpr
    have HD := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ 1+Real.log N by linarith) hp.le
    nlinarith
  · rw [laplaceComparisonShape,ite_eq_right hflat]
    have HL : Real.log (lam*x/d^3) ≤ Real.log N := Real.log_le_log ha harg
    have HE : lam*((1+Real.log (lam*x/d^3))/(lam*x/d^3)) =
        (1+Real.log (lam*x/d^3))*d^3/x := by field_simp
    rw [HE]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : 1+Real.log (lam*x/d^3) ≤ 1+Real.log N) hp.le) hx.le

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_mass_energy_cubic_le_test
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.context.N) (hnd : 1/a.context.N ≤ a.context.d)
    (hCt : 0 ≤ Ct) (hxs1 : a.xs ≤ 1) :
    a.context.E/a.context.d^3 ≤ Ct*(1+Real.log a.context.N)*a.xs*a.context.U := by
  have hE := a.context.hE
  have hd := a.context.hd
  have hN0 := a.context.hN
  have HG := laplaceComparisonStrength_le_log_cubic hN a.context.hd hnd a.hlam a.hld a.hxs hxs1
  have H := a.htest.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left HG hCt) (sq_nonneg a.xs))
  have HE : a.context.N*a.context.E^2 ≤ Ct*(1+Real.log a.context.N)*a.context.d^3*a.xs := by
    convert H using 1
    field_simp
  have Hmul := mul_le_mul_of_nonneg_right HE
    (show 0 ≤ 1/(a.context.N*a.context.E) by positivity)
  apply (div_le_iff₀ (pow_pos a.context.hd 3)).mpr
  change a.context.E ≤ Ct*(1+Real.log a.context.N)*a.xs*
    (1/(a.context.N*a.context.E))*a.context.d^3
  convert Hmul using 1 <;> field_simp [hN0.ne',hE.ne']

def canonicalPositiveOuterBroadMassDiameter
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (v : ℝ) : ℝ :=
  9*Real.log a.context.N*(32*cu^3/cl^3)*a.context.E/
    (a.context.N^delta*a.context.d^3*v)

theorem canonical_outer_broad_mass_diameter_le_positive
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (_hlog : 0 ≤ Real.log a.context.N) (v : ℝ) :
    a.canonicalOuterBroadMassDiameter v ≤ a.canonicalPositiveOuterBroadMassDiameter v := by
  unfold canonicalOuterBroadMassDiameter canonicalPositiveOuterBroadMassDiameter
  have H := mul_le_mul_of_nonneg_left
    (min_le_right a.cavityCapTravel ((32*cu^3/cl^3)*a.context.E/(a.context.N^delta*a.context.d^3*v)))
    (show 0 ≤ 9*Real.log a.context.N by positivity)
  convert H using 1
  ring

theorem canonical_local_mass_diameter_pos
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hlog : 0 < Real.log a.context.N) {v : ℝ} (hv : 0 < v) :
    0 < a.canonicalLocalMassDiameter v := by
  have hE := a.context.hE
  have hd := a.context.hd
  have hN := a.context.hN
  have hU := a.context.hU
  unfold canonicalLocalMassDiameter
  positivity

theorem canonical_positive_outer_broad_mass_diameter_pos
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hlog : 0 < Real.log a.context.N) (hcl : 0 < cl) (hcu : 0 < cu)
    {v : ℝ} (hv : 0 < v) :
    0 < a.canonicalPositiveOuterBroadMassDiameter v := by
  have hE := a.context.hE
  have hd := a.context.hd
  have hN := a.context.hN
  unfold canonicalPositiveOuterBroadMassDiameter
  positivity

theorem canonical_mass_diameter_source_power_le
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.context.N) (hlog : 1 ≤ Real.log a.context.N)
    (hnd : 1/a.context.N ≤ a.context.d) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    (hxs1 : a.xs ≤ 1) {A v : ℝ} (hA : 0 ≤ A) (hv : 0 < v) :
    A*Real.log a.context.N*a.context.E/(a.context.N^delta*a.context.d^3*v) ≤
      (2*A*Ct*C0^3)*(Real.log a.context.N)^2*(a.xs^2/v)*a.context.N^(-(3*m+delta)) := by
  have hN0 := a.context.hN
  have hd := a.context.hd
  have hx := a.hxs
  have hL : 0 ≤ Real.log a.context.N := zero_le_one.trans hlog
  have HE := a.canonical_mass_energy_cubic_le_test hN hnd hCt hxs1
  have HU := a.canonical_mass_small_ratio hC0
  have HL : Real.log a.context.N*(1+Real.log a.context.N) ≤ 2*(Real.log a.context.N)^2 := by nlinarith
  have HP : a.context.N^(-3*m)/a.context.N^delta=a.context.N^(-(3*m+delta)) := by
    rw [div_eq_mul_inv,←Real.rpow_neg hN0.le,←Real.rpow_add hN0]
    congr 1
    ring
  calc
    _ = (A*Real.log a.context.N/(a.context.N^delta*v))*(a.context.E/a.context.d^3) := by field_simp
    _ ≤ (A*Real.log a.context.N/(a.context.N^delta*v))*(Ct*(1+Real.log a.context.N)*a.xs*a.context.U) :=
      mul_le_mul_of_nonneg_left HE (by positivity)
    _ = (A*Ct*(Real.log a.context.N*(1+Real.log a.context.N)))*(a.context.U/a.xs)*(a.xs^2/v)/a.context.N^delta := by
      field_simp
    _ ≤ (A*Ct*(2*(Real.log a.context.N)^2))*(C0^3*a.context.N^(-3*m))*(a.xs^2/v)/a.context.N^delta := by
      gcongr
      exact div_nonneg a.context.hU.le hx.le
    _ = (2*A*Ct*C0^3)*(Real.log a.context.N)^2*(a.xs^2/v)*(a.context.N^(-3*m)/a.context.N^delta) := by ring
    _ = _ := by rw [HP]

theorem canonical_local_mass_diameter_le_high_source
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.context.N) (hlog : 1 ≤ Real.log a.context.N)
    (hnd : 1/a.context.N ≤ a.context.d) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    (hxs1 : a.xs ≤ 1) {v : ℝ} (hv : 0 < v) :
    a.canonicalLocalMassDiameter v ≤
      (1152*Ct*C0^3)*(Real.log a.context.N)^2*(a.xs^2/v)*a.context.N^(-(3*m+delta)) := by
  have hN0 := a.context.hN
  have hd := a.context.hd
  have hE := a.context.hE
  have hU := a.context.hU
  have hL : 0 ≤ Real.log a.context.N := zero_le_one.trans hlog
  have Hlocal : a.canonicalLocalMassDiameter v ≤
      576*Real.log a.context.N*a.context.E/(a.context.N^delta*a.context.d^3*v) := by
    unfold canonicalLocalMassDiameter
    have Hden : a.context.N^delta*a.context.d^3*(v/2) ≤
        a.context.N^delta*a.context.d^3*(v/2+a.context.U) := by gcongr; linarith
    have H := div_le_div_of_nonneg_left
      (show 0 ≤ 9*Real.log a.context.N*32*a.context.E by positivity)
      (show 0 < a.context.N^delta*a.context.d^3*(v/2) by positivity) Hden
    apply H.trans_eq
    field_simp
    ring
  have H := a.canonical_mass_diameter_source_power_le hN hlog hnd hCt hC0 hxs1
    (A:=576) (by norm_num) hv
  norm_num only at H
  exact Hlocal.trans H

theorem canonical_positive_outer_broad_mass_diameter_le_high_source
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.context.N) (hlog : 1 ≤ Real.log a.context.N)
    (hnd : 1/a.context.N ≤ a.context.d) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    (hxs1 : a.xs ≤ 1) (hcl : 0 < cl) (hcu : 0 < cu) {v : ℝ} (hv : 0 < v) :
    a.canonicalPositiveOuterBroadMassDiameter v ≤
      (576*Ct*C0^3*cu^3/cl^3)*(Real.log a.context.N)^2*(a.xs^2/v)*a.context.N^(-(3*m+delta)) := by
  have H := a.canonical_mass_diameter_source_power_le hN hlog hnd hCt hC0 hxs1
    (A:=288*cu^3/cl^3) (by positivity) hv
  unfold canonicalPositiveOuterBroadMassDiameter
  convert H using 1 <;> field_simp <;> ring

theorem canonical_outer_broad_mass_diameter_le_high_source
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.context.N) (hlog : 1 ≤ Real.log a.context.N)
    (hnd : 1/a.context.N ≤ a.context.d) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    (hxs1 : a.xs ≤ 1) (hcl : 0 < cl) (hcu : 0 < cu) {v : ℝ} (hv : 0 < v) :
    a.canonicalOuterBroadMassDiameter v ≤
      (576*Ct*C0^3*cu^3/cl^3)*(Real.log a.context.N)^2*(a.xs^2/v)*a.context.N^(-(3*m+delta)) :=
  (a.canonical_outer_broad_mass_diameter_le_positive (zero_le_one.trans hlog) v).trans
    (a.canonical_positive_outer_broad_mass_diameter_le_high_source hN hlog hnd hCt hC0 hxs1 hcl hcu hv)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
