module

public import ComparisonNativeActualHighMassDiameter
public import SKProof.Port.ComparisonActualOriginalQLocalDiameterBudgetDefinitions
public import SKProof.Port.ComparisonActualOriginalQHighMassCriticalRates

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_mass_energy_cubic_le_test
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    (hCt : 0 ≤ Ct) (hxs1 : a.xs ≤ 1) :
    a.data.E/a.data.d^3 ≤ Ct*(1+Real.log a.data.N)*a.xs*a.data.U := by
  have hE := a.data.hE
  have hd := a.data.hd
  have hN0 := a.data.hN
  have HG := laplaceComparisonStrength_le_log_cubic hN a.data.hd hnd a.hlam a.hld a.hxs hxs1
  have H := a.htest.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left HG hCt) (sq_nonneg a.xs))
  have HE : a.data.N*a.data.E^2 ≤ Ct*(1+Real.log a.data.N)*a.data.d^3*a.xs := by
    convert H using 1
    field_simp
  have Hmul := mul_le_mul_of_nonneg_right HE
    (show 0 ≤ 1/(a.data.N*a.data.E) by positivity)
  apply (div_le_iff₀ (pow_pos a.data.hd 3)).mpr
  change a.data.E ≤ Ct*(1+Real.log a.data.N)*a.xs*
    (1/(a.data.N*a.data.E))*a.data.d^3
  convert Hmul using 1 <;> field_simp [hN0.ne',hE.ne']

def canonicalPositiveOuterBroadMassDiameter
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (v : ℝ) : ℝ :=
  9*Real.log a.data.N*(32*cu^3/cl^3)*a.data.E/
    (a.data.N^delta*a.data.d^3*v)

theorem canonical_outer_broad_mass_diameter_le_positive
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (_hlog : 0 ≤ Real.log a.data.N) (v : ℝ) :
    a.canonicalOuterBroadMassDiameter v ≤ a.canonicalPositiveOuterBroadMassDiameter v := by
  unfold canonicalOuterBroadMassDiameter canonicalPositiveOuterBroadMassDiameter
  have H := mul_le_mul_of_nonneg_left
    (min_le_right a.cavityCapTravel ((32*cu^3/cl^3)*a.data.E/(a.data.N^delta*a.data.d^3*v)))
    (show 0 ≤ 9*Real.log a.data.N by positivity)
  convert H using 1
  ring

theorem canonical_local_mass_diameter_pos
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hlog : 0 < Real.log a.data.N) {v : ℝ} (hv : 0 < v) :
    0 < a.canonicalLocalMassDiameter v := by
  have hE := a.data.hE
  have hd := a.data.hd
  have hN := a.data.hN
  have hU := a.data.hU
  unfold canonicalLocalMassDiameter
  positivity

theorem canonical_positive_outer_broad_mass_diameter_pos
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hlog : 0 < Real.log a.data.N) (hcl : 0 < cl) (hcu : 0 < cu)
    {v : ℝ} (hv : 0 < v) :
    0 < a.canonicalPositiveOuterBroadMassDiameter v := by
  have hE := a.data.hE
  have hd := a.data.hd
  have hN := a.data.hN
  unfold canonicalPositiveOuterBroadMassDiameter
  positivity

theorem canonical_mass_diameter_source_power_le
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N)
    (hnd : 1/a.data.N ≤ a.data.d) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    (hxs1 : a.xs ≤ 1) {A v : ℝ} (hA : 0 ≤ A) (hv : 0 < v) :
    A*Real.log a.data.N*a.data.E/(a.data.N^delta*a.data.d^3*v) ≤
      (2*A*Ct*C0^3)*(Real.log a.data.N)^2*(a.xs^2/v)*a.data.N^(-(3*m+delta)) := by
  have hN0 := a.data.hN
  have hd := a.data.hd
  have hx := a.hxs
  have hL : 0 ≤ Real.log a.data.N := zero_le_one.trans hlog
  have HE := a.canonical_mass_energy_cubic_le_test hN hnd hCt hxs1
  have HU := a.canonical_mass_small_ratio hC0
  have HL : Real.log a.data.N*(1+Real.log a.data.N) ≤ 2*(Real.log a.data.N)^2 := by nlinarith
  have HP : a.data.N^(-3*m)/a.data.N^delta=a.data.N^(-(3*m+delta)) := by
    rw [div_eq_mul_inv,←Real.rpow_neg hN0.le,←Real.rpow_add hN0]
    congr 1
    ring
  calc
    _ = (A*Real.log a.data.N/(a.data.N^delta*v))*(a.data.E/a.data.d^3) := by field_simp
    _ ≤ (A*Real.log a.data.N/(a.data.N^delta*v))*(Ct*(1+Real.log a.data.N)*a.xs*a.data.U) :=
      mul_le_mul_of_nonneg_left HE (by positivity)
    _ = (A*Ct*(Real.log a.data.N*(1+Real.log a.data.N)))*(a.data.U/a.xs)*(a.xs^2/v)/a.data.N^delta := by
      field_simp
    _ ≤ (A*Ct*(2*(Real.log a.data.N)^2))*(C0^3*a.data.N^(-3*m))*(a.xs^2/v)/a.data.N^delta := by
      gcongr
      exact div_nonneg a.data.hU.le hx.le
    _ = (2*A*Ct*C0^3)*(Real.log a.data.N)^2*(a.xs^2/v)*(a.data.N^(-3*m)/a.data.N^delta) := by ring
    _ = _ := by rw [HP]

theorem canonical_local_mass_diameter_le_high_source
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N)
    (hnd : 1/a.data.N ≤ a.data.d) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    (hxs1 : a.xs ≤ 1) {v : ℝ} (hv : 0 < v) :
    a.canonicalLocalMassDiameter v ≤
      (1152*Ct*C0^3)*(Real.log a.data.N)^2*(a.xs^2/v)*a.data.N^(-(3*m+delta)) := by
  have hN0 := a.data.hN
  have hd := a.data.hd
  have hE := a.data.hE
  have hU := a.data.hU
  have hL : 0 ≤ Real.log a.data.N := zero_le_one.trans hlog
  have Hlocal : a.canonicalLocalMassDiameter v ≤
      576*Real.log a.data.N*a.data.E/(a.data.N^delta*a.data.d^3*v) := by
    unfold canonicalLocalMassDiameter
    have Hden : a.data.N^delta*a.data.d^3*(v/2) ≤
        a.data.N^delta*a.data.d^3*(v/2+a.data.U) := by gcongr; linarith
    have H := div_le_div_of_nonneg_left
      (show 0 ≤ 9*Real.log a.data.N*32*a.data.E by positivity)
      (show 0 < a.data.N^delta*a.data.d^3*(v/2) by positivity) Hden
    apply H.trans_eq
    field_simp
    ring
  have H := a.canonical_mass_diameter_source_power_le hN hlog hnd hCt hC0 hxs1
    (A:=576) (by norm_num) hv
  norm_num only at H
  exact Hlocal.trans H

theorem canonical_positive_outer_broad_mass_diameter_le_high_source
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N)
    (hnd : 1/a.data.N ≤ a.data.d) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    (hxs1 : a.xs ≤ 1) (hcl : 0 < cl) (hcu : 0 < cu) {v : ℝ} (hv : 0 < v) :
    a.canonicalPositiveOuterBroadMassDiameter v ≤
      (576*Ct*C0^3*cu^3/cl^3)*(Real.log a.data.N)^2*(a.xs^2/v)*a.data.N^(-(3*m+delta)) := by
  have H := a.canonical_mass_diameter_source_power_le hN hlog hnd hCt hC0 hxs1
    (A:=288*cu^3/cl^3) (by positivity) hv
  unfold canonicalPositiveOuterBroadMassDiameter
  convert H using 1 <;> field_simp <;> ring

theorem canonical_outer_broad_mass_diameter_le_high_source
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N)
    (hnd : 1/a.data.N ≤ a.data.d) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    (hxs1 : a.xs ≤ 1) (hcl : 0 < cl) (hcu : 0 < cu) {v : ℝ} (hv : 0 < v) :
    a.canonicalOuterBroadMassDiameter v ≤
      (576*Ct*C0^3*cu^3/cl^3)*(Real.log a.data.N)^2*(a.xs^2/v)*a.data.N^(-(3*m+delta)) :=
  (a.canonical_outer_broad_mass_diameter_le_positive (zero_le_one.trans hlog) v).trans
    (a.canonical_positive_outer_broad_mass_diameter_le_high_source hN hlog hnd hCt hC0 hxs1 hcl hcu hv)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
