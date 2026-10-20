module

public import ComparisonNativeActualMassBudgetScale
public import ComparisonActualHighOnlyCanonicalMassBudgets
public import ComparisonActualHighOnlyInitialCharges

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
theorem canonical_mass_height_le
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {v Cv : ℝ} (_hCv : 0 ≤ Cv) (hv : v ≤ Cv*a.xs) :
    a.canonicalMassHeight v ≤ (1+16*Cv)*a.xs := by
  unfold canonicalMassHeight
  have H : min (16*v) 1 ≤ 16*v:=min_le_left _ _
  nlinarith

theorem canonical_mass_power_pos
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (v : ℝ) :
    0 < a.canonicalMassPower v:=
  mul_pos a.data.hN (laplaceComparisonStrength_pos a.data.d a.hlam _)

theorem canonical_mass_diameter_rate
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0<C0) (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) :
    a.canonicalMassDiameter/a.xs ≤
      (9*C0^3*(1+Real.log (1+D^2)))*(Real.log a.data.N)^2*a.data.N^(-(3*m+delta)) := by
  have Htravel:=comparisonTravel_ratio_bound (δ:=delta) hN a.data.hE a.data.hd a.hdD hC0 a.hupper a.hlower
  have ht0 : 0 ≤ a.cavityCapTravel := by
    unfold cavityCapTravel
    have Hu:=a.data.hU
    have Hlog : 0 ≤ Real.log ((1+a.data.U)/a.data.U):=
      Real.log_nonneg ((one_le_div Hu).mpr (by linarith))
    exact mul_nonneg (div_nonneg a.data.hL.le (Real.rpow_nonneg a.data.hN.le _)) Hlog
  have Hscale : a.cavityCapTravel/a.xs ≤ a.cavityCapTravel/comparisonLowerScale a.data.N a.data.E a.data.d :=
    div_le_div_of_nonneg_left ht0 (comparisonLowerScale_pos a.data.hN a.data.hE a.data.hd) a.hscale
  have Htr : a.cavityCapTravel/a.xs ≤ C0^3*a.data.N^(-(3*m+delta))*
      (Real.log a.data.N+Real.log (1+D^2)) := Hscale.trans Htravel
  have HlogD : 0 ≤ Real.log (1+D^2):=Real.log_nonneg (by nlinarith [sq_nonneg D])
  have Hlogs : Real.log a.data.N+Real.log (1+D^2) ≤
      (1+Real.log (1+D^2))*Real.log a.data.N := by
    nlinarith [mul_nonneg HlogD (sub_nonneg.mpr hlog)]
  have Hmul:=mul_le_mul_of_nonneg_left Htr (show 0 ≤ 9*Real.log a.data.N by linarith)
  have HlogsMul:=mul_le_mul_of_nonneg_left Hlogs
    (show 0 ≤ 9*Real.log a.data.N*(C0^3*a.data.N^(-(3*m+delta))) by positivity)
  unfold canonicalMassDiameter
  have Hmul' : 9*Real.log a.data.N*a.cavityCapTravel/a.xs ≤
      9*Real.log a.data.N*(C0^3*a.data.N^(-(3*m+delta))*
        (Real.log a.data.N+Real.log (1+D^2))) := by
    simpa only [mul_div_assoc] using Hmul
  exact Hmul'.trans (by nlinarith [HlogsMul])

theorem canonical_mass_power_le
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (v : ℝ) :
    a.canonicalMassPower v ≤ a.data.N*D^2 := by
  apply mul_le_mul_of_nonneg_left _ a.data.hN.le
  exact (laplaceComparisonStrength_le a.data.d a.hlam.le _).trans
    (a.hld.trans (pow_le_pow_left₀ a.data.hd.le a.hdD 2))

theorem canonical_mass_inverse_cube_le
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0<C0) (hm : 0 < m) (hN : 1 ≤ a.data.N) :
    1/a.xs^3 ≤ C0^3*a.data.N^3 := by
  have hupper : a.data.E ≤ a.data.d^2/Real.sqrt a.data.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr a.data.hN)).mpr (by simpa only [mul_comm] using a.hupper)
  have hlower : (1/C0)*a.data.N^(-(2:ℝ)/3+m)*a.data.d ≤ a.data.E := by
    have H : (a.data.N^(-(2:ℝ)/3+m)*a.data.d)/C0 ≤ a.data.E:=
      (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using a.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have Hparent:=comparison_parent_scale_lower_bounds a.data.hN (one_div_pos.mpr hC0)
    a.data.hd hlower hupper
  have Hpow : a.data.N^(-(1:ℝ)) ≤ a.data.N^(-(1:ℝ)/6+m):=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have Hx : 1/(C0*a.data.N) ≤ a.xs := by
    have H:=(mul_le_mul_of_nonneg_left Hpow (one_div_pos.mpr hC0).le).trans
      (Hparent.2.2.trans a.hscale)
    calc
      1/(C0*a.data.N) = (1/C0)*a.data.N^(-(1:ℝ)) := by
        rw [Real.rpow_neg a.data.hN.le,Real.rpow_one]
        ring
      _ ≤ a.xs := H
  have Hcube:=pow_le_pow_left₀ (by positivity : 0 ≤ 1/(C0*a.data.N)) Hx 3
  have Hinv:=one_div_le_one_div_of_le (by positivity : 0 < (1/(C0*a.data.N))^3) Hcube
  simpa only [one_div_div,div_pow,one_pow,mul_pow,div_one] using Hinv

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
