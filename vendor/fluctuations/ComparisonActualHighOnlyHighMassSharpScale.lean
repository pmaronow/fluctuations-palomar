module

public import ComparisonNativeActualHighMassSharpScale
public import ComparisonActualHighOnlyHighMassScale
public import ComparisonActualHighOnlyAnalyticBasics

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_direct_test_high_power_size
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) {Cs c v : ℝ} (hCs : 0 ≤ Cs) (hc : 0 < c)
    (hsmall : a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs)
    (hW1 : a.canonicalDirectTestBandScale ≤ 1)
    (hvlo : c*a.canonicalDirectTestBandScale ≤ v) :
    a.data.N*a.canonicalDirectTestBandScale^3 ≤
      ((Cs+1)^2*actualHighMassEndpointConstant Az cl c)*a.canonicalMassPower v*v := by
  let W:=a.canonicalDirectTestBandScale
  have hW : 0 < W:=a.canonical_direct_test_band_pos
  have HX:=a.canonical_direct_test_band_ge_scale
  have HW:=a.canonical_direct_test_band_geometry hCs hsmall
  have Hbase:=mass_strength_lower_at_scaled_radius a.data.hd a.hlam a.hld hW
    (show 1 ≤ Cs+1 by linarith) (show 0 < Cs+1 by linarith) HW.1 HW.2
  have hv : 0 < v:=(mul_pos hc hW).trans_le hvlo
  let u:=min (16*v) 1
  have hu : u∈Icc (0:ℝ) 1:=⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩
  have HR:=a.inverse_radius_le_source_mass hcl hAz hu
  have hR : a.R u∈Icc (0:ℝ) 1:=a.shiftedNativeModel.R_bounds u
  have Hxv : c*a.xs ≤ v:= (mul_le_mul_of_nonneg_left HX hc.le).trans hvlo
  have HZ : a.R u ≤ actualHighMassEndpointConstant Az cl c*v := by
    have HC : 0 ≤ Az+1/cl:=by positivity
    calc
      _ ≤ (Az+1/cl)*(a.xs+u) := HR
      _ ≤ (Az+1/cl)*(actualHighMassHeightConstant c*v) :=
        mul_le_mul_of_nonneg_left (a.canonical_high_mass_height_le hc Hxv) HC
      _ ≤ actualHighMassEndpointConstant Az cl c*v := by
        rw [←mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hv.le
  have HS:=mass_strength_linear_test_scale a.data.hd a.hlam hW hW1 hR.1 hR.2
    hc hvlo (le_max_left _ _) HZ
  have H1:=mul_le_mul_of_nonneg_right Hbase hW.le
  have H2:=mul_le_mul_of_nonneg_left HS (show 0 ≤ (Cs+1)^2 by positivity)
  have H3 : W^3 ≤ ((Cs+1)^2*actualHighMassEndpointConstant Az cl c)*
      laplaceComparisonStrength a.data.d a.lam (a.R u)*v := by
    unfold actualHighMassEndpointConstant
    nlinarith only [H1,H2]
  have H:=mul_le_mul_of_nonneg_left H3 a.data.hN.le
  convert H using 1; unfold canonicalMassPower; dsimp only [u,W]; ring

theorem canonical_high_mass_critical_ratio
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0 < C0) :
    a.data.d^3/(a.data.N^2*a.data.E^3) ≤ C0^3*a.data.N^(-3*m) := by
  have hN0 := a.data.hN
  have hE0 := a.data.hE
  have hd0 := a.data.hd
  have Hlo : a.data.N^(-(2:ℝ)/3+m)*a.data.d ≤ C0*a.data.E:=by
    simpa only [mul_comm] using a.hlower
  have Hcube:=pow_le_pow_left₀ (by positivity : 0 ≤ a.data.N^(-(2:ℝ)/3+m)*a.data.d) Hlo 3
  have HE : (a.data.N^(-(2:ℝ)/3+m)*a.data.d)^3=
      a.data.N^(-2+3*m)*a.data.d^3:=by
    rw [mul_pow,←Real.rpow_mul_natCast a.data.hN.le]
    congr 1; congr 1; ring
  rw [HE,mul_pow] at Hcube
  have H:=mul_le_mul_of_nonneg_left Hcube
    (show 0 ≤ a.data.N^(-3*m)/(a.data.E^3) by positivity)
  have HEleft : (a.data.N^(-3*m)/a.data.E^3)*
      (a.data.N^(-2+3*m)*a.data.d^3)=a.data.d^3/(a.data.N^2*a.data.E^3):=by
    rw [div_mul_eq_mul_div,←mul_assoc,←Real.rpow_add a.data.hN,
      show -3*m+(-2+3*m)=(-2:ℝ) by ring,Real.rpow_neg a.data.hN.le,Real.rpow_two]
    field_simp
  rw [HEleft] at H
  convert H using 1; field_simp [a.data.hE.ne']

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
