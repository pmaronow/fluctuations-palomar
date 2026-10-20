module

public import ComparisonNativeActualHighMassScale
public import SKProof.Port.ComparisonActualOriginalQLocalDiameterBudgetDefinitions
public import SKProof.Port.ComparisonActualOriginalQMassBandScale
public import SKProof.Port.ComparisonActualOriginalQCriticalScaleNumerics
public import SKProof.Port.ComparisonActualOriginalQInitialCharges

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

theorem canonical_high_mass_height_le
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {v c : ℝ} (hc : 0 < c) (hvlo : c*a.xs ≤ v) :
    a.canonicalMassHeight v ≤ actualHighMassHeightConstant c*v := by
  have HX : a.xs ≤ v/c:= (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hvlo)
  unfold canonicalMassHeight actualHighMassHeightConstant
  have HU:=min_le_left (16*v) 1
  calc
    _ ≤ v/c+16*v := add_le_add HX HU
    _ = _ := by ring

theorem canonical_high_mass_power_size
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (hCt : 0 ≤ Ct) (hxs1 : a.xs ≤ 1)
    {v c : ℝ} (hc : 0 < c) (hvlo : c*a.xs ≤ v) :
    1/a.data.U^2 ≤ actualHighMassStrengthConstant Az cl Ct c*a.canonicalMassPower v*a.xs*v := by
  have hv : 0 < v:=(mul_pos hc a.hxs).trans_le hvlo
  let u:=min (16*v) 1
  have hu : u∈Icc (0:ℝ) 1:=⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩
  have hR : a.sweepRadius u∈Icc (0:ℝ) 1:=a.sweepRadius_bounds0 u
  have hCf : 0 ≤ Az+1/cl:=by positivity
  have HR:=a.inverse_radius_le_source_mass hcl hAz hu
  have HZ : a.sweepRadius u ≤ actualHighMassEndpointConstant Az cl c*v := by
    calc
      _ ≤ (Az+1/cl)*(a.xs+u) := HR
      _ ≤ (Az+1/cl)*(actualHighMassHeightConstant c*v) :=
        mul_le_mul_of_nonneg_left (a.canonical_high_mass_height_le hc hvlo) hCf
      _ ≤ actualHighMassEndpointConstant Az cl c*v := by
        rw [←mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hv.le
  have HS:=mass_strength_linear_test_scale a.data.hd a.hlam a.hxs hxs1 hR.1 hR.2
    hc hvlo (le_max_left _ _) HZ
  have HK : 0 ≤ actualHighMassEndpointConstant Az cl c:=by
    exact (one_div_pos.mpr hc).le.trans (le_max_left _ _)
  have HgR : 0 ≤ laplaceComparisonStrength a.data.d a.lam (a.sweepRadius u):=
    (laplaceComparisonStrength_pos _ a.hlam _).le
  have Hg : 0 ≤ actualHighMassEndpointConstant Az cl c*
      laplaceComparisonStrength a.data.d a.lam (a.sweepRadius u)*a.xs*v:=
    mul_nonneg (mul_nonneg (mul_nonneg HK HgR) a.hxs.le) hv.le
  have HT : a.data.N*a.data.E^2 ≤ actualHighMassStrengthConstant Az cl Ct c*
      laplaceComparisonStrength a.data.d a.lam (a.sweepRadius u)*a.xs*v := by
    have H:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left HS hCt) a.hxs.le
    have H' : Ct*laplaceComparisonStrength a.data.d a.lam a.xs*a.xs^2 ≤
        Ct*actualHighMassEndpointConstant Az cl c*
          laplaceComparisonStrength a.data.d a.lam (a.sweepRadius u)*a.xs*v := by
      unfold actualHighMassEndpointConstant
      convert H using 1 <;> ring
    apply a.htest.trans H' |>.trans
    unfold actualHighMassStrengthConstant
    nlinarith only [Hg]
  calc
    1/a.data.U^2 = a.data.N*(a.data.N*a.data.E^2) := by
      unfold ActualHighWallData.U comparisonSmallMass
      field_simp
    _ ≤ a.data.N*(actualHighMassStrengthConstant Az cl Ct c*
      laplaceComparisonStrength a.data.d a.lam (a.sweepRadius u)*a.xs*v) :=
      mul_le_mul_of_nonneg_left HT a.data.hN.le
    _ = _ := by unfold canonicalMassPower;dsimp only [u];ring

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
