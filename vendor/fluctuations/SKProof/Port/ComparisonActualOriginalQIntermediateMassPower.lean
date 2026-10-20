module

public import ComparisonNativeActualIntermediateMassPower
public import SKProof.Port.ComparisonActualOriginalQHighMassScale
public import SKProof.Port.ComparisonActualOriginalQHighMassSharpScale

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

theorem canonical_intermediate_mass_power_lower
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) {Cs c C v : ℝ} (hCs : 0 ≤ Cs) (hc : 0 < c)
    (hsmall : a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs)
    (hW1 : a.directTestWorkingScale ≤ 1)
    (hvlo : c*a.xs ≤ v) (hvupper : v ≤ C*a.directTestWorkingScale) :
    a.data.N*a.directTestWorkingScale^2 ≤
      actualIntermediateMassPowerConstant Cs Az cl c C*a.canonicalMassPower v := by
  let W := a.directTestWorkingScale
  let E := actualHighMassEndpointConstant Az cl c
  let K := max (1:ℝ) (E*C)
  have hW : 0 < W := a.canonical_direct_test_band_pos
  have hv : 0 < v := (mul_pos hc a.hxs).trans_le hvlo
  have hE : 0 ≤ E := (one_div_pos.mpr hc).le.trans (le_max_left _ _)
  have HK : 1 ≤ K := le_max_left _ _
  have HW := a.canonical_direct_test_band_geometry hCs hsmall
  have Hbase := mass_strength_lower_at_scaled_radius a.data.hd a.hlam a.hld hW
    (show 1 ≤ Cs+1 by linarith) (show 0 < Cs+1 by linarith) HW.1 HW.2
  let u := min (16*v) 1
  have hu : u∈Icc (0:ℝ) 1 := ⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩
  have HR := a.inverse_radius_le_source_mass hcl hAz hu
  have hR : a.sweepRadius u∈Icc (0:ℝ) 1 := a.sweepRadius_bounds0 u
  have HZv : a.sweepRadius u ≤ E*v := by
    have HC : 0 ≤ Az+1/cl := by positivity
    calc
      _ ≤ (Az+1/cl)*(a.xs+u) := HR
      _ ≤ (Az+1/cl)*(actualHighMassHeightConstant c*v) :=
        mul_le_mul_of_nonneg_left (a.canonical_high_mass_height_le hc hvlo) HC
      _ ≤ E*v := by
        rw [←mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hv.le
  have HZW : a.sweepRadius u ≤ K*W := by
    apply HZv.trans
    have H1 := mul_le_mul_of_nonneg_left hvupper hE
    have H2 := mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) (E*C)) hW.le
    exact H1.trans (by simpa only [mul_assoc] using H2)
  have HS := mass_strength_linear_test_scale a.data.hd a.hlam hW hW1 hR.1 hR.2
    (c:=1) zero_lt_one (by simp only [one_mul,le_refl] : 1*W ≤ W)
    (by simpa only [one_div_one] using HK) HZW
  have HG : laplaceComparisonStrength a.data.d a.lam W ≤
      K*laplaceComparisonStrength a.data.d a.lam (a.sweepRadius u) := by
    nlinarith only [HS,hW]
  have HH := Hbase.trans (mul_le_mul_of_nonneg_left HG (show 0 ≤ (Cs+1)*(Cs+1) by positivity))
  have HN := mul_le_mul_of_nonneg_left HH a.data.hN.le
  convert HN using 1;
    dsimp only [actualIntermediateMassPowerConstant,canonicalMassPower,u,K,E,W]; ring

theorem canonical_intermediate_effective_power_size
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) {Cs c C v : ℝ} (hCs : 0 ≤ Cs) (hc : 0 < c)
    (hsmall : a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs)
    (hW1 : a.directTestWorkingScale ≤ 1)
    (hvlo : c*a.xs ≤ v) (hvupper : v ≤ C*a.directTestWorkingScale) :
    a.data.N*(actualIntermediateMassEffectiveScale a.directTestWorkingScale v)^3 ≤
      actualIntermediateMassPowerConstant Cs Az cl c C*a.canonicalMassPower v*v := by
  have hv : 0 < v := (mul_pos hc a.hxs).trans_le hvlo
  rw [actualIntermediateMassEffectiveScale_cube a.canonical_direct_test_band_pos.le hv.le]
  have H := mul_le_mul_of_nonneg_right
    (a.canonical_intermediate_mass_power_lower hcl hAz hCs hc hsmall hW1 hvlo hvupper) hv.le
  simpa only [mul_assoc] using H

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
