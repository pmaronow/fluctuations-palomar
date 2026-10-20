module

public import ComparisonNativeActualMassBandScale
public import ComparisonActualHighOnlyMassBudgetNoise

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
theorem canonical_mass_band_height_le
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {v W Cv : ℝ} (hxsW : a.xs ≤ W) (hv : v ≤ Cv*W) :
    a.canonicalMassHeight v ≤ (1+16*Cv)*W := by
  unfold canonicalMassHeight
  have H : min (16*v) 1 ≤ 16*v:=min_le_left _ _
  nlinarith

theorem canonical_mass_band_power_size
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0<cl) (hAz : 0 ≤ Az) (hCt : 0 ≤ Ct)
    {W v Cv : ℝ} (hxsW : a.xs ≤ W) (hW1 : W ≤ 1) (hv : 0<v) (hvsize : v ≤ Cv*W) :
    1/a.data.U^2 ≤ actualMassStrengthConstant Az cl Ct Cv*a.canonicalMassPower v*W^2 := by
  have hW : 0<W:=a.hxs.trans_le hxsW
  let u:=min (16*v) 1
  have hu : u∈Icc (0:ℝ) 1:=⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩
  have hR:=a.shiftedNativeModel.R_bounds u
  have hCf : 0 ≤ Az+1/cl:=by positivity
  have HR:=a.inverse_radius_le_source_mass hcl hAz hu
  have Hu : a.xs+u ≤ (1+16*Cv)*W:=by
    have H : u ≤ 16*v:=min_le_left _ _
    nlinarith
  have HZ : a.R u ≤ actualMassEndpointConstant Az cl Cv*W := by
    calc
      _ ≤ (Az+1/cl)*(a.xs+u) := HR
      _ ≤ (Az+1/cl)*((1+16*Cv)*W) := mul_le_mul_of_nonneg_left Hu hCf
      _ ≤ actualMassEndpointConstant Az cl Cv*W := by
        rw [←mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hW.le
  have Hstrength:=mass_strength_above_test_scale a.data.hd a.hlam a.hxs hxsW hW1
    hR.1 hR.2 (le_max_left _ _) HZ
  change laplaceComparisonStrength a.data.d a.lam a.xs*a.xs^2 ≤
    actualMassEndpointConstant Az cl Cv*laplaceComparisonStrength a.data.d a.lam (a.R u)*W^2 at Hstrength
  have Htest : a.data.N*a.data.E^2 ≤
      actualMassStrengthConstant Az cl Ct Cv*laplaceComparisonStrength a.data.d a.lam (a.R u)*W^2 := by
    have H:=mul_le_mul_of_nonneg_left Hstrength hCt
    have HZ0 : 0 ≤ actualMassEndpointConstant Az cl Cv:=zero_le_one.trans (le_max_left _ _)
    have HH:=mul_nonneg HZ0 (mul_nonneg
      (laplaceComparisonStrength_pos a.data.d a.hlam (a.R u)).le (sq_nonneg W))
    unfold actualMassStrengthConstant
    nlinarith [a.htest]
  calc
    1/a.data.U^2 = a.data.N*(a.data.N*a.data.E^2) := by
      unfold ActualHighOnlyComparisonData.U comparisonSmallMass
      field_simp
    _ ≤ a.data.N*(actualMassStrengthConstant Az cl Ct Cv*
      laplaceComparisonStrength a.data.d a.lam (a.R u)*W^2) :=
      mul_le_mul_of_nonneg_left Htest a.data.hN.le
    _ = _ := by unfold canonicalMassPower;dsimp only [u];ring

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
