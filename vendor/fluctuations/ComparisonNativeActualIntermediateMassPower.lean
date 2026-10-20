module

public import ComparisonNativeActualIntermediateMassScale

@[expose] public section

noncomputable section
set_option maxHeartbeats 9000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

def actualIntermediateMassPowerConstant (Cs Az cl c C : ℝ) : ℝ :=
  (Cs+1)^2*max 1 (actualHighMassEndpointConstant Az cl c*C)

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_intermediate_mass_power_lower
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) {Cs c C v : ℝ} (hCs : 0 ≤ Cs) (hc : 0 < c)
    (hsmall : a.xs^2 ≤ Cs*laplaceComparisonStrength a.context.d a.lam a.xs)
    (hW1 : a.canonicalDirectTestBandScale ≤ 1)
    (hvlo : c*a.xs ≤ v) (hvupper : v ≤ C*a.canonicalDirectTestBandScale) :
    a.context.N*a.canonicalDirectTestBandScale^2 ≤
      actualIntermediateMassPowerConstant Cs Az cl c C*a.canonicalMassPower v := by
  let W := a.canonicalDirectTestBandScale
  let E := actualHighMassEndpointConstant Az cl c
  let K := max (1:ℝ) (E*C)
  have hW : 0 < W := a.canonical_direct_test_band_pos
  have hv : 0 < v := (mul_pos hc a.hxs).trans_le hvlo
  have hE : 0 ≤ E := (one_div_pos.mpr hc).le.trans (le_max_left _ _)
  have HK : 1 ≤ K := le_max_left _ _
  have HW := a.canonical_direct_test_band_geometry hCs hsmall
  have Hbase := mass_strength_lower_at_scaled_radius a.context.hd a.hlam a.hld hW
    (show 1 ≤ Cs+1 by linarith) (show 0 < Cs+1 by linarith) HW.1 HW.2
  let u := min (16*v) 1
  have hu : u∈Icc (0:ℝ) 1 := ⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩
  have HR := a.inverse_radius_le_source_mass hcl hAz hu
  have hR := comparisonSweepQuantile_bounds a.context.hc a.context.hk a.context.hkc
    a.context.hm a.context.hM a.alpha u
  have HZv : a.R u ≤ E*v := by
    have HC : 0 ≤ Az+1/cl := by positivity
    calc
      _ ≤ (Az+1/cl)*(a.xs+u) := HR
      _ ≤ (Az+1/cl)*(actualHighMassHeightConstant c*v) :=
        mul_le_mul_of_nonneg_left (a.canonical_high_mass_height_le hc hvlo) HC
      _ ≤ E*v := by
        rw [←mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hv.le
  have HZW : a.R u ≤ K*W := by
    apply HZv.trans
    have H1 := mul_le_mul_of_nonneg_left hvupper hE
    have H2 := mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) (E*C)) hW.le
    exact H1.trans (by simpa only [mul_assoc] using H2)
  have HS := mass_strength_linear_test_scale a.context.hd a.hlam hW hW1 hR.1 hR.2
    (c:=1) zero_lt_one (by simp only [one_mul,le_refl] : 1*W ≤ W)
    (by simpa only [one_div_one] using HK) HZW
  have HG : laplaceComparisonStrength a.context.d a.lam W ≤
      K*laplaceComparisonStrength a.context.d a.lam (a.R u) := by
    nlinarith only [HS,hW]
  have HH := Hbase.trans (mul_le_mul_of_nonneg_left HG (show 0 ≤ (Cs+1)*(Cs+1) by positivity))
  have HN := mul_le_mul_of_nonneg_left HH a.context.hN.le
  convert HN using 1;
    dsimp only [actualIntermediateMassPowerConstant,canonicalMassPower,u,K,E,W]; ring

theorem canonical_intermediate_effective_power_size
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) {Cs c C v : ℝ} (hCs : 0 ≤ Cs) (hc : 0 < c)
    (hsmall : a.xs^2 ≤ Cs*laplaceComparisonStrength a.context.d a.lam a.xs)
    (hW1 : a.canonicalDirectTestBandScale ≤ 1)
    (hvlo : c*a.xs ≤ v) (hvupper : v ≤ C*a.canonicalDirectTestBandScale) :
    a.context.N*(actualIntermediateMassEffectiveScale a.canonicalDirectTestBandScale v)^3 ≤
      actualIntermediateMassPowerConstant Cs Az cl c C*a.canonicalMassPower v*v := by
  have hv : 0 < v := (mul_pos hc a.hxs).trans_le hvlo
  rw [actualIntermediateMassEffectiveScale_cube a.canonical_direct_test_band_pos.le hv.le]
  have H := mul_le_mul_of_nonneg_right
    (a.canonical_intermediate_mass_power_lower hcl hAz hCs hc hsmall hW1 hvlo hvupper) hv.le
  simpa only [mul_assoc] using H

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
