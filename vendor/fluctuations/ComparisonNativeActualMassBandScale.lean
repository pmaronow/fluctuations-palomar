module

public import ComparisonNativeActualMassBudgetRates

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem mass_strength_above_test_scale {d lam xs W z C : ℝ}
    (hd : 0<d) (hlam : 0<lam) (hxs : 0<xs) (hxsW : xs ≤ W) (hW1 : W ≤ 1)
    (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 1 ≤ C) (hzW : z ≤ C*W) :
    laplaceComparisonStrength d lam xs*xs^2 ≤ C*laplaceComparisonStrength d lam z*W^2 := by
  have hmono:=laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀:=0) le_rfl
  have hg:=(laplaceComparisonStrength_pos d hlam z).le
  have hW : 0<W:=hxs.trans_le hxsW
  by_cases hzx : z ≤ xs
  · have HG:=(hmono.1 ⟨hz,hz1⟩ ⟨hxs.le,hxsW.trans hW1⟩ hzx)
    have HX:=pow_le_pow_left₀ hxs.le hxsW 2
    have H:=mul_le_mul HG HX (sq_nonneg _) hg
    have HC : laplaceComparisonStrength d lam z*W^2 ≤ C*laplaceComparisonStrength d lam z*W^2 := by
      have Hc:=mul_le_mul_of_nonneg_right hC (mul_nonneg hg (sq_nonneg W))
      simpa only [one_mul,mul_assoc] using Hc
    exact H.trans HC
  · have H:=hmono.2 ⟨hxs.le,hxsW.trans hW1⟩ ⟨hz,hz1⟩ (le_of_not_ge hzx)
    have H1:=mul_le_mul_of_nonneg_left hzW hg
    have H2:=mul_le_mul (H.trans H1) hxsW hxs.le (by positivity : 0 ≤ laplaceComparisonStrength d lam z*(C*W))
    convert H2 using 1 <;> ring

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_mass_band_height_le
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {v W Cv : ℝ} (hxsW : a.xs ≤ W) (hv : v ≤ Cv*W) :
    a.canonicalMassHeight v ≤ (1+16*Cv)*W := by
  unfold canonicalMassHeight
  have H : min (16*v) 1 ≤ 16*v:=min_le_left _ _
  nlinarith

theorem canonical_mass_band_power_size
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0<cl) (hAz : 0 ≤ Az) (hCt : 0 ≤ Ct)
    {W v Cv : ℝ} (hxsW : a.xs ≤ W) (hW1 : W ≤ 1) (hv : 0<v) (hvsize : v ≤ Cv*W) :
    1/a.context.U^2 ≤ actualMassStrengthConstant Az cl Ct Cv*a.canonicalMassPower v*W^2 := by
  have hW : 0<W:=a.hxs.trans_le hxsW
  let u:=min (16*v) 1
  have hu : u∈Icc (0:ℝ) 1:=⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩
  have hR:=comparisonSweepQuantile_bounds a.context.hc a.context.hk a.context.hkc
    a.context.hm a.context.hM a.alpha u
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
  have Hstrength:=mass_strength_above_test_scale a.context.hd a.hlam a.hxs hxsW hW1
    hR.1 hR.2 (le_max_left _ _) HZ
  change laplaceComparisonStrength a.context.d a.lam a.xs*a.xs^2 ≤
    actualMassEndpointConstant Az cl Cv*laplaceComparisonStrength a.context.d a.lam (a.R u)*W^2 at Hstrength
  have Htest : a.context.N*a.context.E^2 ≤
      actualMassStrengthConstant Az cl Ct Cv*laplaceComparisonStrength a.context.d a.lam (a.R u)*W^2 := by
    have H:=mul_le_mul_of_nonneg_left Hstrength hCt
    have HZ0 : 0 ≤ actualMassEndpointConstant Az cl Cv:=zero_le_one.trans (le_max_left _ _)
    have HH:=mul_nonneg HZ0 (mul_nonneg
      (laplaceComparisonStrength_pos a.context.d a.hlam (a.R u)).le (sq_nonneg W))
    unfold actualMassStrengthConstant
    nlinarith [a.htest]
  calc
    1/a.context.U^2 = a.context.N*(a.context.N*a.context.E^2) := by
      unfold NativeOverlapContext.U comparisonSmallMass
      field_simp
    _ ≤ a.context.N*(actualMassStrengthConstant Az cl Ct Cv*
      laplaceComparisonStrength a.context.d a.lam (a.R u)*W^2) :=
      mul_le_mul_of_nonneg_left Htest a.context.hN.le
    _ = _ := by unfold canonicalMassPower;dsimp only [u];ring

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
