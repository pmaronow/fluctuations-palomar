module

public import ComparisonNativeActualHighMassScale
public import ComparisonNativeActualHighMassDiameter

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem mass_strength_lower_at_scaled_radius {d lam W Cd CLam : ℝ}
    (hd : 0 < d) (hLam : 0 < lam) (hld : lam ≤ d^2) (hW : 0 < W)
    (hCd : 1 ≤ Cd) (hCLam : 0 < CLam) (hWd : W ≤ Cd*d)
    (hWLam : W^2 ≤ CLam*lam) :
    W^2 ≤ CLam*Cd*laplaceComparisonStrength d lam W := by
  have hCd0 : 0 < Cd:=zero_lt_one.trans_le hCd
  have hlow : lam/Cd ≤ min lam (d^3/W) := by
    apply le_min
    · exact div_le_self hLam.le hCd
    · apply (div_le_div_iff₀ hCd0 hW).mpr
      have H:=mul_le_mul_of_nonneg_left hWd hLam.le
      have H':=mul_le_mul_of_nonneg_right hld (mul_pos hCd0 hd).le
      nlinarith [H,H']
  have HG:=hlow.trans (laplaceComparisonStrength_lower hd hLam hW)
  have H : lam ≤ Cd*laplaceComparisonStrength d lam W:=
    by simpa only [mul_comm] using (div_le_iff₀ hCd0).mp HG
  have HH:=mul_le_mul_of_nonneg_left H hCLam.le
  exact hWLam.trans (by simpa only [mul_assoc] using HH)

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def canonicalDirectTestBandScale
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) : ℝ :=
  max a.xs (Real.sqrt (laplaceComparisonStrength a.context.d a.lam a.xs))

theorem canonical_direct_test_band_pos
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    0 < a.canonicalDirectTestBandScale := a.hxs.trans_le (le_max_left _ _)

theorem canonical_direct_test_band_ge_scale
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    a.xs ≤ a.canonicalDirectTestBandScale := le_max_left _ _

theorem canonical_direct_test_band_geometry
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hsmall : a.xs^2 ≤ Cs*laplaceComparisonStrength a.context.d a.lam a.xs) :
    a.canonicalDirectTestBandScale ≤ (Cs+1)*a.context.d ∧
      a.canonicalDirectTestBandScale^2 ≤ (Cs+1)*a.lam := by
  have Hg : 0 ≤ laplaceComparisonStrength a.context.d a.lam a.xs:=
    (laplaceComparisonStrength_pos _ a.hlam _).le
  have HgLam:=laplaceComparisonStrength_le a.context.d a.hlam.le a.xs
  have Hgd:=HgLam.trans a.hld
  have HxLam:=hsmall.trans (mul_le_mul_of_nonneg_left HgLam hCs)
  have Hxd:=hsmall.trans (mul_le_mul_of_nonneg_left Hgd hCs)
  have HX : a.xs ≤ (Cs+1)*a.context.d := by
    have Hcoef : Cs ≤ (Cs+1)^2 := by nlinarith
    have HH:=mul_le_mul_of_nonneg_right Hcoef (sq_nonneg a.context.d)
    have Hbound : a.xs^2 ≤ ((Cs+1)*a.context.d)^2:=by nlinarith
    have HY : 0 ≤ (Cs+1)*a.context.d:=mul_nonneg (by linarith) a.context.hd.le
    nlinarith [a.hxs]
  have Hsqrt : Real.sqrt (laplaceComparisonStrength a.context.d a.lam a.xs) ≤ a.context.d := by
    have H:=Real.sqrt_le_sqrt Hgd
    simpa only [Real.sqrt_sq_eq_abs,abs_of_pos a.context.hd] using H
  constructor
  · exact max_le HX (Hsqrt.trans (by nlinarith [a.context.hd]))
  · unfold canonicalDirectTestBandScale
    rcases le_total a.xs (Real.sqrt (laplaceComparisonStrength a.context.d a.lam a.xs)) with H|H
    · rw [max_eq_right H,Real.sq_sqrt Hg]
      nlinarith [a.hlam,mul_nonneg hCs a.hlam.le]
    · rw [max_eq_left H]
      nlinarith [a.hlam]

theorem canonical_direct_test_high_power_size
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) {Cs c v : ℝ} (hCs : 0 ≤ Cs) (hc : 0 < c)
    (hsmall : a.xs^2 ≤ Cs*laplaceComparisonStrength a.context.d a.lam a.xs)
    (hW1 : a.canonicalDirectTestBandScale ≤ 1)
    (hvlo : c*a.canonicalDirectTestBandScale ≤ v) :
    a.context.N*a.canonicalDirectTestBandScale^3 ≤
      ((Cs+1)^2*actualHighMassEndpointConstant Az cl c)*a.canonicalMassPower v*v := by
  let W:=a.canonicalDirectTestBandScale
  have hW : 0 < W:=a.canonical_direct_test_band_pos
  have HX:=a.canonical_direct_test_band_ge_scale
  have HW:=a.canonical_direct_test_band_geometry hCs hsmall
  have Hbase:=mass_strength_lower_at_scaled_radius a.context.hd a.hlam a.hld hW
    (show 1 ≤ Cs+1 by linarith) (show 0 < Cs+1 by linarith) HW.1 HW.2
  have hv : 0 < v:=(mul_pos hc hW).trans_le hvlo
  let u:=min (16*v) 1
  have hu : u∈Icc (0:ℝ) 1:=⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩
  have HR:=a.inverse_radius_le_source_mass hcl hAz hu
  have hR:=comparisonSweepQuantile_bounds a.context.hc a.context.hk a.context.hkc
    a.context.hm a.context.hM a.alpha u
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
  have HS:=mass_strength_linear_test_scale a.context.hd a.hlam hW hW1 hR.1 hR.2
    hc hvlo (le_max_left _ _) HZ
  have H1:=mul_le_mul_of_nonneg_right Hbase hW.le
  have H2:=mul_le_mul_of_nonneg_left HS (show 0 ≤ (Cs+1)^2 by positivity)
  have H3 : W^3 ≤ ((Cs+1)^2*actualHighMassEndpointConstant Az cl c)*
      laplaceComparisonStrength a.context.d a.lam (a.R u)*v := by
    unfold actualHighMassEndpointConstant
    nlinarith only [H1,H2]
  have H:=mul_le_mul_of_nonneg_left H3 a.context.hN.le
  convert H using 1; unfold canonicalMassPower; dsimp only [u,W]; ring

theorem canonical_high_mass_critical_ratio
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0 < C0) :
    a.context.d^3/(a.context.N^2*a.context.E^3) ≤ C0^3*a.context.N^(-3*m) := by
  have hN0 := a.context.hN
  have hE0 := a.context.hE
  have hd0 := a.context.hd
  have Hlo : a.context.N^(-(2:ℝ)/3+m)*a.context.d ≤ C0*a.context.E:=by
    simpa only [mul_comm] using a.hlower
  have Hcube:=pow_le_pow_left₀ (by positivity : 0 ≤ a.context.N^(-(2:ℝ)/3+m)*a.context.d) Hlo 3
  have HE : (a.context.N^(-(2:ℝ)/3+m)*a.context.d)^3=
      a.context.N^(-2+3*m)*a.context.d^3:=by
    rw [mul_pow,←Real.rpow_mul_natCast a.context.hN.le]
    congr 1; congr 1; ring
  rw [HE,mul_pow] at Hcube
  have H:=mul_le_mul_of_nonneg_left Hcube
    (show 0 ≤ a.context.N^(-3*m)/(a.context.E^3) by positivity)
  have HEleft : (a.context.N^(-3*m)/a.context.E^3)*
      (a.context.N^(-2+3*m)*a.context.d^3)=a.context.d^3/(a.context.N^2*a.context.E^3):=by
    rw [div_mul_eq_mul_div,←mul_assoc,←Real.rpow_add a.context.hN,
      show -3*m+(-2+3*m)=(-2:ℝ) by ring,Real.rpow_neg a.context.hN.le,Real.rpow_two]
    field_simp
  rw [HEleft] at H
  convert H using 1; field_simp [a.context.hE.ne']

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
