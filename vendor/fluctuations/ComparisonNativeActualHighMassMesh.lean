module

public import ComparisonNativeActualHighMassOrdinaryNormalization

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_high_mass_inverse_four_coarse
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hC0 : 0 < C0) (hN : 1 ≤ a.context.N) :
    1/a.xs^4 ≤ C0^4*a.context.N^4 := by
  have H:=a.canonical_high_mass_inverse_power hC0 4
  simp only [Nat.cast_ofNat,show (4:ℝ)/6=(2:ℝ)/3 by norm_num] at H
  have HH:=mul_le_mul_of_nonneg_left H (Real.rpow_nonneg a.context.hN.le ((2:ℝ)/3))
  have HE : a.context.N^((2:ℝ)/3)*(1/(a.context.N^((2:ℝ)/3)*a.xs^4))=1/a.xs^4:=by
    field_simp
  have HR : a.context.N^((2:ℝ)/3)*(C0^4*a.context.N^(-(4:ℝ)*m))=
      C0^4*a.context.N^((2:ℝ)/3-4*m):=by
    rw [show a.context.N^((2:ℝ)/3)*(C0^4*a.context.N^(-(4:ℝ)*m))=
      C0^4*(a.context.N^((2:ℝ)/3)*a.context.N^(-4*m)) by ring,←Real.rpow_add a.context.hN]
    rw [show (2:ℝ)/3 + -(4:ℝ)*m=(2:ℝ)/3-4*m by ring]
  rw [HE,HR] at HH
  apply HH.trans
  have Hpow:=Real.rpow_le_rpow_of_exponent_le hN (show (2:ℝ)/3-4*m ≤ 4 by linarith)
  simpa only [Real.rpow_ofNat] using mul_le_mul_of_nonneg_left Hpow (pow_nonneg hC0.le 4)

theorem canonical_high_mass_normalization_weight_le
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hC0 : 0 < C0) (hN : 1 ≤ a.context.N)
    {c v : ℝ} (hc : 0 < c) (hW1 : a.canonicalDirectTestBandScale ≤ 1)
    (hv : 0 < v) (hvlo : c*a.canonicalDirectTestBandScale ≤ v) :
    a.canonicalDirectTestBandScale^2/(a.xs^4*v) ≤ (C0^4/c)*a.context.N^4 := by
  have hW:=a.canonical_direct_test_band_pos
  have hxs:=a.hxs
  have Hvar : a.canonicalDirectTestBandScale^2/v ≤ 1/c:=by
    apply (div_le_div_iff₀ hv hc).mpr
    have HS : a.canonicalDirectTestBandScale^2 ≤ a.canonicalDirectTestBandScale:=by nlinarith
    have H:=mul_le_mul_of_nonneg_left HS hc.le
    nlinarith only [H,hvlo]
  have Hinv:=a.canonical_high_mass_inverse_four_coarse hm hC0 hN
  have H:=mul_le_mul Hvar Hinv (by positivity : 0 ≤ 1/a.xs^4) (one_div_pos.mpr hc).le
  convert H using 1 <;> ring

theorem canonical_high_mass_ordinary_cut_le
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hC0 : 0 < C0) (hN : 1 ≤ a.context.N)
    {Q c v cut : ℝ} (hc : 0 < c) (hW1 : a.canonicalDirectTestBandScale ≤ 1)
    (hv : 0 < v) (hv1 : v ≤ 1) (hvlo : c*a.canonicalDirectTestBandScale ≤ v)
    (hcut : 0 ≤ cut) :
    (18*(((Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2)^((1:ℝ)/3)+2)*cut)*
      (a.canonicalDirectTestBandScale^2/(a.xs^4*v)) ≤
      (18*(1024*Q^4*D^2+3)*C0^4/c)*a.context.N^5*cut := by
  have hxs:=a.hxs
  have hW:=a.canonical_direct_test_band_pos
  have hxs1:=a.canonical_direct_test_band_ge_scale.trans hW1
  have HY : 0 ≤ a.canonicalMassHeight v:=by unfold canonicalMassHeight;positivity
  have HY2 : a.canonicalMassHeight v ≤ 2:=by
    unfold canonicalMassHeight
    linarith [min_le_right (16*v) 1]
  have Hpower:=a.canonical_mass_power_le v
  have hP:=a.canonical_mass_power_pos v
  have HX : (Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2 ≤
      1024*Q^4*D^2*a.context.N:=by
    have Hy:=pow_le_pow_left₀ HY HY2 2
    have Hv:=pow_le_pow_left₀ hv.le hv1 2
    have H:=mul_le_mul (mul_le_mul_of_nonneg_left Hpower (show 0 ≤ Q^4*(a.canonicalMassHeight v)^2 by positivity))
      Hv (sq_nonneg v) (show 0 ≤ Q^4*(a.canonicalMassHeight v)^2*(a.context.N*D^2) by positivity)
    have HH:=mul_le_mul_of_nonneg_left Hy (show 0 ≤ Q^4*(a.context.N*D^2) by positivity)
    have HHH:=mul_le_mul_of_nonneg_left H (show 0 ≤ (256:ℝ) by norm_num)
    nlinarith only [HH,HHH]
  have HX0 : 0 ≤ (Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2:=by positivity
  have Hroot:=mass_root_third_le_linear (A:=1024*Q^4*D^2+1) (N:=a.context.N) HX0
    (by nlinarith [mul_nonneg (show 0 ≤ Q^4 by positivity) (sq_nonneg D)])
    hN (by nlinarith only [HX,a.context.hN.le])
  have Hraw : 18*(((Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2)^((1:ℝ)/3)+2)*cut ≤
      (18*(1024*Q^4*D^2+3))*a.context.N*cut:=by
    have Hb : ((Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2)^((1:ℝ)/3)+2 ≤
        (1024*Q^4*D^2+3)*a.context.N:=by nlinarith only [Hroot,hN]
    have H:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hb
      (by norm_num : (0:ℝ) ≤ 18)) hcut
    convert H using 1; ring
  have Hweight:=a.canonical_high_mass_normalization_weight_le hm hC0 hN hc hW1 hv hvlo
  have H:=mul_le_mul Hraw Hweight (by positivity : 0 ≤ a.canonicalDirectTestBandScale^2/(a.xs^4*v))
    (show 0 ≤ (18*(1024*Q^4*D^2+3))*a.context.N*cut by positivity)
  convert H using 1; ring

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
