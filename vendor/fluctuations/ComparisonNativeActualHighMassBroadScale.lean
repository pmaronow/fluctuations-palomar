module

public import ComparisonNativeActualHighMassReverse

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_chosen_high_mass_diameter_square_bound
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.context.N) (hlog : 1 ≤ Real.log a.context.N)
    (hnd : 1/a.context.N ≤ a.context.d) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    (hxs1 : a.xs ≤ 1) {Cdiam c v : ℝ} (hCdiam : 0 ≤ Cdiam) (hc : 0 < c) (hv : 0 < v)
    (hvlo : c*a.canonicalDirectTestBandScale ≤ v) :
    (a.canonicalChosenHighMassDiameter Cdiam v)^2*(a.canonicalDirectTestBandScale^2/a.xs^4) ≤
      (2*Cdiam*Ct*C0^3/c)^2*(Real.log a.context.N)^4*a.context.N^(-2*(3*m+delta)) := by
  let W := a.canonicalDirectTestBandScale
  let diam := a.canonicalChosenHighMassDiameter Cdiam v
  let C := 2*Cdiam*Ct*C0^3
  let L := Real.log a.context.N
  have hW : 0 < W := a.canonical_direct_test_band_pos
  have hx := a.hxs
  have hN0 := a.context.hN
  have hE := a.context.hE
  have hd := a.context.hd
  have hL : 0 ≤ L := zero_le_one.trans hlog
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdiam : 0 ≤ diam := by dsimp [diam,canonicalChosenHighMassDiameter]; positivity
  have Hsource := a.canonical_mass_diameter_source_power_le hN hlog hnd hCt hC0 hxs1 hCdiam hv
  have Hratio : W/v ≤ 1/c := (div_le_div_iff₀ hv hc).mpr (by simpa only [one_mul,mul_one,mul_comm,W] using hvlo)
  have Hmul := mul_le_mul_of_nonneg_right Hsource (show 0 ≤ W/a.xs^2 by positivity)
  have HE : (C*L^2*(a.xs^2/v)*a.context.N^(-(3*m+delta)))*(W/a.xs^2)=
      C*L^2*a.context.N^(-(3*m+delta))*(W/v) := by field_simp
  change diam*(W/a.xs^2) ≤ (C*L^2*(a.xs^2/v)*a.context.N^(-(3*m+delta)))*(W/a.xs^2) at Hmul
  rw [HE] at Hmul
  have Hupper : diam*W/a.xs^2 ≤ (C/c)*L^2*a.context.N^(-(3*m+delta)) := by
    have HH := mul_le_mul_of_nonneg_left Hratio
      (show 0 ≤ C*L^2*a.context.N^(-(3*m+delta)) by positivity)
    have HHmul : diam*W/a.xs^2 ≤ C*L^2*a.context.N^(-(3*m+delta))*(W/v) := by
      simpa only [mul_div_assoc] using Hmul
    apply HHmul.trans
    convert HH using 1
    ring
  have Hsq := pow_le_pow_left₀ (show 0 ≤ diam*W/a.xs^2 by positivity) Hupper 2
  have HEN : (a.context.N^(-(3*m+delta)))^2=a.context.N^(-2*(3*m+delta)) := by
    rw [←Real.rpow_mul_natCast hN0.le]
    congr 1
    ring
  rw [mul_pow,mul_pow,HEN] at Hsq
  have Hlhs : (diam*W/a.xs^2)^2=diam^2*(W^2/a.xs^4) := by field_simp
  rw [Hlhs,show (L^2)^2=L^4 by ring] at Hsq
  exact Hsq

theorem canonical_high_mass_broad_cut_normalized_le
    (a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0 < C0) (hm : 0 < m) (hN : 1 ≤ a.context.N)
    (hW1 : a.canonicalDirectTestBandScale ≤ 1) {c v cut : ℝ}
    (hc : 0 < c) (hv : 0 < v) (hvlo : c*a.canonicalDirectTestBandScale ≤ v) (hcut : 0 ≤ cut) :
    16*cut*a.canonicalDirectTestBandScale^2/(a.xs^4*v) ≤
      (16*C0^4/c)*a.context.N^4*cut := by
  have hW := a.canonical_direct_test_band_pos
  have hx := a.hxs
  have Hinv4 := a.canonical_high_mass_inverse_power hC0 4
  norm_num only [Nat.cast_ofNat] at Hinv4
  have Hpow : a.context.N^((2:ℝ)/3-4*m) ≤ a.context.N^(4:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have HxInv : 1/a.xs^4 ≤ C0^4*a.context.N^4 := by
    have HH := mul_le_mul_of_nonneg_left Hinv4 (Real.rpow_nonneg a.context.hN.le ((2:ℝ)/3))
    have HE : a.context.N^((2:ℝ)/3)*(1/(a.context.N^((2:ℝ)/3)*a.xs^4))=1/a.xs^4 := by field_simp
    have HE₂ : a.context.N^((2:ℝ)/3)*(C0^4*a.context.N^(-(4:ℝ)*m))=
        C0^4*a.context.N^((2:ℝ)/3-4*m) := by
      calc
        _ = C0^4*(a.context.N^((2:ℝ)/3)*a.context.N^(-(4:ℝ)*m)) := by ring
        _ = _ := by rw [←Real.rpow_add a.context.hN,show (2:ℝ)/3+-(4:ℝ)*m=(2:ℝ)/3-4*m by ring]
    rw [HE,HE₂] at HH
    exact HH.trans (by simpa only [Real.rpow_ofNat] using
      mul_le_mul_of_nonneg_left Hpow (pow_nonneg hC0.le 4))
  have HWv : a.canonicalDirectTestBandScale^2/v ≤ 1/c := by
    have HH : a.canonicalDirectTestBandScale/v ≤ 1/c :=
      (div_le_div_iff₀ hv hc).mpr (by simpa only [one_mul,mul_one,mul_comm] using hvlo)
    have HM := mul_le_mul hW1 HH (div_nonneg hW.le hv.le) zero_le_one
    convert HM using 1 <;> ring
  have Htotal := mul_le_mul HxInv HWv (div_nonneg (sq_nonneg _) hv.le)
    (mul_nonneg (pow_nonneg hC0.le 4) (pow_nonneg a.context.hN.le 4))
  have Hcut := mul_le_mul_of_nonneg_left Htotal (show 0 ≤ 16*cut by positivity)
  convert Hcut using 1 <;> ring

end NativeOverlapMinimum

theorem eventually_chosen_high_mass_diameter_square_polynomial_le
    {m delta cl cu Az C0 Ct D Bclock c Cdiam : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    (hc : 0 < c) (hCdiam : 0 ≤ Cdiam) :
    ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        1 ≤ Real.log a.context.N → 1/a.context.N ≤ a.context.d → a.xs ≤ 1 →
        ∀v : ℝ, 0 < v → c*a.canonicalDirectTestBandScale ≤ v →
          (a.canonicalChosenHighMassDiameter Cdiam v)^2*(a.canonicalDirectTestBandScale^2/a.xs^4) ≤
            a.context.N^(-(32*actualMassSavingExponent m delta)) := by
  have Hb := actualMassSavingExponent_bounds m delta
  have Hroom : 32*actualMassSavingExponent m delta < 2*(3*m+delta) := by
    nlinarith [Hb.2.1,actualMassSavingExponent_pos hm hdelta]
  have Hrate := (tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay Hroom 4 ((2*Cdiam*Ct*C0^3/c)^2))
  filter_upwards [Hrate] with n hn
  intro a hlog hnd hxs1 v hv hvlo
  have hN : 1 ≤ a.context.N := by dsimp [NativeOverlapContext.N]; exact_mod_cast Nat.succ_pos n
  exact (a.canonical_chosen_high_mass_diameter_square_bound hN hlog hnd hCt hC0 hxs1 hCdiam hc hv hvlo).trans
    (by simpa only [NativeOverlapContext.N,neg_mul] using hn)

end OAI.SKFluctuations.LaplaceWindowFormalization
