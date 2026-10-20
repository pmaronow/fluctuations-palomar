module

public import ComparisonNativeActualHighMassOrdinaryRates
public import ComparisonNativeActualHighMassBroadRates
public import SKProof.Port.ComparisonActualOriginalQHighMassNoiseRates
public import SKProof.Port.ComparisonActualOriginalQIntermediateMassNormalization
public import SKProof.Port.ComparisonActualOriginalQIntermediateMassReverseRates
public import SKProof.Port.ComparisonActualOriginalQHighMassReverse
public import SKProof.Port.ComparisonActualOriginalQHighMassDiameter
public import SKProof.Port.ComparisonActualOriginalQLocalDiameterBudgetDefinitions

@[expose] public section

noncomputable section
set_option linter.unusedVariables false

set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_high_mass_inverse_four_coarse
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hC0 : 0 < C0) (hN : 1 ≤ a.data.N) :
    1/a.xs^4 ≤ C0^4*a.data.N^4 := by
  have H:=a.canonical_high_mass_inverse_power hC0 4
  simp only [Nat.cast_ofNat,show (4:ℝ)/6=(2:ℝ)/3 by norm_num] at H
  have HH:=mul_le_mul_of_nonneg_left H (Real.rpow_nonneg a.data.hN.le ((2:ℝ)/3))
  have HE : a.data.N^((2:ℝ)/3)*(1/(a.data.N^((2:ℝ)/3)*a.xs^4))=1/a.xs^4:=by
    field_simp
  have HR : a.data.N^((2:ℝ)/3)*(C0^4*a.data.N^(-(4:ℝ)*m))=
      C0^4*a.data.N^((2:ℝ)/3-4*m):=by
    rw [show a.data.N^((2:ℝ)/3)*(C0^4*a.data.N^(-(4:ℝ)*m))=
      C0^4*(a.data.N^((2:ℝ)/3)*a.data.N^(-4*m)) by ring,←Real.rpow_add a.data.hN]
    rw [show (2:ℝ)/3 + -(4:ℝ)*m=(2:ℝ)/3-4*m by ring]
  rw [HE,HR] at HH
  apply HH.trans
  have Hpow:=Real.rpow_le_rpow_of_exponent_le hN (show (2:ℝ)/3-4*m ≤ 4 by linarith)
  simpa only [Real.rpow_ofNat] using mul_le_mul_of_nonneg_left Hpow (pow_nonneg hC0.le 4)

theorem canonical_high_mass_normalization_weight_le
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hC0 : 0 < C0) (hN : 1 ≤ a.data.N)
    {c v : ℝ} (hc : 0 < c) (hW1 : a.directTestWorkingScale ≤ 1)
    (hv : 0 < v) (hvlo : c*a.directTestWorkingScale ≤ v) :
    a.directTestWorkingScale^2/(a.xs^4*v) ≤ (C0^4/c)*a.data.N^4 := by
  have hW:=a.canonical_direct_test_band_pos
  have hxs:=a.hxs
  have Hvar : a.directTestWorkingScale^2/v ≤ 1/c:=by
    apply (div_le_div_iff₀ hv hc).mpr
    have HS : a.directTestWorkingScale^2 ≤ a.directTestWorkingScale:=by nlinarith
    have H:=mul_le_mul_of_nonneg_left HS hc.le
    nlinarith only [H,hvlo]
  have Hinv:=a.canonical_high_mass_inverse_four_coarse hm hC0 hN
  have H:=mul_le_mul Hvar Hinv (by positivity : 0 ≤ 1/a.xs^4) (one_div_pos.mpr hc).le
  convert H using 1 <;> ring

theorem canonical_high_mass_ordinary_cut_le
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hC0 : 0 < C0) (hN : 1 ≤ a.data.N)
    {Q c v cut : ℝ} (hc : 0 < c) (hW1 : a.directTestWorkingScale ≤ 1)
    (hv : 0 < v) (hv1 : v ≤ 1) (hvlo : c*a.directTestWorkingScale ≤ v)
    (hcut : 0 ≤ cut) :
    (18*(((Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2)^((1:ℝ)/3)+2)*cut)*
      (a.directTestWorkingScale^2/(a.xs^4*v)) ≤
      (18*(1024*Q^4*D^2+3)*C0^4/c)*a.data.N^5*cut := by
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
      1024*Q^4*D^2*a.data.N:=by
    have Hy:=pow_le_pow_left₀ HY HY2 2
    have Hv:=pow_le_pow_left₀ hv.le hv1 2
    have H:=mul_le_mul (mul_le_mul_of_nonneg_left Hpower (show 0 ≤ Q^4*(a.canonicalMassHeight v)^2 by positivity))
      Hv (sq_nonneg v) (show 0 ≤ Q^4*(a.canonicalMassHeight v)^2*(a.data.N*D^2) by positivity)
    have HH:=mul_le_mul_of_nonneg_left Hy (show 0 ≤ Q^4*(a.data.N*D^2) by positivity)
    have HHH:=mul_le_mul_of_nonneg_left H (show 0 ≤ (256:ℝ) by norm_num)
    nlinarith only [HH,HHH]
  have HX0 : 0 ≤ (Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2:=by positivity
  have Hroot:=mass_root_third_le_linear (A:=1024*Q^4*D^2+1) (N:=a.data.N) HX0
    (by nlinarith [mul_nonneg (show 0 ≤ Q^4 by positivity) (sq_nonneg D)])
    hN (by nlinarith only [HX,a.data.hN.le])
  have Hraw : 18*(((Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2)^((1:ℝ)/3)+2)*cut ≤
      (18*(1024*Q^4*D^2+3))*a.data.N*cut:=by
    have Hb : ((Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2)^((1:ℝ)/3)+2 ≤
        (1024*Q^4*D^2+3)*a.data.N:=by nlinarith only [Hroot,hN]
    have H:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hb
      (by norm_num : (0:ℝ) ≤ 18)) hcut
    convert H using 1; ring
  have Hweight:=a.canonical_high_mass_normalization_weight_le hm hC0 hN hc hW1 hv hvlo
  have H:=mul_le_mul Hraw Hweight (by positivity : 0 ≤ a.directTestWorkingScale^2/(a.xs^4*v))
    (show 0 ≤ (18*(1024*Q^4*D^2+3))*a.data.N*cut by positivity)
  convert H using 1; ring

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_chosen_high_mass_diameter_square_bound
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N)
    (hnd : 1/a.data.N ≤ a.data.d) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    (hxs1 : a.xs ≤ 1) {Cdiam c v : ℝ} (hCdiam : 0 ≤ Cdiam) (hc : 0 < c) (hv : 0 < v)
    (hvlo : c*a.directTestWorkingScale ≤ v) :
    (a.canonicalChosenHighMassDiameter Cdiam v)^2*(a.directTestWorkingScale^2/a.xs^4) ≤
      (2*Cdiam*Ct*C0^3/c)^2*(Real.log a.data.N)^4*a.data.N^(-2*(3*m+delta)) := by
  let W := a.directTestWorkingScale
  let diam := a.canonicalChosenHighMassDiameter Cdiam v
  let C := 2*Cdiam*Ct*C0^3
  let L := Real.log a.data.N
  have hW : 0 < W := a.canonical_direct_test_band_pos
  have hx := a.hxs
  have hN0 := a.data.hN
  have hE := a.data.hE
  have hd := a.data.hd
  have hL : 0 ≤ L := zero_le_one.trans hlog
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdiam : 0 ≤ diam := by dsimp [diam,canonicalChosenHighMassDiameter]; positivity
  have Hsource := a.canonical_mass_diameter_source_power_le hN hlog hnd hCt hC0 hxs1 hCdiam hv
  have Hratio : W/v ≤ 1/c := (div_le_div_iff₀ hv hc).mpr (by simpa only [one_mul,mul_one,mul_comm,W] using hvlo)
  have Hmul := mul_le_mul_of_nonneg_right Hsource (show 0 ≤ W/a.xs^2 by positivity)
  have HE : (C*L^2*(a.xs^2/v)*a.data.N^(-(3*m+delta)))*(W/a.xs^2)=
      C*L^2*a.data.N^(-(3*m+delta))*(W/v) := by field_simp
  change diam*(W/a.xs^2) ≤ (C*L^2*(a.xs^2/v)*a.data.N^(-(3*m+delta)))*(W/a.xs^2) at Hmul
  rw [HE] at Hmul
  have Hupper : diam*W/a.xs^2 ≤ (C/c)*L^2*a.data.N^(-(3*m+delta)) := by
    have HH := mul_le_mul_of_nonneg_left Hratio
      (show 0 ≤ C*L^2*a.data.N^(-(3*m+delta)) by positivity)
    have HHmul : diam*W/a.xs^2 ≤ C*L^2*a.data.N^(-(3*m+delta))*(W/v) := by
      simpa only [mul_div_assoc] using Hmul
    apply HHmul.trans
    convert HH using 1
    ring
  have Hsq := pow_le_pow_left₀ (show 0 ≤ diam*W/a.xs^2 by positivity) Hupper 2
  have HEN : (a.data.N^(-(3*m+delta)))^2=a.data.N^(-2*(3*m+delta)) := by
    rw [←Real.rpow_mul_natCast hN0.le]
    congr 1
    ring
  rw [mul_pow,mul_pow,HEN] at Hsq
  have Hlhs : (diam*W/a.xs^2)^2=diam^2*(W^2/a.xs^4) := by field_simp
  rw [Hlhs,show (L^2)^2=L^4 by ring] at Hsq
  exact Hsq

theorem canonical_high_mass_broad_cut_normalized_le
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0 < C0) (hm : 0 < m) (hN : 1 ≤ a.data.N)
    (hW1 : a.directTestWorkingScale ≤ 1) {c v cut : ℝ}
    (hc : 0 < c) (hv : 0 < v) (hvlo : c*a.directTestWorkingScale ≤ v) (hcut : 0 ≤ cut) :
    16*cut*a.directTestWorkingScale^2/(a.xs^4*v) ≤
      (16*C0^4/c)*a.data.N^4*cut := by
  have hW := a.canonical_direct_test_band_pos
  have hx := a.hxs
  have Hinv4 := a.canonical_high_mass_inverse_power hC0 4
  norm_num only [Nat.cast_ofNat] at Hinv4
  have Hpow : a.data.N^((2:ℝ)/3-4*m) ≤ a.data.N^(4:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have HxInv : 1/a.xs^4 ≤ C0^4*a.data.N^4 := by
    have HH := mul_le_mul_of_nonneg_left Hinv4 (Real.rpow_nonneg a.data.hN.le ((2:ℝ)/3))
    have HE : a.data.N^((2:ℝ)/3)*(1/(a.data.N^((2:ℝ)/3)*a.xs^4))=1/a.xs^4 := by field_simp
    have HE₂ : a.data.N^((2:ℝ)/3)*(C0^4*a.data.N^(-(4:ℝ)*m))=
        C0^4*a.data.N^((2:ℝ)/3-4*m) := by
      calc
        _ = C0^4*(a.data.N^((2:ℝ)/3)*a.data.N^(-(4:ℝ)*m)) := by ring
        _ = _ := by rw [←Real.rpow_add a.data.hN,show (2:ℝ)/3+-(4:ℝ)*m=(2:ℝ)/3-4*m by ring]
    rw [HE,HE₂] at HH
    exact HH.trans (by simpa only [Real.rpow_ofNat] using
      mul_le_mul_of_nonneg_left Hpow (pow_nonneg hC0.le 4))
  have HWv : a.directTestWorkingScale^2/v ≤ 1/c := by
    have HH : a.directTestWorkingScale/v ≤ 1/c :=
      (div_le_div_iff₀ hv hc).mpr (by simpa only [one_mul,mul_one,mul_comm] using hvlo)
    have HM := mul_le_mul hW1 HH (div_nonneg hW.le hv.le) zero_le_one
    convert HM using 1 <;> ring
  have Htotal := mul_le_mul HxInv HWv (div_nonneg (sq_nonneg _) hv.le)
    (mul_nonneg (pow_nonneg hC0.le 4) (pow_nonneg a.data.hN.le 4))
  have Hcut := mul_le_mul_of_nonneg_left Htotal (show 0 ≤ 16*cut by positivity)
  convert Hcut using 1 <;> ring

end ActualThetaZeroOverlapMinimum

theorem eventually_chosen_high_mass_diameter_square_polynomial_le_original_q
    {m delta cl cu Az C0 Ct D Bclock c Cdiam : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    (hc : 0 < c) (hCdiam : 0 ≤ Cdiam) :
    ∀ᶠn : ℕ in atTop,
      ∀a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        1 ≤ Real.log a.data.N → 1/a.data.N ≤ a.data.d → a.xs ≤ 1 →
        ∀v : ℝ, 0 < v → c*a.directTestWorkingScale ≤ v →
          (a.canonicalChosenHighMassDiameter Cdiam v)^2*(a.directTestWorkingScale^2/a.xs^4) ≤
            a.data.N^(-(32*actualMassSavingExponent m delta)) := by
  have Hb := actualMassSavingExponent_bounds m delta
  have Hroom : 32*actualMassSavingExponent m delta < 2*(3*m+delta) := by
    nlinarith [Hb.2.1,actualMassSavingExponent_pos hm hdelta]
  have Hrate := (tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay Hroom 4 ((2*Cdiam*Ct*C0^3/c)^2))
  filter_upwards [Hrate] with n hn
  intro a hlog hnd hxs1 v hv hvlo
  have hN : 1 ≤ a.data.N := by dsimp [ActualHighWallData.N]; exact_mod_cast Nat.succ_pos n
  exact (a.canonical_chosen_high_mass_diameter_square_bound hN hlog hnd hCt hC0 hxs1 hCdiam hc hv hvlo).trans
    (by simpa only [ActualHighWallData.N,neg_mul] using hn)

end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

namespace ActualThetaZeroOverlapMinimum

theorem exists_actual_high_mass_reverse_polynomial_order
    {m delta cl cu Az C0 Ct D Bclock Cs c Cdiam : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0) (hD : 0 < D)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hCdiam : 0 < Cdiam) :
    ∃ell : ℕ,2 < ell ∧ ∀Q : ℝ,1 ≤ Q →
      ∀ᶠ n : ℕ in atTop,
        ∀a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
          a.xs ≤ 1 →
          a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs →
          ∀v : ℝ,0 < v → v ≤ 1 → c*a.directTestWorkingScale ≤ v →
            a.canonicalMassReverseAtDiameter ell Q v (a.canonicalChosenHighMassDiameter Cdiam v)*
                (a.directTestWorkingScale^2/a.xs^4) ≤
              a.data.N^(-(32*actualMassSavingExponent m delta)) := by
  let eps0:=delta/64
  let eps:=delta/4
  let k:=delta+2
  obtain ⟨ell,hEll,hgap⟩:=exists_high_mass_reverse_order
    (show 0 ≤ k by dsimp [k];linarith) (show 0 ≤ eps0 by dsimp [eps0];positivity)
    (show 0 < eps by dsimp [eps];positivity) (by dsimp [eps0,eps];linarith)
  refine ⟨ell,hEll,?_⟩
  intro Q hQ
  let e:=2*(ell:ℝ)*eps0/((ell:ℝ)-1)+(1+k)/((ell:ℝ)-1)
  let Cpow:=(2:ℝ)^(2*(ell:ℝ)/((ell:ℝ)-1))
  let Cy:=actualHighMassHeightConstant c
  let Ctotal:=Cpow*Cy*Cdiam*(Cs+1)^2*C0^3
  let eta:=actualMassSavingExponent m delta
  have hEta:=actualMassSavingExponent_bounds m delta
  have hCy : 0 ≤ Cy:=by dsimp [Cy,actualHighMassHeightConstant];positivity
  have htotal : 0 ≤ Ctotal:=by dsimp [Ctotal,Cpow];positivity
  have hsave : 32*eta < 3*m+delta-e:=by
    change e < eps at hgap
    dsimp only [eps] at hgap
    dsimp only [eta]
    nlinarith [hEta.2.2]
  have Hraw:=(tendsto_add_atTop_nat 1).eventually
    (eventually_absorb_fixed_coefficient (e:=0) (eps:=eps0) (by dsimp [eps0];positivity) Q)
  have Hdiam:=eventually_chosen_high_mass_diameter_polynomial_lower
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (Bclock:=Bclock) hm hC0 hD hCdiam
  have Hdecay:=(tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay hsave 1 Ctotal)
  have Hlog:=(tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1:ℝ)))
  filter_upwards [Hraw,Hdiam,Hdecay,Hlog,eventually_ge_atTop (1:ℕ)] with n hnraw hndiam hnrate hnlog hn
  intro a hxs1 hsmall v hv hv1 hvlo
  let W:=a.directTestWorkingScale
  let diam:=a.canonicalChosenHighMassDiameter Cdiam v
  let y:=a.canonicalMassHeight v
  have hN:=a.data.hN
  have hxs:=a.hxs
  have hW : 0 < W:=a.canonical_direct_test_band_pos
  have hN2 : (2:ℝ) ≤ a.data.N:=by
    dsimp [ActualHighWallData.N]
    exact_mod_cast (by omega : 2 ≤ n+1)
  have hlog : 1 ≤ Real.log a.data.N:=hnlog
  have hdiam : 0 < diam:=a.canonical_chosen_high_mass_diameter_pos hCdiam (by linarith) hv
  have hy : 0 < y:=by
    dsimp [y,canonicalMassHeight]
    have hu : 0 ≤ min (16*v) 1:=le_min (by positivity) zero_le_one
    positivity
  have hyN : y ≤ a.data.N:=by
    have Hy : y ≤ 2:=by dsimp [y,canonicalMassHeight];linarith [min_le_right (16*v) 1]
    exact Hy.trans hN2
  have hraw : Q ≤ a.data.N^eps0:=by simpa only [Real.rpow_zero,mul_one] using hnraw
  have hdiamN : a.data.N^(-k) ≤ diam:=hndiam a hlog v hv hv1
  have Hreverse:=mass_reverse_power_extraction (p:=(ell:ℝ)) (a:=1) (k:=k) (eps0:=eps0)
    hN hdiam (zero_lt_one.trans_le hQ) hy
    (by exact_mod_cast hEll) hraw (by simpa only [Real.rpow_one] using hyN) hdiamN
  have Hactual : a.canonicalMassReverseAtDiameter ell Q v diam ≤ Cpow*a.data.N^e*y*diam:=by
    unfold canonicalMassReverseAtDiameter
    have Hpow : (2*Q)^((2:ℝ)*(ell:ℝ))=(2*Q)^(2*ell):=by
      rw [show 2*(ell:ℝ)=((2*ell:ℕ):ℝ) by push_cast;ring,Real.rpow_natCast]
    rw [Hpow,Real.rpow_natCast] at Hreverse
    simpa only [y,Cpow,e] using Hreverse
  have Hxv : c*a.xs ≤ v:=
    (mul_le_mul_of_nonneg_left a.canonical_direct_test_band_ge_scale hc.le).trans hvlo
  have Hy:=a.canonical_high_mass_height_le hc Hxv
  have Hnorm:=mul_le_mul_of_nonneg_right Hactual (show 0 ≤ W^2/a.xs^4 by positivity)
  have HyNorm:=mul_le_mul_of_nonneg_right Hy
    (show 0 ≤ Cpow*a.data.N^e*diam*(W^2/a.xs^4) by dsimp [Cpow];positivity)
  have Hcap:=a.canonical_direct_test_cap_strong_rate hC0 hCs hsmall
  have HcapMul:=mul_le_mul_of_nonneg_left Hcap
    (show 0 ≤ Cpow*a.data.N^e*Cy*Cdiam*Real.log a.data.N*a.data.N^(-delta) by dsimp [Cpow];positivity)
  have HE : Cpow*a.data.N^e*(Cy*v)*diam*(W^2/a.xs^4)=
      (Cpow*a.data.N^e*Cy*Cdiam*Real.log a.data.N*a.data.N^(-delta))*
        ((a.data.E/a.data.d^3)*(W^2/a.xs^4)):=by
    dsimp [diam,canonicalChosenHighMassDiameter]
    rw [Real.rpow_neg hN.le]
    field_simp
  have HE2 : (Cpow*a.data.N^e*Cy*Cdiam*Real.log a.data.N*a.data.N^(-delta))*
      ((Cs+1)^2*C0^3*a.data.N^(-3*m))=
      Ctotal*(Real.log a.data.N)^1*a.data.N^(-(3*m+delta-e)):=by
    dsimp [Ctotal]
    rw [show (Cpow*a.data.N^e*Cy*Cdiam*Real.log a.data.N*a.data.N^(-delta))*
      ((Cs+1)^2*C0^3*a.data.N^(-3*m))=
      (Cpow*Cy*Cdiam*(Cs+1)^2*C0^3)*Real.log a.data.N*
        ((a.data.N^e*a.data.N^(-delta))*a.data.N^(-3*m)) by ring,
      ←Real.rpow_add hN,←Real.rpow_add hN]
    rw [show e + -delta + -3*m=-(3*m+delta-e) by ring,pow_one]
  have Hfinal : a.canonicalMassReverseAtDiameter ell Q v diam*(W^2/a.xs^4) ≤
      Ctotal*(Real.log a.data.N)^1*a.data.N^(-(3*m+delta-e)):=by
    apply Hnorm.trans
    have Hyn : Cpow*a.data.N^e*y*diam*(W^2/a.xs^4) ≤
        Cpow*a.data.N^e*(Cy*v)*diam*(W^2/a.xs^4):=by nlinarith only [HyNorm]
    apply Hyn.trans
    rw [HE]
    exact HcapMul.trans_eq HE2
  exact Hfinal.trans hnrate

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace ActualThetaZeroOverlapMinimum

theorem eventually_high_mass_ordinary_budget_of_reverse_rate
    {m delta cl cu Az C0 Ct D Bclock Cs c Cdiam : ℝ}
    (ell : ℕ) (_hell : 2 < ell) (Q : ℝ)
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hCt : 0 ≤ Ct) (hC0 : 0 < C0) (hCs : 0 ≤ Cs) (hc : 0 < c) (hCdiam : 0 < Cdiam)
    (hreverse : ∀ᶠ n : ℕ in atTop,
      ∀a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.xs ≤ 1 → a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs →
        ∀v : ℝ,0 < v → v ≤ 1 → c*a.directTestWorkingScale ≤ v →
          a.canonicalMassReverseAtDiameter ell Q v (a.canonicalChosenHighMassDiameter Cdiam v)*
            (a.directTestWorkingScale^2/a.xs^4) ≤
              a.data.N^(-(32*actualMassSavingExponent m delta))) :
    ∀ᶠ n : ℕ in atTop,
      ∀a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        1/a.data.N ≤ a.data.d →
        a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs →
        a.directTestWorkingScale ≤ 1 →
        ∀v : ℝ,0 < v → v ≤ 1 → c*a.directTestWorkingScale ≤ v →
          a.canonicalOrdinaryMassBudgetAtDiameter ell Q (10*Real.log a.data.N)
            (a.data.N^(-(10:ℝ))) v (a.canonicalChosenHighMassDiameter Cdiam v)/
              (a.xs^4*v/a.directTestWorkingScale^2) ≤
                a.data.N^(-actualMassSavingExponent m delta) := by
  let eta:=actualMassSavingExponent m delta
  let Cbin:=nativeMassBinLossConstant 10
  let Cerr:=18*(1024*Q^4*D^2+3)*C0^4/c
  have hEta : 0 < eta:=actualMassSavingExponent_pos hm hdelta
  have Heta:=actualMassSavingExponent_bounds m delta
  have hBin : 0 ≤ Cbin:=native_mass_binScaleLoss_constant_nonneg (by norm_num)
  have Hnoise:=eventually_actual_high_mass_noise_polynomial
    (cu:=cu) (D:=D) (Bclock:=Bclock) Q hm hdelta hcl hAz hCt hC0 hCs hc
  have Hdiam:=eventually_chosen_high_mass_diameter_square_polynomial_le_original_q
    (cl:=cl) (cu:=cu) (Az:=Az) (D:=D) (Bclock:=Bclock)
    hm hdelta hCt hC0 hc hCdiam.le
  have Hcut:=(tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=5) (s:=32*eta) (by dsimp [eta];nlinarith [Heta.1]) 0 Cerr)
  have Habs:=(tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=32*eta) (s:=eta) (by linarith) 4 (112*Cbin+1))
  have Hlog:=(tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1:ℝ)))
  filter_upwards [Hnoise,Hdiam,hreverse,Hcut,Habs,Hlog] with n hnNoise hnDiam hnReverse hnCut hnAbs hnLog
  intro a hnd hsmall hW1 v hv hv1 hvlo
  have hN : 1 ≤ a.data.N:=by dsimp [ActualHighWallData.N];exact_mod_cast Nat.succ_pos n
  have hxs:=a.hxs
  have hW:=a.canonical_direct_test_band_pos
  have hxs1:=a.canonical_direct_test_band_ge_scale.trans hW1
  have hlog : 1 ≤ Real.log a.data.N:=hnLog
  have hdiam:=a.canonical_chosen_high_mass_diameter_pos hCdiam (by linarith) hv
  have Hn:=hnNoise a hsmall hW1 v hv hvlo
  have Hd:=hnDiam a hlog hnd hxs1 v hv hvlo
  have Hr:=hnReverse a hxs1 hsmall v hv hv1 hvlo
  have Hbudget:=a.canonical_intermediate_ordinary_budget_normalized_le ell Q 10 (by norm_num)
    hlog (cut:=a.data.N^(-(10:ℝ))) hW hv hdiam.le
  have Hmesh:=a.canonical_high_mass_ordinary_cut_le hm hC0 hN hc hW1 hv hv1 hvlo
    (Real.rpow_nonneg a.data.hN.le (-(10:ℝ))) (Q:=Q)
  have HEcut : (18*(1024*Q^4*D^2+3)*C0^4/c)*a.data.N^5*a.data.N^(-(10:ℝ))=
      Cerr*a.data.N^(-(5:ℝ)):=by
    change Cerr*a.data.N^5*a.data.N^(-(10:ℝ))=Cerr*a.data.N^(-(5:ℝ))
    rw [←Real.rpow_natCast a.data.N 5,mul_assoc,←Real.rpow_add a.data.hN]
    norm_num
  rw [HEcut] at Hmesh
  have HcutFinal:=Hmesh.trans (by simpa only [pow_zero,mul_one] using hnCut)
  have Hsum : 2*(((Q^2*a.canonicalMassHeight v)/(a.canonicalMassPower v*(16*v)^2))^((2:ℝ)/3)*
      (a.directTestWorkingScale^2/a.xs^4))+
      3*((a.directTestWorkingScale^2/a.xs^4)/(a.canonicalMassPower v*(16*v)^2))+
      (a.canonicalChosenHighMassDiameter Cdiam v)^2*(a.directTestWorkingScale^2/a.xs^4)+
      a.canonicalMassReverseAtDiameter ell Q v (a.canonicalChosenHighMassDiameter Cdiam v)*
        (a.directTestWorkingScale^2/a.xs^4) ≤ 7*a.data.N^(-(32*eta)):=by
    nlinarith only [Hn.1,Hn.2.1,Hd,Hr]
  have HsumMul:=mul_le_mul_of_nonneg_left Hsum
    (show 0 ≤ 16*Cbin*(Real.log a.data.N)^4 by positivity)
  have Hmain : a.canonicalOrdinaryMassBudgetAtDiameter ell Q (10*Real.log a.data.N)
      (a.data.N^(-(10:ℝ))) v (a.canonicalChosenHighMassDiameter Cdiam v)/
        (a.xs^4*v/a.directTestWorkingScale^2) ≤
        112*Cbin*(Real.log a.data.N)^4*a.data.N^(-(32*eta))+a.data.N^(-(32*eta)):=by
    nlinarith only [Hbudget,HsumMul,HcutFinal]
  have HlogPow : 1 ≤ (Real.log a.data.N)^4:=one_le_pow₀ hlog
  have Hlast:=mul_le_mul_of_nonneg_right HlogPow (Real.rpow_nonneg a.data.hN.le (-(32*eta)))
  have Htotal : a.canonicalOrdinaryMassBudgetAtDiameter ell Q (10*Real.log a.data.N)
      (a.data.N^(-(10:ℝ))) v (a.canonicalChosenHighMassDiameter Cdiam v)/
        (a.xs^4*v/a.directTestWorkingScale^2) ≤
        (112*Cbin+1)*(Real.log a.data.N)^4*a.data.N^(-(32*eta)):=by
    nlinarith only [Hmain,Hlast]
  exact Htotal.trans hnAbs

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem chosen_high_comparable_broad_budget_polynomial_le
    (ell : ℕ) (_hell : 2 < ell) (Q : ℝ) (_hQ : 1 ≤ Q)
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hCt : 0 ≤ Ct) (hC0 : 0 < C0) {Cs c Cdiam : ℝ}
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hCdiam : 0 < Cdiam)
    (Hreverse : ∀ᶠn : ℕ in atTop,
      ∀a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.xs ≤ 1 → a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs →
        ∀v : ℝ,0 < v → v ≤ 1 → c*a.directTestWorkingScale ≤ v →
          a.canonicalMassReverseAtDiameter ell Q v (a.canonicalChosenHighMassDiameter Cdiam v)*
            (a.directTestWorkingScale^2/a.xs^4) ≤
              a.data.N^(-(32*actualMassSavingExponent m delta))) :
    ∀ᶠn : ℕ in atTop,
      ∀a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        1/a.data.N ≤ a.data.d →
        a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs →
        a.directTestWorkingScale ≤ 1 →
        ∀v width : ℝ,0 < v → v ≤ 1 → c*a.directTestWorkingScale ≤ v →
          v ≤ width → width ≤ 4*v → width ≤ 1 →
          a.canonicalComparableBroadMassBudgetAtDiameter ell Q (10*Real.log a.data.N)
            (a.data.N^(-(10:ℝ))) v width (a.canonicalChosenHighMassDiameter Cdiam v)/
              (a.xs^4*v/a.directTestWorkingScale^2) ≤
                a.data.N^(-actualMassSavingExponent m delta) := by
  let eta := actualMassSavingExponent m delta
  let loss := nativeOuterComparableTraceConstant cl cu
  let Cfinite := nativeHighMassBroadFiniteConstant 10
  let Cerr := 16*C0^4/c
  let Ctotal := Cfinite*(256*loss+2)+Cerr
  have heta : 0 < eta := actualMassSavingExponent_pos hm hdelta
  have HCfinite : 0 ≤ Cfinite := native_high_mass_broad_finite_constant_nonneg (by norm_num)
  have HCerr : 0 ≤ Cerr := by dsimp [Cerr];positivity
  have HCloss : 0 ≤ loss := native_outer_comparable_trace_constant_nonneg hcl hcu
  have Hsquare := eventually_chosen_high_mass_diameter_square_polynomial_le_original_q
    (cl:=cl) (cu:=cu) (Az:=Az) (D:=D) (Bclock:=Bclock)
    hm hdelta hCt hC0 hc hCdiam.le
  have Hnoise := eventually_actual_high_mass_noise_polynomial
    (cu:=cu) (D:=D) (Bclock:=Bclock) Q hm hdelta hcl hAz hCt hC0 hCs hc
  have Hdecay := (tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=32*eta) (s:=eta) (by linarith) 5 Ctotal)
  have Hlog := (tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1:ℝ)))
  filter_upwards [Hreverse,Hsquare,Hnoise,Hdecay,Hlog] with n hnReverse hnSquare hnNoise hnRate hnLog
  intro a hnd hsmall hW1 v width hv hv1 hvlo hwlo hwhi hw1
  let W := a.directTestWorkingScale
  let B := W
  let diam := a.canonicalChosenHighMassDiameter Cdiam v
  let tau := B^2/(a.canonicalMassPower v*v^2*a.xs^4)
  let L := Real.log a.data.N
  have hN : 1 ≤ a.data.N := by dsimp [ActualHighWallData.N];exact_mod_cast Nat.succ_pos n
  have hN0 := a.data.hN
  have hW : 0 < W := a.canonical_direct_test_band_pos
  have hB : 0 < B := hW
  have hP := a.canonical_mass_power_pos v
  have hxs := a.hxs
  have hxs1 := a.canonical_direct_test_band_ge_scale.trans hW1
  have hlog : 1 ≤ Real.log a.data.N := hnLog
  have hcut : 0 < a.data.N^(-(10:ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hwidth : 0 < width := hv.trans_le hwlo
  have hdiam : 0 < diam := a.canonical_chosen_high_mass_diameter_pos hCdiam (by linarith) hv
  have hwidthlog : Real.log (width/a.data.N^(-(10:ℝ))) ≤ 10*Real.log a.data.N := by
    have HH := Real.log_le_log (div_pos hwidth hcut) (div_le_div_of_nonneg_right hw1 hcut.le)
    apply HH.trans_eq
    rw [one_div,Real.log_inv,Real.log_rpow hN0]
    ring
  have hEven : 0 ≤ (2*Q)^(2*ell) := by rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
  have hy : 0 ≤ a.canonicalMassHeight v := by unfold canonicalMassHeight;positivity
  have hR : 0 ≤ a.canonicalMassReverseAtDiameter ell Q v diam := by
    unfold canonicalMassReverseAtDiameter
    exact mul_nonneg (Real.rpow_nonneg hdiam.le _)
      (Real.rpow_nonneg (mul_nonneg hEven (pow_nonneg hy ell)) _)
  have Hnorm := mass_high_broad_finite_normalized_le a.hxs hB (a.canonical_mass_power_pos v)
    hv hwidth.le hwhi hdiam.le hR HCloss hlog (by norm_num : (0:ℝ) ≤ 10) hwidthlog
  change a.canonicalComparableBroadMassBudgetAtDiameter ell Q (10*Real.log a.data.N)
      (a.data.N^(-(10:ℝ))) v width diam/(a.xs^4*v/B^2) ≤
      Cfinite*L^5*(loss*tau/L+diam^2*B^2/a.xs^4+
        a.canonicalMassReverseAtDiameter ell Q v diam*B^2/a.xs^4)+
      16*a.data.N^(-(10:ℝ))*B^2/(a.xs^4*v) at Hnorm
  have Htau : tau ≤ 256*a.data.N^(-(32*eta)) := by
    have HH := (hnNoise a hsmall hW1 v hv hvlo).2.1
    have HM := mul_le_mul_of_nonneg_left HH (by norm_num : (0:ℝ) ≤ 256)
    convert HM using 1 <;> dsimp only [tau,B,W] <;> ring
  have Htrace : loss*tau/L ≤ (256*loss)*a.data.N^(-(32*eta)) := by
    apply (div_le_self (mul_nonneg HCloss (by dsimp [tau];positivity)) hlog).trans
    convert mul_le_mul_of_nonneg_left Htau HCloss using 1 <;> ring
  have HDsaved : diam^2*B^2/a.xs^4 ≤ a.data.N^(-(32*eta)) := by
    simpa only [mul_div_assoc,B,W] using hnSquare a hlog hnd hxs1 v hv hvlo
  have HRsaved : a.canonicalMassReverseAtDiameter ell Q v diam*B^2/a.xs^4 ≤
      a.data.N^(-(32*eta)) := by
    simpa only [mul_div_assoc] using hnReverse a hxs1 hsmall v hv hv1 hvlo
  have Hmain := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add Htrace HDsaved) HRsaved)
    (show 0 ≤ Cfinite*L^5 by exact mul_nonneg HCfinite (pow_nonneg (by linarith) _))
  have Hcut : 16*a.data.N^(-(10:ℝ))*B^2/(a.xs^4*v) ≤
      Cerr*a.data.N^4*a.data.N^(-(10:ℝ)) := by
    simpa only [B,W,Cerr] using a.canonical_high_mass_broad_cut_normalized_le hC0 hm hN hW1 hc hv hvlo hcut.le
  have Hpowcut : a.data.N^4*a.data.N^(-(10:ℝ))=a.data.N^(-(6:ℝ)) := by
    rw [←Real.rpow_natCast a.data.N 4,←Real.rpow_add hN0]
    norm_num
  have Hbounds := actualMassSavingExponent_bounds m delta
  have HcutPower : a.data.N^(-(6:ℝ)) ≤ a.data.N^(-(32*eta)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by dsimp [eta];nlinarith [Hbounds.1])
  have HcutLog : 1 ≤ L^5 := one_le_pow₀ hlog
  have HCnormal : 16*a.data.N^(-(10:ℝ))*B^2/(a.xs^4*v) ≤ Cerr*L^5*a.data.N^(-(32*eta)) := by
    apply Hcut.trans
    rw [mul_assoc,Hpowcut]
    have HH := mul_le_mul_of_nonneg_left HcutPower HCerr
    have HL := mul_le_mul_of_nonneg_left HcutLog
      (show 0 ≤ Cerr*a.data.N^(-(32*eta)) by positivity)
    nlinarith only [HH,HL]
  have Htotal : a.canonicalComparableBroadMassBudgetAtDiameter ell Q (10*Real.log a.data.N)
      (a.data.N^(-(10:ℝ))) v width diam/(a.xs^4*v/B^2) ≤
        Ctotal*L^5*a.data.N^(-(32*eta)) := by
    apply Hnorm.trans
    have HH := add_le_add Hmain HCnormal
    convert HH using 1
    dsimp [Ctotal]
    ring
  exact Htotal.trans (by simpa only [ActualHighWallData.N] using hnRate)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
