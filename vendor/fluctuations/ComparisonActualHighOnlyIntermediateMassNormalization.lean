module

public import ComparisonNativeActualIntermediateMassNormalization
public import ComparisonActualHighOnlyLocalDiameterBudgetDefinitions
public import ComparisonActualHighOnlyHighMassCriticalRates
public import ComparisonActualHighOnlyMassBudgetScale

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

theorem canonical_intermediate_ordinary_budget_normalized_le
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    (hlog : 1 ≤ Real.log a.data.N) {B v diam cut : ℝ} (hB : 0 < B)
    (hv : 0 < v) (hdiam : 0 ≤ diam) :
    a.canonicalOrdinaryMassBudgetAtDiameter ell Q (Ccut*Real.log a.data.N) cut v diam/
        (a.xs^4*v/B^2) ≤
      (16*nativeMassBinLossConstant Ccut)*(Real.log a.data.N)^4*
        (2*(((Q^2*a.canonicalMassHeight v)/(a.canonicalMassPower v*(16*v)^2))^((2:ℝ)/3)*
              (B^2/a.xs^4))+
          3*((B^2/a.xs^4)/(a.canonicalMassPower v*(16*v)^2))+
          diam^2*(B^2/a.xs^4)+
          a.canonicalMassReverseAtDiameter ell Q v diam*(B^2/a.xs^4))+
      (18*(((Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2)^((1:ℝ)/3)+2)*cut)*
        (B^2/(a.xs^4*v)) := by
  have Hnorm:=mass_high_ordinary_normalization (P:=a.canonicalMassPower v)
    (y:=a.canonicalMassHeight v) (Q:=Q) (diam:=diam)
    (rev:=a.canonicalMassReverseAtDiameter ell Q v diam)
    (F:=nativeBinScaleLoss (Ccut*Real.log a.data.N) (108*32^2*(Real.log a.data.N)^2)
      (54*32^2*(Real.log a.data.N)^2) (16*v) (v/4)) (cut:=cut)
    a.hxs hB hv
  unfold canonicalOrdinaryMassBudgetAtDiameter
  rw [Hnorm]
  have HF:=native_mass_binScaleLoss_log_bound hCcut hlog hv
  have hP:=a.canonical_mass_power_pos v
  have hxs:=a.hxs
  have hW:=hB
  have hy : 0 ≤ a.canonicalMassHeight v:=by unfold canonicalMassHeight;positivity
  have hEven : 0 ≤ (2*Q)^(2*ell):=by rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
  have hR : 0 ≤ a.canonicalMassReverseAtDiameter ell Q v diam:=by
    unfold canonicalMassReverseAtDiameter
    exact mul_nonneg (Real.rpow_nonneg hdiam _)
      (Real.rpow_nonneg (mul_nonneg hEven (pow_nonneg hy ell)) _)
  have H:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left HF (by norm_num : (0:ℝ) ≤ 16))
    (show 0 ≤ 2*(((Q^2*a.canonicalMassHeight v)/(a.canonicalMassPower v*(16*v)^2))^((2:ℝ)/3)*
        (B^2/a.xs^4))+
      3*((B^2/a.xs^4)/(a.canonicalMassPower v*(16*v)^2))+
      diam^2*(B^2/a.xs^4)+
      a.canonicalMassReverseAtDiameter ell Q v diam*(B^2/a.xs^4) by positivity)
  nlinarith only [H]

theorem canonical_intermediate_inverse_five_coarse
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hC0 : 0 < C0) (hN : 1 ≤ a.data.N) :
    1/a.xs^5 ≤ C0^5*a.data.N^5 := by
  have H := a.canonical_high_mass_inverse_power hC0 5
  simp only [Nat.cast_ofNat] at H
  have HH := mul_le_mul_of_nonneg_left H (Real.rpow_nonneg a.data.hN.le ((5:ℝ)/6))
  have HE : a.data.N^((5:ℝ)/6)*(1/(a.data.N^((5:ℝ)/6)*a.xs^5))=1/a.xs^5 := by
    field_simp
  have HR : a.data.N^((5:ℝ)/6)*(C0^5*a.data.N^(-(5:ℝ)*m))=
      C0^5*a.data.N^((5:ℝ)/6-5*m) := by
    rw [show a.data.N^((5:ℝ)/6)*(C0^5*a.data.N^(-(5:ℝ)*m))=
      C0^5*(a.data.N^((5:ℝ)/6)*a.data.N^(-5*m)) by ring,←Real.rpow_add a.data.hN]
    rw [show (5:ℝ)/6 + -(5:ℝ)*m=(5:ℝ)/6-5*m by ring]
  rw [HE,HR] at HH
  apply HH.trans
  have Hpow := Real.rpow_le_rpow_of_exponent_le hN (show (5:ℝ)/6-5*m ≤ 5 by linarith)
  simpa only [Real.rpow_ofNat] using mul_le_mul_of_nonneg_left Hpow (pow_nonneg hC0.le 5)

theorem canonical_intermediate_normalization_weight_le
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hC0 : 0 < C0) (hN : 1 ≤ a.data.N)
    {c C v : ℝ} (hc : 0 < c) (hW1 : a.canonicalDirectTestBandScale ≤ 1)
    (hvlo : c*a.xs ≤ v) (hvupper : v ≤ C*a.canonicalDirectTestBandScale) :
    (actualIntermediateMassEffectiveScale a.canonicalDirectTestBandScale v)^2/(a.xs^4*v) ≤
      ((max 1 C)^2*C0^5/c)*a.data.N^5 := by
  let W := a.canonicalDirectTestBandScale
  let B := actualIntermediateMassEffectiveScale W v
  let K := max (1:ℝ) C
  have hx := a.hxs
  have hW : 0 < W := a.canonical_direct_test_band_pos
  have hv : 0 < v := (mul_pos hc hx).trans_le hvlo
  have HB := (actualIntermediateMassEffectiveScale_upper hW hv hvupper).2
  have HWsq : W^2 ≤ 1 := by nlinarith only [hW1,hW]
  have HBsq : B^2 ≤ K^2 := HB.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left HWsq (sq_nonneg K))
  have Hnorm : B^2/(a.xs^4*v) ≤ (K^2/c)*(1/a.xs^5) := by
    rw [div_mul_div_comm,mul_one]
    apply (div_le_div_iff₀ (show 0 < a.xs^4*v by positivity)
      (show 0 < c*a.xs^5 by positivity)).mpr
    have H1 := mul_le_mul_of_nonneg_right HBsq (show 0 ≤ c*a.xs^5 by positivity)
    have H2 := mul_le_mul_of_nonneg_left hvlo (show 0 ≤ K^2*a.xs^4 by positivity)
    nlinarith only [H1,H2]
  have Hinv := a.canonical_intermediate_inverse_five_coarse hm hC0 hN
  have HH := mul_le_mul_of_nonneg_left Hinv (show 0 ≤ K^2/c by positivity)
  apply Hnorm.trans
  convert HH using 1; dsimp only [K]; ring

theorem canonical_intermediate_ordinary_cut_le
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hC0 : 0 < C0) (hN : 1 ≤ a.data.N)
    {Q c C v cut : ℝ} (hc : 0 < c) (hW1 : a.canonicalDirectTestBandScale ≤ 1)
    (hv : 0 < v) (hv1 : v ≤ 1) (hvlo : c*a.xs ≤ v) (hvupper : v ≤ C*a.canonicalDirectTestBandScale)
    (hcut : 0 ≤ cut) :
    (18*(((Q^2*a.canonicalMassHeight v)^2*a.canonicalMassPower v*(16*v)^2)^((1:ℝ)/3)+2)*cut)*
      ((actualIntermediateMassEffectiveScale a.canonicalDirectTestBandScale v)^2/(a.xs^4*v)) ≤
      (18*(1024*Q^4*D^2+3)*(max 1 C)^2*C0^5/c)*a.data.N^6*cut := by
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
  have Hweight:=a.canonical_intermediate_normalization_weight_le hm hC0 hN hc hW1 hvlo hvupper
  have H:=mul_le_mul Hraw Hweight (by positivity : 0 ≤ (actualIntermediateMassEffectiveScale a.canonicalDirectTestBandScale v)^2/(a.xs^4*v))
    (show 0 ≤ (18*(1024*Q^4*D^2+3))*a.data.N*cut by positivity)
  convert H using 1; ring

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
