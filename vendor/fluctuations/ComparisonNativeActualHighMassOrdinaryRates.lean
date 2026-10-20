module

public import ComparisonNativeActualHighMassNoiseRates
public import ComparisonNativeActualHighMassMesh
public import ComparisonNativeActualHighMassReverseRates
public import ComparisonNativeActualHighMassBroadScale

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace NativeOverlapMinimum

theorem eventually_high_mass_ordinary_budget_of_reverse_rate
    {m delta cl cu Az C0 Ct D Bclock Cs c Cdiam : ℝ}
    (ell : ℕ) (_hell : 2 < ell) (Q : ℝ)
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hCt : 0 ≤ Ct) (hC0 : 0 < C0) (hCs : 0 ≤ Cs) (hc : 0 < c) (hCdiam : 0 < Cdiam)
    (hreverse : ∀ᶠ n : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.xs ≤ 1 → a.xs^2 ≤ Cs*laplaceComparisonStrength a.context.d a.lam a.xs →
        ∀v : ℝ,0 < v → v ≤ 1 → c*a.canonicalDirectTestBandScale ≤ v →
          a.canonicalMassReverseAtDiameter ell Q v (a.canonicalChosenHighMassDiameter Cdiam v)*
            (a.canonicalDirectTestBandScale^2/a.xs^4) ≤
              a.context.N^(-(32*actualMassSavingExponent m delta))) :
    ∀ᶠ n : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        1/a.context.N ≤ a.context.d →
        a.xs^2 ≤ Cs*laplaceComparisonStrength a.context.d a.lam a.xs →
        a.canonicalDirectTestBandScale ≤ 1 →
        ∀v : ℝ,0 < v → v ≤ 1 → c*a.canonicalDirectTestBandScale ≤ v →
          a.canonicalOrdinaryMassBudgetAtDiameter ell Q (10*Real.log a.context.N)
            (a.context.N^(-(10:ℝ))) v (a.canonicalChosenHighMassDiameter Cdiam v)/
              (a.xs^4*v/a.canonicalDirectTestBandScale^2) ≤
                a.context.N^(-actualMassSavingExponent m delta) := by
  let eta:=actualMassSavingExponent m delta
  let Cbin:=nativeMassBinLossConstant 10
  let Cerr:=18*(1024*Q^4*D^2+3)*C0^4/c
  have hEta : 0 < eta:=actualMassSavingExponent_pos hm hdelta
  have Heta:=actualMassSavingExponent_bounds m delta
  have hBin : 0 ≤ Cbin:=native_mass_binScaleLoss_constant_nonneg (by norm_num)
  have Hnoise:=eventually_actual_high_mass_noise_polynomial
    (cu:=cu) (D:=D) (Bclock:=Bclock) Q hm hdelta hcl hAz hCt hC0 hCs hc
  have Hdiam:=eventually_chosen_high_mass_diameter_square_polynomial_le
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
  have hN : 1 ≤ a.context.N:=by dsimp [NativeOverlapContext.N];exact_mod_cast Nat.succ_pos n
  have hxs:=a.hxs
  have hW:=a.canonical_direct_test_band_pos
  have hxs1:=a.canonical_direct_test_band_ge_scale.trans hW1
  have hlog : 1 ≤ Real.log a.context.N:=hnLog
  have hdiam:=a.canonical_chosen_high_mass_diameter_pos hCdiam (by linarith) hv
  have Hn:=hnNoise a hsmall hW1 v hv hvlo
  have Hd:=hnDiam a hlog hnd hxs1 v hv hvlo
  have Hr:=hnReverse a hxs1 hsmall v hv hv1 hvlo
  have Hbudget:=a.canonical_high_mass_ordinary_budget_normalized_le ell Q 10 (by norm_num)
    hlog (cut:=a.context.N^(-(10:ℝ))) hv hdiam.le
  have Hmesh:=a.canonical_high_mass_ordinary_cut_le hm hC0 hN hc hW1 hv hv1 hvlo
    (Real.rpow_nonneg a.context.hN.le (-(10:ℝ))) (Q:=Q)
  have HEcut : (18*(1024*Q^4*D^2+3)*C0^4/c)*a.context.N^5*a.context.N^(-(10:ℝ))=
      Cerr*a.context.N^(-(5:ℝ)):=by
    change Cerr*a.context.N^5*a.context.N^(-(10:ℝ))=Cerr*a.context.N^(-(5:ℝ))
    rw [←Real.rpow_natCast a.context.N 5,mul_assoc,←Real.rpow_add a.context.hN]
    norm_num
  rw [HEcut] at Hmesh
  have HcutFinal:=Hmesh.trans (by simpa only [pow_zero,mul_one] using hnCut)
  have Hsum : 2*(((Q^2*a.canonicalMassHeight v)/(a.canonicalMassPower v*(16*v)^2))^((2:ℝ)/3)*
      (a.canonicalDirectTestBandScale^2/a.xs^4))+
      3*((a.canonicalDirectTestBandScale^2/a.xs^4)/(a.canonicalMassPower v*(16*v)^2))+
      (a.canonicalChosenHighMassDiameter Cdiam v)^2*(a.canonicalDirectTestBandScale^2/a.xs^4)+
      a.canonicalMassReverseAtDiameter ell Q v (a.canonicalChosenHighMassDiameter Cdiam v)*
        (a.canonicalDirectTestBandScale^2/a.xs^4) ≤ 7*a.context.N^(-(32*eta)):=by
    nlinarith only [Hn.1,Hn.2.1,Hd,Hr]
  have HsumMul:=mul_le_mul_of_nonneg_left Hsum
    (show 0 ≤ 16*Cbin*(Real.log a.context.N)^4 by positivity)
  have Hmain : a.canonicalOrdinaryMassBudgetAtDiameter ell Q (10*Real.log a.context.N)
      (a.context.N^(-(10:ℝ))) v (a.canonicalChosenHighMassDiameter Cdiam v)/
        (a.xs^4*v/a.canonicalDirectTestBandScale^2) ≤
        112*Cbin*(Real.log a.context.N)^4*a.context.N^(-(32*eta))+a.context.N^(-(32*eta)):=by
    nlinarith only [Hbudget,HsumMul,HcutFinal]
  have HlogPow : 1 ≤ (Real.log a.context.N)^4:=one_le_pow₀ hlog
  have Hlast:=mul_le_mul_of_nonneg_right HlogPow (Real.rpow_nonneg a.context.hN.le (-(32*eta)))
  have Htotal : a.canonicalOrdinaryMassBudgetAtDiameter ell Q (10*Real.log a.context.N)
      (a.context.N^(-(10:ℝ))) v (a.canonicalChosenHighMassDiameter Cdiam v)/
        (a.xs^4*v/a.canonicalDirectTestBandScale^2) ≤
        (112*Cbin+1)*(Real.log a.context.N)^4*a.context.N^(-(32*eta)):=by
    nlinarith only [Hmain,Hlast]
  exact Htotal.trans hnAbs

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
