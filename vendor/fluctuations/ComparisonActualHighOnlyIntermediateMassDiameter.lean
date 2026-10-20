module

public import ComparisonNativeActualIntermediateMassDiameter
public import ComparisonActualHighOnlyHighMassReverse
public import ComparisonActualHighOnlyHighMassCriticalRates

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

theorem eventually_actual_intermediate_mass_diameter_polynomial
    {m delta cl cu Az C0 Ct D Bclock Cs c C Cdiam : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hCdiam : 0 < Cdiam) :
    ∀ᶠn : ℕ in atTop,
      ∀a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs →
        a.canonicalDirectTestBandScale ≤ 1 →
        ∀v : ℝ,c*a.xs ≤ v → v ≤ C*a.canonicalDirectTestBandScale →
          a.canonicalChosenHighMassDiameter Cdiam v ≤ v ∧
          (a.canonicalChosenHighMassDiameter Cdiam v)^2*
            ((actualIntermediateMassEffectiveScale a.canonicalDirectTestBandScale v)^2/a.xs^4) ≤
              a.data.N^(-(32*actualMassSavingExponent m delta)) := by
  let Csource := 2*Cdiam*Ct*C0^3
  let K := max (1:ℝ) C
  let Cfinal := K^2*Cdiam*(Cs+1)^2*C0^3
  let eta := actualMassSavingExponent m delta
  have Heta := actualMassSavingExponent_bounds m delta
  have Hsmall := (tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=3*m+delta) (s:=0) (by linarith) 2 (Csource/c^2))
  have Hrate := (tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=3*m+delta) (s:=32*eta)
      (by dsimp [eta];nlinarith [Heta.2.1]) 1 Cfinal)
  have Hlog := (tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1:ℝ)))
  have Hdepth := (tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  filter_upwards [Hsmall,Hrate,Hlog,Hdepth] with n hnSmall hnRate hnLog hnDepth
  intro a hsmall hW1 v hvlo hvupper
  let W := a.canonicalDirectTestBandScale
  let B := actualIntermediateMassEffectiveScale W v
  let diam := a.canonicalChosenHighMassDiameter Cdiam v
  have hx := a.hxs
  have hW : 0 < W := a.canonical_direct_test_band_pos
  have hv : 0 < v := (mul_pos hc hx).trans_le hvlo
  have hN0 := a.data.hN
  have hd := a.data.hd
  have hE := a.data.hE
  have hN : 1 ≤ a.data.N := by dsimp [ActualHighOnlyComparisonData.N];exact_mod_cast Nat.succ_pos n
  have hlog : 1 ≤ Real.log a.data.N := hnLog
  have hlog0 : 0 ≤ Real.log a.data.N := zero_le_one.trans hlog
  have hnd : 1/a.data.N ≤ a.data.d := by
    have HD := hnDepth a.data.E a.data.d a.data.hE a.data.hd a.hlower
    have HE : comparisonLowerScale a.data.N a.data.E a.data.d ≤ a.data.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ a.data.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact HD.trans HE
  have hxs1 := a.canonical_direct_test_band_ge_scale.trans hW1
  have hdiam : 0 < diam := a.canonical_chosen_high_mass_diameter_pos hCdiam (by linarith) hv
  have Hsource := a.canonical_mass_diameter_source_power_le hN hlog hnd hCt hC0 hxs1 hCdiam.le hv
  change diam ≤ Csource*(Real.log a.data.N)^2*(a.xs^2/v)*a.data.N^(-(3*m+delta)) at Hsource
  have Hratio : a.xs^2/v ≤ v/c^2 := by
    apply (div_le_div_iff₀ hv (sq_pos_of_pos hc)).mpr
    have HH := pow_le_pow_left₀ (mul_pos hc hx).le hvlo 2
    nlinarith only [HH]
  have Hcoeff : (Csource/c^2)*(Real.log a.data.N)^2*a.data.N^(-(3*m+delta)) ≤ 1 := by
    simpa only [ActualHighOnlyComparisonData.N,Real.rpow_zero,neg_zero] using hnSmall
  have HdiamV : diam ≤ v := by
    apply Hsource.trans
    have HH := mul_le_mul_of_nonneg_left Hratio
      (show 0 ≤ Csource*(Real.log a.data.N)^2*a.data.N^(-(3*m+delta)) by dsimp [Csource];positivity)
    have HC := mul_le_mul_of_nonneg_right Hcoeff hv.le
    have Hfirst : Csource*(Real.log a.data.N)^2*(a.xs^2/v)*a.data.N^(-(3*m+delta)) ≤
        ((Csource/c^2)*(Real.log a.data.N)^2*a.data.N^(-(3*m+delta)))*v := by
      convert HH using 1 <;> ring
    exact Hfirst.trans (by simpa only [one_mul] using HC)
  have Hsquare : diam^2 ≤ v*diam := by nlinarith only [mul_le_mul_of_nonneg_right HdiamV hdiam.le]
  have HB := (actualIntermediateMassEffectiveScale_upper hW hv hvupper).2
  have Hnorm := mul_le_mul_of_nonneg_right Hsquare (show 0 ≤ B^2/a.xs^4 by positivity)
  have HnormB := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right HB (pow_pos hx 4).le) (mul_pos hv hdiam).le
  have Hcap := a.canonical_direct_test_cap_strong_rate hC0 hCs hsmall
  have HcapMul := mul_le_mul_of_nonneg_left Hcap
    (show 0 ≤ K^2*Cdiam*Real.log a.data.N*a.data.N^(-delta) by dsimp [K];positivity)
  have HE : (v*diam)*(K^2*W^2/a.xs^4)=
      (K^2*Cdiam*Real.log a.data.N*a.data.N^(-delta))*
        ((a.data.E/a.data.d^3)*(W^2/a.xs^4)) := by
    dsimp [diam,canonicalChosenHighMassDiameter]
    rw [Real.rpow_neg hN0.le]
    field_simp
  have HE2 : (K^2*Cdiam*Real.log a.data.N*a.data.N^(-delta))*
      ((Cs+1)^2*C0^3*a.data.N^(-3*m))=
      Cfinal*Real.log a.data.N*a.data.N^(-(3*m+delta)) := by
    dsimp only [Cfinal]
    have HP : a.data.N^(-delta)*a.data.N^(-3*m)=a.data.N^(-(3*m+delta)) := by
      rw [←Real.rpow_add hN0]
      congr 1
      ring
    calc
      _ = (K^2*Cdiam*(Cs+1)^2*C0^3)*Real.log a.data.N*
        (a.data.N^(-delta)*a.data.N^(-3*m)) := by ring
      _ = _ := by rw [HP]
  have Hnormalized : diam^2*(B^2/a.xs^4) ≤
      Cfinal*Real.log a.data.N*a.data.N^(-(3*m+delta)) := by
    apply Hnorm.trans
    apply HnormB.trans
    rw [HE]
    exact HcapMul.trans_eq HE2
  refine ⟨HdiamV,Hnormalized.trans ?_⟩
  simpa only [ActualHighOnlyComparisonData.N,pow_one] using hnRate

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
