module

public import ComparisonNativeActualIntermediateMassReverseRates
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

theorem exists_actual_intermediate_mass_reverse_high_clock_order
    {m delta cl cu Az C0 Ct D Bclock Cs c Cdiam : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0) (hD : 0 < D)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hCdiam : 0 < Cdiam) :
    ∃ell : ℕ,2 < ell ∧ ∀Q : ℝ,1 ≤ Q →
      ∀ᶠ n : ℕ in atTop,
        ∀a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
          a.xs ≤ 1 →
          a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs →
          ∀v : ℝ,0 < v → v ≤ 1 → c*a.xs ≤ v →
            a.canonicalMassReverseAtDiameter ell Q v (a.canonicalChosenHighMassDiameter Cdiam v)*
                (a.canonicalDirectTestBandScale^2/a.xs^4) ≤
              a.data.N^(-(64*actualMassSavingExponent m delta)) := by
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
  have hsave : 64*eta < 3*m+delta-e:=by
    change e < eps at hgap
    dsimp only [eps] at hgap
    dsimp only [eta]
    nlinarith [hEta.2.1,hEta.2.2]
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
  let W:=a.canonicalDirectTestBandScale
  let diam:=a.canonicalChosenHighMassDiameter Cdiam v
  let y:=a.canonicalMassHeight v
  have hN:=a.data.hN
  have hxs:=a.hxs
  have hW : 0 < W:=a.canonical_direct_test_band_pos
  have hN2 : (2:ℝ) ≤ a.data.N:=by
    dsimp [ActualHighOnlyComparisonData.N]
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
  have Hy:=a.canonical_high_mass_height_le hc hvlo
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

theorem exists_actual_intermediate_mass_reverse_polynomial_order
    {m delta cl cu Az C0 Ct D Bclock Cs c Cdiam : ℝ}
    (C : ℝ) (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0) (hD : 0 < D)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hCdiam : 0 < Cdiam) :
    ∃ell : ℕ,2 < ell ∧ ∀Q : ℝ,1 ≤ Q →
      ∀ᶠ n : ℕ in atTop,
        ∀a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
          a.xs ≤ 1 →
          a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs →
          ∀v : ℝ,0 < v → v ≤ 1 → c*a.xs ≤ v → v ≤ C*a.canonicalDirectTestBandScale →
            a.canonicalMassReverseAtDiameter ell Q v (a.canonicalChosenHighMassDiameter Cdiam v)*
              ((actualIntermediateMassEffectiveScale a.canonicalDirectTestBandScale v)^2/a.xs^4) ≤
                a.data.N^(-(32*actualMassSavingExponent m delta)) := by
  obtain ⟨ell,hEll,Horder⟩ := exists_actual_intermediate_mass_reverse_high_clock_order
    (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (Bclock:=Bclock) hm hdelta hC0 hD hCs hc hCdiam
  refine ⟨ell,hEll,?_⟩
  intro Q hQ
  let eta := actualMassSavingExponent m delta
  have heta := actualMassSavingExponent_pos hm hdelta
  have Habsorb := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=(max (1:ℝ) C)^2) (d:=1)
      (q:=-(64*eta)) (r:=-(32*eta)) zero_lt_one (by dsimp [eta];nlinarith))
  have Hlog := (tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1:ℝ)))
  filter_upwards [Horder Q hQ,Habsorb,Hlog] with n hnOrder hnAbsorb hnLog
  intro a hxs1 hsmall v hv hv1 hvlo hvhi
  let W := a.canonicalDirectTestBandScale
  let diam := a.canonicalChosenHighMassDiameter Cdiam v
  have hW : 0 < W := a.canonical_direct_test_band_pos
  have hlog : 1 ≤ Real.log a.data.N := hnLog
  have hdiam : 0 < diam := a.canonical_chosen_high_mass_diameter_pos hCdiam (by linarith) hv
  have hy : 0 ≤ a.canonicalMassHeight v := by
    unfold canonicalMassHeight
    exact add_nonneg a.hxs.le (le_min (by positivity) zero_le_one)
  have hR : 0 ≤ a.canonicalMassReverseAtDiameter ell Q v diam := by
    unfold canonicalMassReverseAtDiameter
    have hEven : 0 ≤ (2*Q)^(2*ell) := by rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
    exact mul_nonneg (Real.rpow_nonneg hdiam.le _)
      (Real.rpow_nonneg (mul_nonneg hEven (pow_nonneg hy ell)) _)
  have Hscale := (actualIntermediateMassEffectiveScale_upper hW hv hvhi).2
  have Hscale' : a.canonicalMassReverseAtDiameter ell Q v diam*
      ((actualIntermediateMassEffectiveScale W v)^2/a.xs^4) ≤
        (max (1:ℝ) C)^2*(a.canonicalMassReverseAtDiameter ell Q v diam*(W^2/a.xs^4)) := by
    have HH := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right Hscale (pow_nonneg a.hxs.le 4)) hR
    convert HH using 1
    ring
  have Hnorm := mul_le_mul_of_nonneg_left (hnOrder a hxs1 hsmall v hv hv1 hvlo)
    (sq_nonneg (max (1:ℝ) C))
  have Hcoef : (max (1:ℝ) C)^2*a.data.N^(-(64*eta)) ≤ a.data.N^(-(32*eta)) := by
    simpa only [ActualHighOnlyComparisonData.N,one_mul] using hnAbsorb
  exact Hscale'.trans (Hnorm.trans Hcoef)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
