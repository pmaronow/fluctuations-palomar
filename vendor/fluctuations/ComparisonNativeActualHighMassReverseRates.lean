module

public import ComparisonNativeActualHighMassReverse

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

namespace NativeOverlapMinimum

theorem exists_actual_high_mass_reverse_polynomial_order
    {m delta cl cu Az C0 Ct D Bclock Cs c Cdiam : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hC0 : 0 < C0) (hD : 0 < D)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hCdiam : 0 < Cdiam) :
    ∃ell : ℕ,2 < ell ∧ ∀Q : ℝ,1 ≤ Q →
      ∀ᶠ n : ℕ in atTop,
        ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
          a.xs ≤ 1 →
          a.xs^2 ≤ Cs*laplaceComparisonStrength a.context.d a.lam a.xs →
          ∀v : ℝ,0 < v → v ≤ 1 → c*a.canonicalDirectTestBandScale ≤ v →
            a.canonicalMassReverseAtDiameter ell Q v (a.canonicalChosenHighMassDiameter Cdiam v)*
                (a.canonicalDirectTestBandScale^2/a.xs^4) ≤
              a.context.N^(-(32*actualMassSavingExponent m delta)) := by
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
  let W:=a.canonicalDirectTestBandScale
  let diam:=a.canonicalChosenHighMassDiameter Cdiam v
  let y:=a.canonicalMassHeight v
  have hN:=a.context.hN
  have hxs:=a.hxs
  have hW : 0 < W:=a.canonical_direct_test_band_pos
  have hN2 : (2:ℝ) ≤ a.context.N:=by
    dsimp [NativeOverlapContext.N]
    exact_mod_cast (by omega : 2 ≤ n+1)
  have hlog : 1 ≤ Real.log a.context.N:=hnlog
  have hdiam : 0 < diam:=a.canonical_chosen_high_mass_diameter_pos hCdiam (by linarith) hv
  have hy : 0 < y:=by
    dsimp [y,canonicalMassHeight]
    have hu : 0 ≤ min (16*v) 1:=le_min (by positivity) zero_le_one
    positivity
  have hyN : y ≤ a.context.N:=by
    have Hy : y ≤ 2:=by dsimp [y,canonicalMassHeight];linarith [min_le_right (16*v) 1]
    exact Hy.trans hN2
  have hraw : Q ≤ a.context.N^eps0:=by simpa only [Real.rpow_zero,mul_one] using hnraw
  have hdiamN : a.context.N^(-k) ≤ diam:=hndiam a hlog v hv hv1
  have Hreverse:=mass_reverse_power_extraction (p:=(ell:ℝ)) (a:=1) (k:=k) (eps0:=eps0)
    hN hdiam (zero_lt_one.trans_le hQ) hy
    (by exact_mod_cast hEll) hraw (by simpa only [Real.rpow_one] using hyN) hdiamN
  have Hactual : a.canonicalMassReverseAtDiameter ell Q v diam ≤ Cpow*a.context.N^e*y*diam:=by
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
    (show 0 ≤ Cpow*a.context.N^e*diam*(W^2/a.xs^4) by dsimp [Cpow];positivity)
  have Hcap:=a.canonical_direct_test_cap_strong_rate hC0 hCs hsmall
  have HcapMul:=mul_le_mul_of_nonneg_left Hcap
    (show 0 ≤ Cpow*a.context.N^e*Cy*Cdiam*Real.log a.context.N*a.context.N^(-delta) by dsimp [Cpow];positivity)
  have HE : Cpow*a.context.N^e*(Cy*v)*diam*(W^2/a.xs^4)=
      (Cpow*a.context.N^e*Cy*Cdiam*Real.log a.context.N*a.context.N^(-delta))*
        ((a.context.E/a.context.d^3)*(W^2/a.xs^4)):=by
    dsimp [diam,canonicalChosenHighMassDiameter]
    rw [Real.rpow_neg hN.le]
    field_simp
  have HE2 : (Cpow*a.context.N^e*Cy*Cdiam*Real.log a.context.N*a.context.N^(-delta))*
      ((Cs+1)^2*C0^3*a.context.N^(-3*m))=
      Ctotal*(Real.log a.context.N)^1*a.context.N^(-(3*m+delta-e)):=by
    dsimp [Ctotal]
    rw [show (Cpow*a.context.N^e*Cy*Cdiam*Real.log a.context.N*a.context.N^(-delta))*
      ((Cs+1)^2*C0^3*a.context.N^(-3*m))=
      (Cpow*Cy*Cdiam*(Cs+1)^2*C0^3)*Real.log a.context.N*
        ((a.context.N^e*a.context.N^(-delta))*a.context.N^(-3*m)) by ring,
      ←Real.rpow_add hN,←Real.rpow_add hN]
    rw [show e + -delta + -3*m=-(3*m+delta-e) by ring,pow_one]
  have Hfinal : a.canonicalMassReverseAtDiameter ell Q v diam*(W^2/a.xs^4) ≤
      Ctotal*(Real.log a.context.N)^1*a.context.N^(-(3*m+delta-e)):=by
    apply Hnorm.trans
    have Hyn : Cpow*a.context.N^e*y*diam*(W^2/a.xs^4) ≤
        Cpow*a.context.N^e*(Cy*v)*diam*(W^2/a.xs^4):=by nlinarith only [HyNorm]
    apply Hyn.trans
    rw [HE]
    exact HcapMul.trans_eq HE2
  exact Hfinal.trans hnrate

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
