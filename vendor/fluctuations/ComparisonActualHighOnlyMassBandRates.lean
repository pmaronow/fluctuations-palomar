module

public import ComparisonNativeActualMassBandRates
public import ComparisonActualHighOnlyMassBandNormalization

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
theorem canonical_ordinary_mass_band_budget_polynomial_le
    (ell : ℕ) (hell : 2<ell) (Q c Cv : ℝ) (hc : 0<c) (hCv : 0 ≤ Cv)
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0<cl)
    (hAz : 0 ≤ Az) (hCt : 0 ≤ Ct) (hC0 : 0<C0) :
    ∀ᶠ n : ℕ in atTop,
      ∀a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        ∀W : ℝ,a.xs ≤ W → W ≤ 1 → ∀v : ℝ,0<v → v ≤ 1 → c*W ≤ v → v ≤ Cv*W →
          a.canonicalOrdinaryMassBudget ell Q (10*Real.log a.data.N)
            (a.data.N^(-(10:ℝ))) v/W^3 ≤ a.data.N^(-actualMassSavingExponent m delta) := by
  let η:=actualMassSavingExponent m delta
  let Cn:=actualMassStrengthConstant Az cl Ct Cv/(256*c^2)
  let Cd:=9*C0^3*(1+Real.log (1+D^2))
  let Cenv:=nativeMassOrdinaryRateConstant ell Q Cv Cn C0 Cd
  let Cerr:=18*(3+1024*Q^4*D^2)*C0^3
  let Ctotal:=nativeMassBinLossConstant 10*(16*Cv)*Cenv+Cerr
  have hη : 0<η:=actualMassSavingExponent_pos hm hdelta
  have hCn : 0 ≤ Cn:=by
    dsimp [Cn,actualMassStrengthConstant,actualMassEndpointConstant]
    positivity
  have HlogD : 0 ≤ Real.log (1+D^2):=Real.log_nonneg (by nlinarith [sq_nonneg D])
  have hCd : 0 ≤ Cd:=by dsimp [Cd];positivity
  have HCenv : 0 ≤ Cenv := by
    have Heven : 0 ≤ (2*Q)^(2*ell):=by rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
    dsimp [Cenv,nativeMassOrdinaryRateConstant,nativeMassReverseConstant]
    positivity
  have Hdecay:=(tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=32*η) (s:=η) (by linarith) 8 Ctotal)
  have Hlog:=(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1:ℝ))
  filter_upwards [Hdecay,(tendsto_add_atTop_nat 1).eventually Hlog] with n hn hlog
  intro a W hxsW hxs1 v hv hv1 hvlo hvhi
  have hW : 0<W:=a.hxs.trans_le hxsW
  have hN : 1 ≤ a.data.N:=by dsimp [ActualHighOnlyComparisonData.N];exact_mod_cast Nat.succ_pos n
  have hlog' : 1 ≤ Real.log a.data.N:=hlog
  have Hbudget:=a.canonical_ordinary_mass_band_budget_normalized_le (cut:=a.data.N^(-(10:ℝ))) W hxsW ell hell Q 10 c Cv
    (by norm_num) hc hCv hm hcl hAz hCt hC0 hxs1 hN hlog' hv hv1 hvlo hvhi
    (Real.rpow_nonneg a.data.hN.le (-(10:ℝ)))
  have Ht : a.data.U/W ≤ C0^3*a.data.N^(-3*m):=
    (div_le_div_of_nonneg_left a.data.hU.le a.hxs hxsW).trans (a.canonical_mass_small_ratio hC0)
  have HL2 : 1 ≤ (Real.log a.data.N)^2:=one_le_pow₀ hlog'
  have Htr : a.data.U/W ≤ C0^3*(Real.log a.data.N)^2*a.data.N^(-3*m) := by
    apply Ht.trans
    have H:=mul_le_mul_of_nonneg_left HL2 (show 0 ≤ C0^3*a.data.N^(-3*m) by positivity)
    nlinarith
  have Hd := (div_le_div_of_nonneg_left
    (a.canonical_mass_diameter_nonneg (by linarith : 0 ≤ Real.log a.data.N)) a.hxs hxsW).trans
      (a.canonical_mass_diameter_rate hC0 hN hlog')
  have Henv:=native_mass_ordinary_envelope_rate_le (Q:=Q) ell hell hN hlog'
    (div_nonneg a.data.hU.le hW.le)
    (div_nonneg (a.canonical_mass_diameter_nonneg (by linarith)) hW.le)
    hCv hCn hC0.le hCd hm hdelta Htr Hd
  have Hmain:=mul_le_mul_of_nonneg_left Henv
    (show 0 ≤ nativeMassBinLossConstant 10*(Real.log a.data.N)^4*(16*Cv) by
      exact mul_nonneg (mul_nonneg (native_mass_binScaleLoss_constant_nonneg (by norm_num))
        (pow_nonneg (by linarith) _)) (mul_nonneg (by norm_num) hCv))
  have Hpowcut : a.data.N^4*a.data.N^(-(10:ℝ))=a.data.N^(-(6:ℝ)) := by
    rw [←Real.rpow_natCast a.data.N 4,←Real.rpow_add a.data.hN]
    norm_num
  have Hsave:=actualMassSavingExponent_bounds m delta
  have Hcutpow : a.data.N^(-(6:ℝ)) ≤ a.data.N^(-(32*η)):=
    Real.rpow_le_rpow_of_exponent_le hN (by dsimp [η];nlinarith [Hsave.1])
  have Hlog8 : 1 ≤ (Real.log a.data.N)^8:=one_le_pow₀ hlog'
  have Hcut : Cerr*a.data.N^4*a.data.N^(-(10:ℝ)) ≤
      Cerr*(Real.log a.data.N)^8*a.data.N^(-(32*η)) := by
    rw [mul_assoc,Hpowcut]
    have H1:=mul_le_mul_of_nonneg_left Hcutpow (show 0 ≤ Cerr by dsimp [Cerr];positivity)
    have H2:=mul_le_mul_of_nonneg_left Hlog8 (show 0 ≤ Cerr*a.data.N^(-(32*η)) by
      dsimp [Cerr];positivity)
    nlinarith
  have Htotal : a.canonicalOrdinaryMassBudget ell Q (10*Real.log a.data.N)
      (a.data.N^(-(10:ℝ))) v/W^3 ≤ Ctotal*(Real.log a.data.N)^8*a.data.N^(-(32*η)) := by
    apply Hbudget.trans
    dsimp only [Ctotal,Cenv,Cn,Cd,Cerr] at Hmain Hcut ⊢
    nlinarith [Hmain,Hcut]
  exact Htotal.trans hn

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
