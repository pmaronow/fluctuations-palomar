module

public import ComparisonNativeActualBroadMassBandNormalization
public import ComparisonNativeActualMassBandRates

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

def nativeMassBroadRateConstant (ell : ℕ) (C0 Cd : ℝ) : ℝ :=
  C0^3+Cd^2+Cd^(((ell:ℝ)-2)/((ell:ℝ)-1))

theorem native_mass_broad_envelope_rate_le
    (ell : ℕ) (hell : 2<ell) {N L t d C0 Cd m delta : ℝ}
    (hN : 1 ≤ N) (hL : 1 ≤ L) (ht : 0 ≤ t) (hd : 0 ≤ d)
    (hC0 : 0 ≤ C0) (hCd : 0 ≤ Cd) (hm : 0 < m) (hdelta : 0 < delta)
    (htr : t ≤ C0^3*L^2*N^(-3*m))
    (hdr : d ≤ Cd*L^2*N^(-(3*m+delta))) :
    t+d^2+d^(((ell:ℝ)-2)/((ell:ℝ)-1)) ≤
      nativeMassBroadRateConstant ell C0 Cd*L^4*N^(-(32*actualMassSavingExponent m delta)) := by
  have Hθ:=native_mass_reverse_exponent_range hell
  have Hsave:=actualMassSavingExponent_bounds m delta
  have H1:=native_mass_fixed_power_rate_le hN hL ht (pow_nonneg hC0 3)
    (a:=(1:ℝ)) (b:=3*m) (q:=32*actualMassSavingExponent m delta)
    (by norm_num) (by norm_num) (by nlinarith [Hsave.2.1]) (by simpa only [neg_mul] using htr)
  have H2:=native_mass_fixed_power_rate_le hN hL hd hCd
    (a:=(2:ℝ)) (b:=3*m+delta) (q:=32*actualMassSavingExponent m delta)
    (by norm_num) le_rfl (by nlinarith [Hsave.2.1]) hdr
  have Hθ0 : 0 ≤ ((ell:ℝ)-2)/((ell:ℝ)-1):=by linarith [Hθ.1]
  have Hqθ : 32*actualMassSavingExponent m delta ≤ (3*m+delta)*(((ell:ℝ)-2)/((ell:ℝ)-1)) := by
    have H:=mul_nonneg (show 0 ≤ 3*m+delta by linarith) (sub_nonneg.mpr Hθ.1)
    nlinarith [Hsave.2.1]
  have H3:=native_mass_fixed_power_rate_le hN hL hd hCd
    (b:=3*m+delta) (q:=32*actualMassSavingExponent m delta) Hθ0 (by linarith [Hθ.2]) Hqθ hdr
  simp only [Real.rpow_one,Real.rpow_two] at H1 H2
  unfold nativeMassBroadRateConstant
  nlinarith [H1,H2,H3]

namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_broad_mass_band_budget_polynomial_le
    (ell : ℕ) (hell : 2<ell) (Q c Cv : ℝ) (hc : 0<c) (hCv : 0 ≤ Cv)
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0<cl)
    (hAz : 0 ≤ Az) (hCt : 0 ≤ Ct) (hC0 : 0<C0) :
    ∀ᶠ n : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        ∀W : ℝ,a.xs ≤ W → W ≤ 1 → ∀v width : ℝ,
          0<v → c*W ≤ v → v ≤ Cv*W → v ≤ width → width ≤ 4*v → width ≤ 1 →
          a.canonicalBroadMassBudget ell Q (10*Real.log a.context.N)
            (a.context.N^(-(10:ℝ))) v width/W^3 ≤ a.context.N^(-actualMassSavingExponent m delta) := by
  let η:=actualMassSavingExponent m delta
  let Cn:=actualMassStrengthConstant Az cl Ct Cv/(256*c^2)
  let Cd:=9*C0^3*(1+Real.log (1+D^2))
  let Cenv:=nativeMassBroadRateConstant ell C0 Cd
  let Cb:=nativeMassBroadEnvelopeConstant ell Q 10 Cv Cn (nativeMassBroadTraceConstant Cv D)
  let Cerr:=16*C0^3
  let Ctotal:=Cb*Cenv+Cerr
  have hη : 0<η:=actualMassSavingExponent_pos hm hdelta
  have hCn : 0 ≤ Cn:=by dsimp [Cn,actualMassStrengthConstant,actualMassEndpointConstant];positivity
  have HlogD : 0 ≤ Real.log (1+D^2):=Real.log_nonneg (by nlinarith [sq_nonneg D])
  have hCd : 0 ≤ Cd:=by dsimp [Cd];positivity
  have HCr : 0 ≤ nativeMassReverseConstant ell Q (1+16*Cv) := by
    unfold nativeMassReverseConstant
    have Heven : 0 ≤ (2*Q)^(2*ell):=by rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
    exact Real.rpow_nonneg (mul_nonneg Heven (pow_nonneg (by positivity) _)) _
  have hCb : 0 ≤ Cb:=by
    dsimp [Cb,nativeMassBroadEnvelopeConstant,nativeMassBroadTraceConstant]
    positivity
  have hCenv : 0 ≤ Cenv:=by dsimp [Cenv,nativeMassBroadRateConstant];positivity
  have Hdecay:=(tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=32*η) (s:=η) (by linarith) 9 Ctotal)
  have Hratio:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^3) (d:=1) (q:=-3*m) (r:=0) zero_lt_one (by linarith))
  have Hlog:=(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1:ℝ))
  filter_upwards [Hdecay,Hratio,(tendsto_add_atTop_nat 1).eventually Hlog] with n hn hratio hlog
  intro a W hxsW hW1 v width hv hvlo hvhi hvwidth hwidthhi hwidth1
  have hW : 0<W:=a.hxs.trans_le hxsW
  have hwidth : 0<width:=hv.trans_le hvwidth
  have hN : 1 ≤ a.context.N:=by dsimp [NativeOverlapContext.N];exact_mod_cast Nat.succ_pos n
  have hlog' : 1 ≤ Real.log a.context.N:=hlog
  have Ht : a.context.U/W ≤ C0^3*a.context.N^(-3*m):=
    (div_le_div_of_nonneg_left a.context.hU.le a.hxs hxsW).trans (a.canonical_mass_small_ratio hC0)
  have Htsmall : a.context.U/W ≤ 1:=Ht.trans (by simpa only [Real.rpow_zero,mul_one,one_mul] using hratio)
  have hcut : 0<a.context.N^(-(10:ℝ)):=Real.rpow_pos_of_pos a.context.hN _
  have hwidthlog : Real.log (width/a.context.N^(-(10:ℝ))) ≤ 10*Real.log a.context.N := by
    have H:=Real.log_le_log (div_pos hwidth hcut)
      (div_le_div_of_nonneg_right hwidth1 hcut.le)
    apply H.trans_eq
    rw [Real.log_div one_ne_zero hcut.ne',Real.log_one,Real.log_rpow a.context.hN]
    ring
  have Hbudget:=a.canonical_broad_mass_band_budget_normalized_le ell hell Q 10 c Cv
    (by norm_num) hc hCv hm hcl hAz hCt hC0 hxsW hW1 hN hlog' Htsmall
    hv hvlo hvhi hwidth.le hwidthhi hcut.le hwidthlog
  have HL2 : 1 ≤ (Real.log a.context.N)^2:=one_le_pow₀ hlog'
  have Htr : a.context.U/W ≤ C0^3*(Real.log a.context.N)^2*a.context.N^(-3*m) := by
    apply Ht.trans
    have H:=mul_le_mul_of_nonneg_left HL2 (show 0 ≤ C0^3*a.context.N^(-3*m) by positivity)
    nlinarith
  have Hd := (div_le_div_of_nonneg_left
    (a.canonical_mass_diameter_nonneg (by linarith : 0 ≤ Real.log a.context.N)) a.hxs hxsW).trans
      (a.canonical_mass_diameter_rate hC0 hN hlog')
  have Henv:=native_mass_broad_envelope_rate_le ell hell hN hlog'
    (div_nonneg a.context.hU.le hW.le)
    (div_nonneg (a.canonical_mass_diameter_nonneg (by linarith)) hW.le)
    hC0.le hCd hm hdelta Htr Hd
  have Hmain:=mul_le_mul_of_nonneg_left Henv
    (mul_nonneg hCb (pow_nonneg (show 0 ≤ Real.log a.context.N by linarith) 5))
  have Hpowcut : a.context.N^3*a.context.N^(-(10:ℝ))=a.context.N^(-(7:ℝ)) := by
    rw [←Real.rpow_natCast a.context.N 3,←Real.rpow_add a.context.hN]
    norm_num
  have Hsave:=actualMassSavingExponent_bounds m delta
  have Hcutpow : a.context.N^(-(7:ℝ)) ≤ a.context.N^(-(32*η)):=
    Real.rpow_le_rpow_of_exponent_le hN (by dsimp [η];nlinarith [Hsave.1])
  have Hlog9 : 1 ≤ (Real.log a.context.N)^9:=one_le_pow₀ hlog'
  have Hcut : Cerr*a.context.N^3*a.context.N^(-(10:ℝ)) ≤
      Cerr*(Real.log a.context.N)^9*a.context.N^(-(32*η)) := by
    rw [mul_assoc,Hpowcut]
    have H1:=mul_le_mul_of_nonneg_left Hcutpow (show 0 ≤ Cerr by dsimp [Cerr];positivity)
    have H2:=mul_le_mul_of_nonneg_left Hlog9 (show 0 ≤ Cerr*a.context.N^(-(32*η)) by dsimp [Cerr];positivity)
    nlinarith
  have Htotal : a.canonicalBroadMassBudget ell Q (10*Real.log a.context.N)
      (a.context.N^(-(10:ℝ))) v width/W^3 ≤ Ctotal*(Real.log a.context.N)^9*a.context.N^(-(32*η)) := by
    apply Hbudget.trans
    dsimp only [Ctotal,Cenv,Cn,Cd,Cerr,Cb] at Hmain Hcut ⊢
    nlinarith [Hmain,Hcut]
  exact Htotal.trans hn

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
