module

public import ComparisonNativeActualMassBudgetNormalization
public import ComparisonNativeCavityRadiusPolynomialRate

@[expose] public section

noncomputable section
set_option maxHeartbeats 9000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

def actualMassSavingExponent (m delta : ℝ) : ℝ := min 1 (min m delta)/64

theorem actualMassSavingExponent_pos {m delta : ℝ} (hm : 0 < m) (hd : 0 < delta) :
    0 < actualMassSavingExponent m delta := by unfold actualMassSavingExponent;positivity

theorem actualMassSavingExponent_bounds (m delta : ℝ) :
    64*actualMassSavingExponent m delta ≤ 1 ∧
      64*actualMassSavingExponent m delta ≤ m ∧ 64*actualMassSavingExponent m delta ≤ delta := by
  dsimp [actualMassSavingExponent]
  constructor
  · nlinarith [min_le_left (1:ℝ) (min m delta)]
  constructor
  · nlinarith [(min_le_right (1:ℝ) (min m delta)).trans (min_le_left m delta)]
  · nlinarith [(min_le_right (1:ℝ) (min m delta)).trans (min_le_right m delta)]

theorem native_mass_reverse_exponent_range {ell : ℕ} (hell : 2<ell) :
    (1:ℝ)/2 ≤ ((ell:ℝ)-2)/((ell:ℝ)-1) ∧ ((ell:ℝ)-2)/((ell:ℝ)-1) ≤ 1 := by
  have he : (3:ℝ) ≤ ell:=by exact_mod_cast (by omega : 3 ≤ ell)
  have hden : 0<(ell:ℝ)-1:=by linarith
  constructor
  · exact (le_div_iff₀ hden).mpr (by linarith)
  · exact (div_le_iff₀ hden).mpr (by linarith)

theorem native_mass_fixed_power_rate_le {N L t C a b q : ℝ}
    (hN : 1 ≤ N) (hL : 1 ≤ L) (ht : 0 ≤ t) (hC : 0 ≤ C)
    (ha : 0 ≤ a) (ha2 : a ≤ 2) (hq : q ≤ b*a)
    (hbound : t ≤ C*L^2*N^(-b)) :
    t^a ≤ C^a*L^4*N^(-q) := by
  have hN0 : 0<N:=zero_lt_one.trans_le hN
  have hL0 : 0 ≤ L:=zero_le_one.trans hL
  have H:=Real.rpow_le_rpow ht hbound ha
  apply H.trans
  rw [Real.mul_rpow (mul_nonneg hC (sq_nonneg L)) (Real.rpow_nonneg hN0.le _),
    Real.mul_rpow hC (sq_nonneg L),←Real.rpow_natCast L 2,←Real.rpow_mul hL0,
    ←Real.rpow_mul hN0.le]
  have HL : L^((2:ℝ)*a) ≤ L^(4:ℝ):=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have HN : N^((-b)*a) ≤ N^(-q):=
    Real.rpow_le_rpow_of_exponent_le hN (by nlinarith)
  have Hmul:=mul_le_mul HL HN (Real.rpow_nonneg hN0.le _) (Real.rpow_nonneg hL0 _)
  have HC:=mul_le_mul_of_nonneg_left Hmul (Real.rpow_nonneg hC a)
  simpa only [Real.rpow_ofNat,mul_assoc,Nat.cast_ofNat] using HC

theorem native_mass_log_power_absorbed {q : ℝ} (hq : 0<q) (k : ℕ) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,C*(Real.log (n:ℝ))^k ≤ (n:ℝ)^q := by
  let r:=q/(k+1:ℕ)
  have hr : 0<r:=by dsimp [r];positivity
  have HC:=eventually_coefficient_rpow_le (c:=C) (d:=1) (q:=0) (r:=r) zero_lt_one hr
  have HL:=radius_log_power_absorbed hr 1
  filter_upwards [HC,HL,eventually_ge_atTop (1:ℕ)] with n hnC hnL hn
  have hN : 1 ≤ (n:ℝ):=by exact_mod_cast hn
  have hN0 : 0<(n:ℝ):=zero_lt_one.trans_le hN
  have Hc : C ≤ (n:ℝ)^r:=by simpa only [Real.rpow_zero,mul_one,one_mul] using hnC
  have Hl : Real.log (n:ℝ) ≤ (n:ℝ)^r:=by simpa only [one_mul] using hnL
  have Hpow:=pow_le_pow_left₀ (Real.log_nonneg hN) Hl k
  have Hmul:=mul_le_mul Hc Hpow (pow_nonneg (Real.log_nonneg hN) _) (Real.rpow_nonneg hN0.le _)
  calc
    _ ≤ (n:ℝ)^r*((n:ℝ)^r)^k := Hmul
    _ = ((n:ℝ)^r)^(k+1) := by rw [pow_succ];ring
    _ = (n:ℝ)^(r*(k+1:ℕ)) := (Real.rpow_mul_natCast hN0.le r (k+1)).symm
    _ = _ := by congr 1;dsimp [r];field_simp

theorem native_mass_log_power_decay {q s : ℝ} (hqs : s<q) (k : ℕ) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,C*(Real.log (n:ℝ))^k*(n:ℝ)^(-q) ≤ (n:ℝ)^(-s) := by
  filter_upwards [native_mass_log_power_absorbed (sub_pos.mpr hqs) k C,
    eventually_gt_atTop (0:ℕ)] with n hn hnpos
  have hN : 0<(n:ℝ):=by exact_mod_cast hnpos
  have H:=mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hN.le (-q))
  rw [←Real.rpow_add hN,show (q-s)+(-q)=-s by ring] at H
  exact H

def nativeMassOrdinaryRateConstant (ell : ℕ) (Q Cv Cnoise C0 Cd : ℝ) : ℝ :=
  2*(Q^2*(1+16*Cv)*Cnoise)^((2:ℝ)/3)*(C0^3)^((4:ℝ)/3)+
    3*Cnoise*(C0^3)^2+Cd^2+nativeMassReverseConstant ell Q (1+16*Cv)*
      Cd^(((ell:ℝ)-2)/((ell:ℝ)-1))

theorem native_mass_ordinary_envelope_rate_le
    (ell : ℕ) (hell : 2<ell) {N L t d Q Cv Cnoise C0 Cd m delta : ℝ}
    (hN : 1 ≤ N) (hL : 1 ≤ L) (ht : 0 ≤ t) (hd : 0 ≤ d)
    (hCv : 0 ≤ Cv) (hCn : 0 ≤ Cnoise) (hC0 : 0 ≤ C0) (hCd : 0 ≤ Cd)
    (hm : 0 < m) (hdelta : 0 < delta)
    (htr : t ≤ C0^3*L^2*N^(-3*m))
    (hdr : d ≤ Cd*L^2*N^(-(3*m+delta))) :
    nativeMassOrdinaryEnvelope ell Q Cv Cnoise t d ≤
      nativeMassOrdinaryRateConstant ell Q Cv Cnoise C0 Cd*L^4*
        N^(-(32*actualMassSavingExponent m delta)) := by
  have Hθ:=native_mass_reverse_exponent_range hell
  have Hsave:=actualMassSavingExponent_bounds m delta
  have H1:=native_mass_fixed_power_rate_le hN hL ht (pow_nonneg hC0 3)
    (a:=((4:ℝ)/3)) (b:=3*m) (q:=32*actualMassSavingExponent m delta)
    (by norm_num) (by norm_num) (by nlinarith [Hsave.2.1]) (by simpa only [neg_mul] using htr)
  have H2:=native_mass_fixed_power_rate_le hN hL ht (pow_nonneg hC0 3)
    (a:=(2:ℝ)) (b:=3*m) (q:=32*actualMassSavingExponent m delta)
    (by norm_num) le_rfl (by nlinarith [Hsave.2.1]) (by simpa only [neg_mul] using htr)
  have H3:=native_mass_fixed_power_rate_le hN hL hd hCd
    (a:=(2:ℝ)) (b:=3*m+delta) (q:=32*actualMassSavingExponent m delta)
    (by norm_num) le_rfl (by nlinarith [Hsave.2.1]) hdr
  have Hθ0 : 0 ≤ ((ell:ℝ)-2)/((ell:ℝ)-1):=by linarith [Hθ.1]
  have Hqθ : 32*actualMassSavingExponent m delta ≤ (3*m+delta)*(((ell:ℝ)-2)/((ell:ℝ)-1)) := by
    have H:=mul_nonneg (show 0 ≤ 3*m+delta by linarith) (sub_nonneg.mpr Hθ.1)
    nlinarith [Hsave.2.1]
  have H4:=native_mass_fixed_power_rate_le hN hL hd hCd
    (b:=3*m+delta) (q:=32*actualMassSavingExponent m delta) Hθ0 (by linarith [Hθ.2]) Hqθ hdr
  have HC1 : 0 ≤ 2*(Q^2*(1+16*Cv)*Cnoise)^((2:ℝ)/3):=by positivity
  have HC4 : 0 ≤ nativeMassReverseConstant ell Q (1+16*Cv) := by
    unfold nativeMassReverseConstant
    apply Real.rpow_nonneg
    apply mul_nonneg
    · rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
    · positivity
  have HP1:=mul_le_mul_of_nonneg_left H1 HC1
  have HP2:=mul_le_mul_of_nonneg_left H2 (show 0 ≤ 3*Cnoise by positivity)
  have HP4:=mul_le_mul_of_nonneg_left H4 HC4
  simp only [Real.rpow_two] at H2 H3 HP2
  unfold nativeMassOrdinaryEnvelope nativeMassOrdinaryRateConstant
  nlinarith [HP1,HP2,H3,HP4]

namespace NativeOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_ordinary_mass_budget_polynomial_le
    (ell : ℕ) (hell : 2<ell) (Q c Cv : ℝ) (hc : 0<c) (hCv : 0 ≤ Cv)
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0<cl)
    (hAz : 0 ≤ Az) (hCt : 0 ≤ Ct) (hC0 : 0<C0) :
    ∀ᶠ n : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.xs ≤ 1 → ∀v : ℝ,0<v → v ≤ 1 → c*a.xs ≤ v → v ≤ Cv*a.xs →
          a.canonicalOrdinaryMassBudget ell Q (10*Real.log a.context.N)
            (a.context.N^(-(10:ℝ))) v/a.xs^3 ≤ a.context.N^(-actualMassSavingExponent m delta) := by
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
  intro a hxs1 v hv hv1 hvlo hvhi
  have hN : 1 ≤ a.context.N:=by dsimp [NativeOverlapContext.N];exact_mod_cast Nat.succ_pos n
  have hlog' : 1 ≤ Real.log a.context.N:=hlog
  have Hbudget:=a.canonical_ordinary_mass_budget_normalized_le (cut:=a.context.N^(-(10:ℝ))) ell hell Q 10 c Cv
    (by norm_num) hc hCv hm hcl hAz hCt hC0 hxs1 hN hlog' hv hv1 hvlo hvhi
    (Real.rpow_nonneg a.context.hN.le (-(10:ℝ)))
  have Ht:=a.canonical_mass_small_ratio hC0
  have HL2 : 1 ≤ (Real.log a.context.N)^2:=one_le_pow₀ hlog'
  have Htr : a.context.U/a.xs ≤ C0^3*(Real.log a.context.N)^2*a.context.N^(-3*m) := by
    apply Ht.trans
    have H:=mul_le_mul_of_nonneg_left HL2 (show 0 ≤ C0^3*a.context.N^(-3*m) by positivity)
    nlinarith
  have Hd:=a.canonical_mass_diameter_rate hC0 hN hlog'
  have Henv:=native_mass_ordinary_envelope_rate_le (Q:=Q) ell hell hN hlog'
    (div_nonneg a.context.hU.le a.hxs.le)
    (div_nonneg (a.canonical_mass_diameter_nonneg (by linarith)) a.hxs.le)
    hCv hCn hC0.le hCd hm hdelta Htr Hd
  have Hmain:=mul_le_mul_of_nonneg_left Henv
    (show 0 ≤ nativeMassBinLossConstant 10*(Real.log a.context.N)^4*(16*Cv) by
      exact mul_nonneg (mul_nonneg (native_mass_binScaleLoss_constant_nonneg (by norm_num))
        (pow_nonneg (by linarith) _)) (mul_nonneg (by norm_num) hCv))
  have Hpowcut : a.context.N^4*a.context.N^(-(10:ℝ))=a.context.N^(-(6:ℝ)) := by
    rw [←Real.rpow_natCast a.context.N 4,←Real.rpow_add a.context.hN]
    norm_num
  have Hsave:=actualMassSavingExponent_bounds m delta
  have Hcutpow : a.context.N^(-(6:ℝ)) ≤ a.context.N^(-(32*η)):=
    Real.rpow_le_rpow_of_exponent_le hN (by dsimp [η];nlinarith [Hsave.1])
  have Hlog8 : 1 ≤ (Real.log a.context.N)^8:=one_le_pow₀ hlog'
  have Hcut : Cerr*a.context.N^4*a.context.N^(-(10:ℝ)) ≤
      Cerr*(Real.log a.context.N)^8*a.context.N^(-(32*η)) := by
    rw [mul_assoc,Hpowcut]
    have H1:=mul_le_mul_of_nonneg_left Hcutpow (show 0 ≤ Cerr by dsimp [Cerr];positivity)
    have H2:=mul_le_mul_of_nonneg_left Hlog8 (show 0 ≤ Cerr*a.context.N^(-(32*η)) by
      dsimp [Cerr];positivity)
    nlinarith
  have Htotal : a.canonicalOrdinaryMassBudget ell Q (10*Real.log a.context.N)
      (a.context.N^(-(10:ℝ))) v/a.xs^3 ≤ Ctotal*(Real.log a.context.N)^8*a.context.N^(-(32*η)) := by
    apply Hbudget.trans
    dsimp only [Ctotal,Cenv,Cn,Cd,Cerr] at Hmain Hcut ⊢
    nlinarith [Hmain,Hcut]
  exact Htotal.trans hn

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
