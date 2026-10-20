module

public import ComparisonNativeActualHighMassBroadNormalization
public import ComparisonNativeActualHighMassBroadScale
public import ComparisonNativeActualHighMassNoiseRates

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem chosen_high_mass_broad_budget_polynomial_le
    (ell : ℕ) (_hell : 2 < ell) (Q : ℝ) (_hQ : 1 ≤ Q)
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hCt : 0 ≤ Ct) (hC0 : 0 < C0) {Cs c Cdiam : ℝ}
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hCdiam : 0 < Cdiam)
    (Hreverse : ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.xs ≤ 1 → a.xs^2 ≤ Cs*laplaceComparisonStrength a.context.d a.lam a.xs →
        ∀v : ℝ, 0 < v → v ≤ 1 → c*a.canonicalDirectTestBandScale ≤ v →
          a.canonicalMassReverseAtDiameter ell Q v (a.canonicalChosenHighMassDiameter Cdiam v)*
            (a.canonicalDirectTestBandScale^2/a.xs^4) ≤
              a.context.N^(-(32*actualMassSavingExponent m delta))) :
    ∀ᶠn : ℕ in atTop,
      ∀a : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        1 ≤ Real.log a.context.N → 1/a.context.N ≤ a.context.d →
        a.xs^2 ≤ Cs*laplaceComparisonStrength a.context.d a.lam a.xs →
        a.canonicalDirectTestBandScale ≤ 1 →
        ∀v width : ℝ, 0 < v → v ≤ 1 → c*a.canonicalDirectTestBandScale ≤ v →
          v ≤ width → width ≤ 4*v → width ≤ 1 →
          a.canonicalBroadMassBudgetAtDiameter ell Q (10*Real.log a.context.N)
            (a.context.N^(-(10:ℝ))) v width (a.canonicalChosenHighMassDiameter Cdiam v)/
              (a.xs^4*v/a.canonicalDirectTestBandScale^2) ≤
                a.context.N^(-actualMassSavingExponent m delta) := by
  let eta := actualMassSavingExponent m delta
  let Ctrace := actualHighMassTraceConstant Cs Az cl c C0 Ct D
  let Cfinite := nativeHighMassBroadFiniteConstant 10
  let Cerr := 16*C0^4/c
  let Ctotal := Cfinite*(Ctrace+2)+Cerr
  have heta : 0 < eta := actualMassSavingExponent_pos hm hdelta
  have HCfinite : 0 ≤ Cfinite := native_high_mass_broad_finite_constant_nonneg (by norm_num)
  have HCerr : 0 ≤ Cerr := by dsimp [Cerr]; positivity
  have HlogD : 0 ≤ Real.log (1+D^2) := Real.log_nonneg (by nlinarith [sq_nonneg D])
  have HCtrace : 0 ≤ Ctrace := by
    dsimp [Ctrace,actualHighMassTraceConstant,actualHighMassPowerConstant,actualHighMassEndpointConstant]
    positivity
  have Hsquare := eventually_chosen_high_mass_diameter_square_polynomial_le
    (cl:=cl) (cu:=cu) (Az:=Az) (D:=D) (Bclock:=Bclock)
    hm hdelta hCt hC0 hc hCdiam.le
  have Hdecay := (tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=32*eta) (s:=eta) (by linarith) 5 Ctotal)
  filter_upwards [Hreverse,Hsquare,Hdecay] with n hnreverse hnsquare hnrate
  intro a hlog hnd hsmall hW1 v width hv hv1 hvlo hwlo hwhi hw1
  let W := a.canonicalDirectTestBandScale
  let diam := a.canonicalChosenHighMassDiameter Cdiam v
  let loss := (32:ℝ)^2+25*(1+v/a.context.U)*Real.log ((1+a.context.U)/a.context.U)+1
  let tau := W^2/(a.canonicalMassPower v*v^2*a.xs^4)
  let L := Real.log a.context.N
  have hN : 1 ≤ a.context.N := by dsimp [NativeOverlapContext.N]; exact_mod_cast Nat.succ_pos n
  have hN0 := a.context.hN
  have hW : 0 < W := a.canonical_direct_test_band_pos
  have hxs := a.hxs
  have hxs1 : a.xs ≤ 1 := a.canonical_direct_test_band_ge_scale.trans hW1
  have hcut : 0 < a.context.N^(-(10:ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hwidth : 0 < width := hv.trans_le hwlo
  have hdiam : 0 < diam := a.canonical_chosen_high_mass_diameter_pos hCdiam (by linarith) hv
  have hwidthlog : Real.log (width/a.context.N^(-(10:ℝ))) ≤ 10*Real.log a.context.N := by
    have HH := Real.log_le_log (div_pos hwidth hcut) (div_le_div_of_nonneg_right hw1 hcut.le)
    apply HH.trans_eq
    rw [one_div,Real.log_inv,Real.log_rpow hN0]
    ring
  have Hnorm := a.canonical_high_mass_broad_budget_normalized_le ell Q 10 (by norm_num)
    hlog hv hwidth.le hwhi hdiam.le hwidthlog
  have Hnoise := a.canonical_high_mass_noise_bounds (Q:=Q)
    hm hcl hAz hCt hC0 hCs hc hN hlog hsmall hW1 hv hvlo
  have HEtrace : loss*tau/L=
      ((1025+25*(1+v/a.context.U)*Real.log ((1+a.context.U)/a.context.U))*
        ((a.canonicalDirectTestBandScale^2/a.xs^4)/(a.canonicalMassPower v*v^2)))/
          Real.log a.context.N := by
    dsimp [loss,tau,L,W]
    ring
  have Htrace : loss*tau/L ≤ Ctrace*a.context.N^(-3*m) := by
    rw [HEtrace]
    exact Hnoise.2.2
  have Hbounds := actualMassSavingExponent_bounds m delta
  have HnoisePower : a.context.N^(-3*m) ≤ a.context.N^(-(32*eta)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by dsimp [eta]; nlinarith [Hbounds.2.1])
  have HtraceSaved : loss*tau/L ≤ Ctrace*a.context.N^(-(32*eta)) :=
    Htrace.trans (mul_le_mul_of_nonneg_left HnoisePower HCtrace)
  have HDsaved : diam^2*W^2/a.xs^4 ≤ a.context.N^(-(32*eta)) := by
    simpa only [mul_div_assoc] using hnsquare a hlog hnd hxs1 v hv hvlo
  have HRsaved : a.canonicalMassReverseAtDiameter ell Q v diam*W^2/a.xs^4 ≤
      a.context.N^(-(32*eta)) := by
    simpa only [mul_div_assoc] using hnreverse a hxs1 hsmall v hv hv1 hvlo
  have Hmain := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add HtraceSaved HDsaved) HRsaved)
    (show 0 ≤ Cfinite*L^5 by exact mul_nonneg HCfinite (pow_nonneg (by linarith) _))
  have Hcut := a.canonical_high_mass_broad_cut_normalized_le hC0 hm hN hW1 hc hv hvlo hcut.le
  have Hpowcut : a.context.N^4*a.context.N^(-(10:ℝ))=a.context.N^(-(6:ℝ)) := by
    rw [←Real.rpow_natCast a.context.N 4,←Real.rpow_add hN0]
    norm_num
  have HcutPower : a.context.N^(-(6:ℝ)) ≤ a.context.N^(-(32*eta)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by dsimp [eta]; nlinarith [Hbounds.1])
  have HcutLog : 1 ≤ L^5 := one_le_pow₀ hlog
  have HCnormal : 16*a.context.N^(-(10:ℝ))*W^2/(a.xs^4*v) ≤ Cerr*L^5*a.context.N^(-(32*eta)) := by
    apply Hcut.trans
    rw [mul_assoc,Hpowcut]
    have HH := mul_le_mul_of_nonneg_left HcutPower HCerr
    have HL := mul_le_mul_of_nonneg_left HcutLog
      (show 0 ≤ Cerr*a.context.N^(-(32*eta)) by positivity)
    nlinarith only [HH,HL]
  have Htotal : a.canonicalBroadMassBudgetAtDiameter ell Q (10*Real.log a.context.N)
      (a.context.N^(-(10:ℝ))) v width diam/(a.xs^4*v/W^2) ≤
        Ctotal*L^5*a.context.N^(-(32*eta)) := by
    apply Hnorm.trans
    have HH := add_le_add Hmain HCnormal
    convert HH using 1
    dsimp [Ctotal]
    ring
  exact Htotal.trans (by simpa only [NativeOverlapContext.N] using hnrate)

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
