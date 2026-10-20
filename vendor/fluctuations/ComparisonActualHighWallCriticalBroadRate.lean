module

public import ComparisonNativeActualHighMassBroadNormalization
public import ComparisonNativeActualMassBudgetRates

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option linter.unusedVariables false
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

def criticalBroadFiniteRateConstant (Ctrace Cd Cr Ccut : ℝ) : ℝ :=
  nativeHighMassBroadFiniteConstant 10*(Ctrace+Cd^2+Cr)+16*Ccut

theorem critical_broad_finite_saved_envelope_le
    {m delta N x P v width diameter R loss Ctrace Cd Cr Ccut : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hN : 1 ≤ N)
    (hlog : 1 ≤ Real.log N) (hx : 0 < x) (hP : 0 < P) (hv : 0 < v)
    (hwidthlo : v ≤ width) (hwidthhi : width ≤ 4*v) (hwidthone : width ≤ 1)
    (hdiameter : 0 ≤ diameter) (hR : 0 ≤ R) (hloss : 0 ≤ loss)
    (hCtrace : 0 ≤ Ctrace) (hCd : 0 ≤ Cd) (hCr : 0 ≤ Cr) (hCcut : 0 ≤ Ccut)
    (Htrace : loss/(P*v^2*x^2)/Real.log N ≤ Ctrace*N^(-3*m))
    (Hdiameter : diameter/x ≤ Cd*(Real.log N)^2*N^(-3*m))
    (Hreverse : R/x^2 ≤ Cr*(Real.log N)^4*N^(-(32*actualMassSavingExponent m delta)))
    (Hcut : N^(-(10:ℝ))/(x^2*v) ≤ Ccut*N^(-(6:ℝ))) :
    nativeConditionalLedgerBudget 1 width (N^(-(10:ℝ))) diameter
      (108*loss*(Real.log N)^2/(P*(v/4))*Real.log (width/N^(-(10:ℝ))))
      (54*loss*(Real.log N)^2*width/(P*(v/4)^2)) R (10*Real.log N)/(x^2*v) ≤
      criticalBroadFiniteRateConstant Ctrace Cd Cr Ccut*(Real.log N)^9*
        N^(-(32*actualMassSavingExponent m delta)) := by
  let eta := actualMassSavingExponent m delta
  let L := Real.log N
  let Cfinite := nativeHighMassBroadFiniteConstant 10
  have hN0 : 0 < N := zero_lt_one.trans_le hN
  have hL0 : 0 ≤ L := zero_le_one.trans hlog
  have hcut : 0 < N^(-(10:ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hwidth : 0 < width := hv.trans_le hwidthlo
  have hwidthlog : Real.log (width/N^(-(10:ℝ))) ≤ 10*Real.log N := by
    have HH := Real.log_le_log (div_pos hwidth hcut)
      (div_le_div_of_nonneg_right hwidthone hcut.le)
    apply HH.trans_eq
    rw [one_div,Real.log_inv,Real.log_rpow hN0]
    ring
  have Hnorm := mass_high_broad_finite_normalized_le hx hx hP hv hwidth.le hwidthhi
    hdiameter hR hloss hlog (by norm_num : (0:ℝ) ≤ 10) hwidthlog
  have Hden : x^4*v/x^2 = x^2*v := by field_simp
  have Htraceeq : loss*(x^2/(P*v^2*x^4))/L = loss/(P*v^2*x^2)/L := by
    field_simp
  have Hdiameq : diameter^2*x^2/x^4 = (diameter/x)^2 := by field_simp
  have Hreveq : R*x^2/x^4 = R/x^2 := by field_simp
  have Hcuteq : 16*N^(-(10:ℝ))*x^2/(x^4*v) = 16*(N^(-(10:ℝ))/(x^2*v)) := by
    field_simp
  rw [Hden,Htraceeq,Hdiameq,Hreveq,Hcuteq] at Hnorm
  have Heta := actualMassSavingExponent_bounds m delta
  have Hpower : N^(-3*m) ≤ N^(-(32*eta)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by dsimp [eta]; nlinarith [Heta.2.1])
  have HL4 : 1 ≤ L^4 := one_le_pow₀ hlog
  have HtraceSaved : loss/(P*v^2*x^2)/L ≤ Ctrace*L^4*N^(-(32*eta)) := by
    have HH := Htrace.trans (mul_le_mul_of_nonneg_left Hpower hCtrace)
    have HL := mul_le_mul_of_nonneg_right HL4
      (show 0 ≤ Ctrace*N^(-(32*eta)) by positivity)
    nlinarith only [HH,HL]
  have HDsaved := native_mass_fixed_power_rate_le hN hlog
    (div_nonneg hdiameter hx.le) hCd (a:=(2:ℝ)) (b:=3*m) (q:=32*eta)
    (by norm_num) le_rfl (by dsimp [eta]; nlinarith [Heta.2.1])
    (by simpa only [neg_mul] using Hdiameter)
  simp only [Real.rpow_two] at HDsaved
  have HCfinite : 0 ≤ Cfinite := native_high_mass_broad_finite_constant_nonneg (by norm_num)
  have Hmain := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add HtraceSaved HDsaved) Hreverse)
    (show 0 ≤ Cfinite*L^5 by positivity)
  have HcutPower : N^(-(6:ℝ)) ≤ N^(-(32*eta)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by dsimp [eta]; nlinarith [Heta.1])
  have HL9 : 1 ≤ L^9 := one_le_pow₀ hlog
  have HcutSaved : 16*(N^(-(10:ℝ))/(x^2*v)) ≤ 16*Ccut*L^9*N^(-(32*eta)) := by
    have HH := mul_le_mul_of_nonneg_left
      (Hcut.trans (mul_le_mul_of_nonneg_left HcutPower hCcut)) (by norm_num : (0:ℝ) ≤ 16)
    have HL := mul_le_mul_of_nonneg_right HL9
      (show 0 ≤ 16*Ccut*N^(-(32*eta)) by positivity)
    nlinarith only [HH,HL]
  apply Hnorm.trans
  have HH := add_le_add Hmain HcutSaved
  convert HH using 1
  dsimp [criticalBroadFiniteRateConstant,Cfinite,L,eta]
  ring

theorem eventually_critical_broad_finite_saved_rate_le
    {m delta Ctrace Cd Cr Ccut : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta)
    (hCtrace : 0 ≤ Ctrace) (hCd : 0 ≤ Cd) (hCr : 0 ≤ Cr) (hCcut : 0 ≤ Ccut) :
    ∀ᶠ n : ℕ in atTop,
      let N : ℝ := (n+1:ℕ)
      ∀ x P v width diameter R loss : ℝ,
        0 < x → 0 < P → 0 < v → v ≤ width → width ≤ 4*v → width ≤ 1 →
        0 ≤ diameter → 0 ≤ R → 0 ≤ loss →
        loss/(P*v^2*x^2)/Real.log N ≤ Ctrace*N^(-3*m) →
        diameter/x ≤ Cd*(Real.log N)^2*N^(-3*m) →
        R/x^2 ≤ Cr*(Real.log N)^4*N^(-(32*actualMassSavingExponent m delta)) →
        N^(-(10:ℝ))/(x^2*v) ≤ Ccut*N^(-(6:ℝ)) →
        nativeConditionalLedgerBudget 1 width (N^(-(10:ℝ))) diameter
          (108*loss*(Real.log N)^2/(P*(v/4))*Real.log (width/N^(-(10:ℝ))))
          (54*loss*(Real.log N)^2*width/(P*(v/4)^2)) R (10*Real.log N)/(x^2*v) ≤
            N^(-actualMassSavingExponent m delta) := by
  let eta := actualMassSavingExponent m delta
  have heta : 0 < eta := actualMassSavingExponent_pos hm hdelta
  have Hdecay := (tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=32*eta) (s:=eta) (by linarith) 9
      (criticalBroadFiniteRateConstant Ctrace Cd Cr Ccut))
  have Hlog := (tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1:ℝ)))
  filter_upwards [Hdecay,Hlog] with n hnRate hnLog
  dsimp only
  intro x P v width diameter R loss hx hP hv hwidthlo hwidthhi hwidthone
    hdiameter hR hloss Htrace Hdiameter Hreverse Hcut
  have hN : 1 ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos n
  exact (critical_broad_finite_saved_envelope_le hm hdelta hN hnLog hx hP hv
    hwidthlo hwidthhi hwidthone hdiameter hR hloss hCtrace hCd hCr hCcut
    Htrace Hdiameter Hreverse Hcut).trans hnRate

end OAI.SKFluctuations.LaplaceWindowFormalization
