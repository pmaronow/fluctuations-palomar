module

public import ComparisonNativeActualIntermediateMassBroadRates
public import SKProof.Port.ComparisonActualOriginalQIntermediateMassNoise
public import SKProof.Port.ComparisonActualOriginalQIntermediateMassDiameter
public import SKProof.Port.ComparisonActualOriginalQIntermediateMassNormalization
public import SKProof.Port.ComparisonActualOriginalQIntermediateMassReverseRates
public import SKProof.Port.ComparisonActualOriginalQLocalDiameterBudgetDefinitions

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem chosen_intermediate_comparable_broad_budget_polynomial_le
    (ell : ℕ) (_hell : 2 < ell) (Q : ℝ) (_hQ : 1 ≤ Q)
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hCt : 0 ≤ Ct) (hC0 : 0 < C0) {Cs c C Cdiam : ℝ}
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hCdiam : 0 < Cdiam)
    (Hreverse : ∀ᶠn : ℕ in atTop,
      ∀a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.xs ≤ 1 → a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs →
        ∀v : ℝ,0 < v → v ≤ 1 → c*a.xs ≤ v → v ≤ C*a.directTestWorkingScale →
          a.canonicalMassReverseAtDiameter ell Q v (a.canonicalChosenHighMassDiameter Cdiam v)*
            ((actualIntermediateMassEffectiveScale a.directTestWorkingScale v)^2/a.xs^4) ≤
              a.data.N^(-(32*actualMassSavingExponent m delta))) :
    ∀ᶠn : ℕ in atTop,
      ∀a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs →
        a.directTestWorkingScale ≤ 1 →
        ∀v width : ℝ,0 < v → v ≤ 1 → c*a.xs ≤ v → v ≤ C*a.directTestWorkingScale →
          v ≤ width → width ≤ 4*v → width ≤ 1 →
          a.canonicalComparableBroadMassBudgetAtDiameter ell Q (10*Real.log a.data.N)
            (a.data.N^(-(10:ℝ))) v width (a.canonicalChosenHighMassDiameter Cdiam v)/
              (a.xs^4*v/(actualIntermediateMassEffectiveScale a.directTestWorkingScale v)^2) ≤
                a.data.N^(-actualMassSavingExponent m delta) := by
  let eta := actualMassSavingExponent m delta
  let loss := nativeOuterComparableTraceConstant cl cu
  let Cfinite := nativeHighMassBroadFiniteConstant 10
  let Cerr := 16*(max 1 C)^2*C0^5/c
  let Ctotal := Cfinite*(loss+2)+Cerr
  have heta : 0 < eta := actualMassSavingExponent_pos hm hdelta
  have HCfinite : 0 ≤ Cfinite := native_high_mass_broad_finite_constant_nonneg (by norm_num)
  have HCerr : 0 ≤ Cerr := by dsimp [Cerr];positivity
  have HCloss : 0 ≤ loss := native_outer_comparable_trace_constant_nonneg hcl hcu
  have Hsquare := eventually_actual_intermediate_mass_diameter_polynomial
    (cl:=cl) (cu:=cu) (Az:=Az) (D:=D) (Bclock:=Bclock) (C:=C)
    hm hdelta hC0 hCt hCs hc hCdiam
  have Hnoise := eventually_actual_intermediate_mass_noise_polynomial
    (cu:=cu) (Ct:=Ct) (D:=D) (Bclock:=Bclock) (C:=C) Q hm hdelta hcl hAz hC0 hCs hc
  have Hdecay := (tendsto_add_atTop_nat 1).eventually
    (native_mass_log_power_decay (q:=32*eta) (s:=eta) (by linarith) 5 Ctotal)
  have Hlog := (tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1:ℝ)))
  filter_upwards [Hreverse,Hsquare,Hnoise,Hdecay,Hlog] with n hnReverse hnSquare hnNoise hnRate hnLog
  intro a hsmall hW1 v width hv hv1 hvlo hvupper hwlo hwhi hw1
  let W := a.directTestWorkingScale
  let B := actualIntermediateMassEffectiveScale W v
  let diam := a.canonicalChosenHighMassDiameter Cdiam v
  let tau := B^2/(a.canonicalMassPower v*v^2*a.xs^4)
  let L := Real.log a.data.N
  have hN : 1 ≤ a.data.N := by dsimp [ActualHighWallData.N];exact_mod_cast Nat.succ_pos n
  have hN0 := a.data.hN
  have hW : 0 < W := a.canonical_direct_test_band_pos
  have hB : 0 < B := actualIntermediateMassEffectiveScale_pos hW hv
  have hP := a.canonical_mass_power_pos v
  have hxs := a.hxs
  have hxs1 := a.canonical_direct_test_band_ge_scale.trans hW1
  have hlog : 1 ≤ Real.log a.data.N := hnLog
  have hcut : 0 < a.data.N^(-(10:ℝ)) := Real.rpow_pos_of_pos hN0 _
  have hwidth : 0 < width := hv.trans_le hwlo
  have hdiam : 0 < diam := a.canonical_chosen_high_mass_diameter_pos hCdiam (by linarith) hv
  have hwidthlog : Real.log (width/a.data.N^(-(10:ℝ))) ≤ 10*Real.log a.data.N := by
    have HH := Real.log_le_log (div_pos hwidth hcut) (div_le_div_of_nonneg_right hw1 hcut.le)
    apply HH.trans_eq
    rw [one_div,Real.log_inv,Real.log_rpow hN0]
    ring
  have hEven : 0 ≤ (2*Q)^(2*ell) := by rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
  have hy : 0 ≤ a.canonicalMassHeight v := by unfold canonicalMassHeight;positivity
  have hR : 0 ≤ a.canonicalMassReverseAtDiameter ell Q v diam := by
    unfold canonicalMassReverseAtDiameter
    exact mul_nonneg (Real.rpow_nonneg hdiam.le _)
      (Real.rpow_nonneg (mul_nonneg hEven (pow_nonneg hy ell)) _)
  have Hnorm := mass_high_broad_finite_normalized_le a.hxs hB (a.canonical_mass_power_pos v)
    hv hwidth.le hwhi hdiam.le hR HCloss hlog (by norm_num : (0:ℝ) ≤ 10) hwidthlog
  change a.canonicalComparableBroadMassBudgetAtDiameter ell Q (10*Real.log a.data.N)
      (a.data.N^(-(10:ℝ))) v width diam/(a.xs^4*v/B^2) ≤
      Cfinite*L^5*(loss*tau/L+diam^2*B^2/a.xs^4+
        a.canonicalMassReverseAtDiameter ell Q v diam*B^2/a.xs^4)+
      16*a.data.N^(-(10:ℝ))*B^2/(a.xs^4*v) at Hnorm
  have Htau : tau ≤ a.data.N^(-(32*eta)) := by
    have HH := (hnNoise a hsmall hW1 v hvlo hvupper).2
    convert HH using 1; dsimp only [tau,B,W]; ring
  have Htrace : loss*tau/L ≤ loss*a.data.N^(-(32*eta)) :=
    (div_le_self (mul_nonneg HCloss (by dsimp [tau];positivity)) hlog).trans
      (mul_le_mul_of_nonneg_left Htau HCloss)
  have HDsaved : diam^2*B^2/a.xs^4 ≤ a.data.N^(-(32*eta)) := by
    simpa only [mul_div_assoc] using (hnSquare a hsmall hW1 v hvlo hvupper).2
  have HRsaved : a.canonicalMassReverseAtDiameter ell Q v diam*B^2/a.xs^4 ≤
      a.data.N^(-(32*eta)) := by
    simpa only [mul_div_assoc] using hnReverse a hxs1 hsmall v hv hv1 hvlo hvupper
  have Hmain := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add Htrace HDsaved) HRsaved)
    (show 0 ≤ Cfinite*L^5 by exact mul_nonneg HCfinite (pow_nonneg (by linarith) _))
  have Hweight := a.canonical_intermediate_normalization_weight_le hm hC0 hN hc hW1 hvlo hvupper
  have Hcut : 16*a.data.N^(-(10:ℝ))*B^2/(a.xs^4*v) ≤
      Cerr*a.data.N^5*a.data.N^(-(10:ℝ)) := by
    have HH := mul_le_mul_of_nonneg_left Hweight
      (show 0 ≤ 16*a.data.N^(-(10:ℝ)) by positivity)
    convert HH using 1 <;> dsimp only [Cerr,B,W] <;> ring
  have Hpowcut : a.data.N^5*a.data.N^(-(10:ℝ))=a.data.N^(-(5:ℝ)) := by
    rw [←Real.rpow_natCast a.data.N 5,←Real.rpow_add hN0]
    norm_num
  have Hbounds := actualMassSavingExponent_bounds m delta
  have HcutPower : a.data.N^(-(5:ℝ)) ≤ a.data.N^(-(32*eta)) :=
    Real.rpow_le_rpow_of_exponent_le hN (by dsimp [eta];nlinarith [Hbounds.1])
  have HcutLog : 1 ≤ L^5 := one_le_pow₀ hlog
  have HCnormal : 16*a.data.N^(-(10:ℝ))*B^2/(a.xs^4*v) ≤ Cerr*L^5*a.data.N^(-(32*eta)) := by
    apply Hcut.trans
    rw [mul_assoc,Hpowcut]
    have HH := mul_le_mul_of_nonneg_left HcutPower HCerr
    have HL := mul_le_mul_of_nonneg_left HcutLog
      (show 0 ≤ Cerr*a.data.N^(-(32*eta)) by positivity)
    nlinarith only [HH,HL]
  have Htotal : a.canonicalComparableBroadMassBudgetAtDiameter ell Q (10*Real.log a.data.N)
      (a.data.N^(-(10:ℝ))) v width diam/(a.xs^4*v/B^2) ≤
        Ctotal*L^5*a.data.N^(-(32*eta)) := by
    apply Hnorm.trans
    have HH := add_le_add Hmain HCnormal
    convert HH using 1
    dsimp [Ctotal]
    ring
  exact Htotal.trans (by simpa only [ActualHighWallData.N] using hnRate)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
