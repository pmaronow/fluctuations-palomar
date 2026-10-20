module

public import SKProof.Port.ComparisonActualOriginalQBroadMassTrace
public import ComparisonNativeActualHighMassNoiseRates
public import SKProof.Port.ComparisonActualOriginalQHighMassCriticalRates
public import SKProof.Port.ComparisonActualOriginalQHighMassSharpScale

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
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_direct_test_energy_over_band
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (hCt : 0 ≤ Ct) :
    a.data.E/(a.directTestWorkingScale*a.xs^4) ≤
      (Ct+1)/(Real.sqrt a.data.N*a.xs^3) := by
  have Hg : 0 ≤ laplaceComparisonStrength a.data.d a.lam a.xs:=
    (laplaceComparisonStrength_pos _ a.hlam _).le
  have HS:=pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right a.xs
    (Real.sqrt (laplaceComparisonStrength a.data.d a.lam a.xs))) 2
  rw [Real.sq_sqrt Hg] at HS
  exact mass_direct_test_energy_over_band a.data.hN a.data.hE a.hxs
    a.canonical_direct_test_band_pos hCt a.htest HS

theorem canonical_high_mass_noise_bounds
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hcl : 0 < cl) (hAz : 0 ≤ Az) (hCt : 0 ≤ Ct) (hC0 : 0 < C0)
    {Cs c v Q : ℝ} (hCs : 0 ≤ Cs) (hc : 0 < c)
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N)
    (hsmall : a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs)
    (hW1 : a.directTestWorkingScale ≤ 1) (hv : 0 < v)
    (hvlo : c*a.directTestWorkingScale ≤ v) :
    (((Q^2*a.canonicalMassHeight v)/(a.canonicalMassPower v*(16*v)^2))^((2:ℝ)/3)*
        (a.directTestWorkingScale^2/a.xs^4) ≤
      actualHighMassVarianceConstant Q Cs Az cl c C0*a.data.N^(-4*m)) ∧
    ((a.directTestWorkingScale^2/a.xs^4)/(a.canonicalMassPower v*(16*v)^2) ≤
      actualHighMassInverseConstant Cs Az cl c C0*a.data.N^(-6*m)) ∧
    (((1025+25*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U))*
        ((a.directTestWorkingScale^2/a.xs^4)/(a.canonicalMassPower v*v^2)))/Real.log a.data.N ≤
      actualHighMassTraceConstant Cs Az cl c C0 Ct D*a.data.N^(-3*m)) := by
  let W:=a.directTestWorkingScale
  let K:=actualHighMassPowerConstant Cs Az cl c
  let Cy:=actualHighMassHeightConstant c
  let Cr:=1+Real.log (1+D^2)
  let L:=Real.log a.data.N
  have hW : 0 < W:=a.canonical_direct_test_band_pos
  have hxs:=a.hxs
  have hP:=a.canonical_mass_power_pos v
  have hN0:=a.data.hN
  have hU:=a.data.hU
  have hE:=a.data.hE
  have hK : 0 ≤ K:=by
    dsimp [K,actualHighMassPowerConstant,actualHighMassEndpointConstant]
    apply mul_nonneg (sq_nonneg _)
    exact (one_div_pos.mpr hc).le.trans (le_max_left _ _)
  have hCy : 0 ≤ Cy:=by dsimp [Cy,actualHighMassHeightConstant];positivity
  have hCr : 0 ≤ Cr:=by dsimp [Cr];have := Real.log_nonneg (by nlinarith [sq_nonneg D] : (1:ℝ) ≤ 1+D^2);linarith
  have hL : 0 < L:=zero_lt_one.trans_le hlog
  have HX:=a.canonical_direct_test_band_ge_scale
  have Hxv : c*a.xs ≤ v:=(mul_le_mul_of_nonneg_left HX hc.le).trans hvlo
  have Hpower:=a.canonical_direct_test_high_power_size hcl hAz hCs hc hsmall hW1 hvlo
  have Hy:=a.canonical_high_mass_height_le hc Hxv
  have hy0 : 0 ≤ a.canonicalMassHeight v:=by unfold canonicalMassHeight;positivity
  have Hinv4:=a.canonical_high_mass_inverse_power hC0 4
  have Hinv6:=a.canonical_high_mass_inverse_power hC0 6
  have Hinv3:=a.canonical_high_mass_inverse_power hC0 3
  simp only [Nat.cast_ofNat,show (4:ℝ)/6=(2:ℝ)/3 by norm_num] at Hinv4
  simp only [Nat.cast_ofNat,show (6:ℝ)/6=1 by norm_num,Real.rpow_one] at Hinv6
  simp only [Nat.cast_ofNat,show (3:ℝ)/6=(1:ℝ)/2 by norm_num] at Hinv3
  have Hinv3' : 1/(Real.sqrt a.data.N*a.xs^3) ≤ C0^3*a.data.N^(-3*m):=by
    simpa only [Real.sqrt_eq_rpow] using Hinv3
  have Hvar:=mass_high_variance_noise_le (Q:=Q) hN0 hP hW hv hxs hy0 hCy hK Hy Hpower
  have HCvar : 0 ≤ (Q^2*Cy*K/256)^((2:ℝ)/3):=by positivity
  have HvarInv:=mul_le_mul_of_nonneg_left Hinv4 HCvar
  have HvarFinal : ((Q^2*a.canonicalMassHeight v)/(a.canonicalMassPower v*(16*v)^2))^((2:ℝ)/3)*
      (W^2/a.xs^4) ≤ actualHighMassVarianceConstant Q Cs Az cl c C0*a.data.N^(-4*m):=by
    apply Hvar.trans
    unfold actualHighMassVarianceConstant
    convert HvarInv using 1 <;> ring
  have Hsecond:=mass_high_inverse_noise_le hN0 hP hW hv hxs hK hc HX hvlo Hpower
  have HsecondInv:=mul_le_mul_of_nonneg_left Hinv6 (show 0 ≤ K/(256*c) by positivity)
  have HsecondFinal : (W^2/a.xs^4)/(a.canonicalMassPower v*(16*v)^2) ≤
      actualHighMassInverseConstant Cs Az cl c C0*a.data.N^(-6*m):=by
    have HE : (W^2/a.xs^4)/(a.canonicalMassPower v*(16*v)^2)=
        (1/(a.canonicalMassPower v*(16*v)^2))*(W^2/a.xs^4):=by ring
    rw [HE]
    apply Hsecond.trans
    unfold actualHighMassInverseConstant
    convert HsecondInv using 1; ring
  have Henergy:=a.canonical_direct_test_energy_over_band hCt
  have Hr0 : 0 ≤ Real.log ((1+a.data.U)/a.data.U):=
    Real.log_nonneg ((one_le_div hU).mpr (by linarith))
  have Hr:=a.canonical_mass_trace_log_le hN hlog
  have Htrace:=mass_high_broad_trace_noise_le
    (tau:=(W^2/a.xs^4)/(a.canonicalMassPower v*v^2))
    hN0 hP hW hv hxs hU hE hK hc hCr (show 0 ≤ Ct+1 by linarith) hL.le Hr0
    HX hvlo Hpower rfl Hr le_rfl Henergy
  have Hpow : a.data.N^(-6*m) ≤ a.data.N^(-3*m):=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  have Hsix:=Hinv6.trans (mul_le_mul_of_nonneg_left Hpow (pow_nonneg hC0.le 6))
  have Hsmall:=mul_le_mul_of_nonneg_left Hsix (show 0 ≤ (1/c) by positivity)
  have HenergyInv:=mul_le_mul_of_nonneg_left Hinv3' (show 0 ≤ Ct+1 by linarith)
  have HlogOne:=le_mul_of_one_le_left
    (show 0 ≤ (1/c)*(C0^6*a.data.N^(-3*m)) by positivity) hlog
  have HtraceFinal : (1025+25*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U))*
      ((W^2/a.xs^4)/(a.canonicalMassPower v*v^2)) ≤
      actualHighMassTraceConstant Cs Az cl c C0 Ct D*L*a.data.N^(-3*m):=by
    apply Htrace.trans
    have H1 : K*(1025*((1/c)*(1/(a.data.N*a.xs^6)))+
        25*(Cr*L)*((1/c)*(1/(a.data.N*a.xs^6))+(Ct+1)/(Real.sqrt a.data.N*a.xs^3))) ≤
        K*(1025*(L*((1/c)*(C0^6*a.data.N^(-3*m))))+
          25*(Cr*L)*((1/c)*(C0^6*a.data.N^(-3*m))+(Ct+1)*(C0^3*a.data.N^(-3*m)))):=by
      have Hbase:=mul_le_mul_of_nonneg_left (Hsmall.trans HlogOne) (by norm_num : (0:ℝ) ≤ 1025)
      have Henergy' : (Ct+1)/(Real.sqrt a.data.N*a.xs^3) ≤
          (Ct+1)*(C0^3*a.data.N^(-3*m)):=by
        convert HenergyInv using 1; ring
      have Hsum:=add_le_add Hsmall Henergy'
      have Hpart:=mul_le_mul_of_nonneg_left Hsum (show 0 ≤ 25*(Cr*L) by positivity)
      exact mul_le_mul_of_nonneg_left (add_le_add Hbase Hpart) hK
    apply H1.trans_eq
    unfold actualHighMassTraceConstant
    dsimp only [K,Cr]
    ring
  refine ⟨HvarFinal,HsecondFinal,?_⟩
  apply (div_le_iff₀ hL).mpr
  convert HtraceFinal using 1; ring

theorem eventually_actual_high_mass_noise_polynomial
    {m delta cl cu Az C0 Ct D Bclock Cs c : ℝ} (Q : ℝ)
    (hm : 0 < m) (_hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hCt : 0 ≤ Ct) (hC0 : 0 < C0) (hCs : 0 ≤ Cs) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∀a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs →
        a.directTestWorkingScale ≤ 1 →
        ∀v : ℝ,0 < v → c*a.directTestWorkingScale ≤ v →
          ((((Q^2*a.canonicalMassHeight v)/(a.canonicalMassPower v*(16*v)^2))^((2:ℝ)/3)*
            (a.directTestWorkingScale^2/a.xs^4) ≤ a.data.N^(-(32*actualMassSavingExponent m delta))) ∧
          ((a.directTestWorkingScale^2/a.xs^4)/(a.canonicalMassPower v*(16*v)^2) ≤
            a.data.N^(-(32*actualMassSavingExponent m delta))) ∧
          (((1025+25*(1+v/a.data.U)*Real.log ((1+a.data.U)/a.data.U))*
            ((a.directTestWorkingScale^2/a.xs^4)/(a.canonicalMassPower v*v^2)))/Real.log a.data.N ≤
              a.data.N^(-(32*actualMassSavingExponent m delta)))) := by
  let eta:=actualMassSavingExponent m delta
  have Heta:=actualMassSavingExponent_bounds m delta
  have H1:=(tendsto_add_atTop_nat 1).eventually
    (eventually_absorb_fixed_coefficient (e:=-4*m) (eps:=-(32*eta))
      (by dsimp [eta];nlinarith [Heta.2.1]) (actualHighMassVarianceConstant Q Cs Az cl c C0))
  have H2:=(tendsto_add_atTop_nat 1).eventually
    (eventually_absorb_fixed_coefficient (e:=-6*m) (eps:=-(32*eta))
      (by dsimp [eta];nlinarith [Heta.2.1]) (actualHighMassInverseConstant Cs Az cl c C0))
  have H3:=(tendsto_add_atTop_nat 1).eventually
    (eventually_absorb_fixed_coefficient (e:=-3*m) (eps:=-(32*eta))
      (by dsimp [eta];nlinarith [Heta.2.1]) (actualHighMassTraceConstant Cs Az cl c C0 Ct D))
  have Hlog:=(tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1:ℝ)))
  filter_upwards [H1,H2,H3,Hlog] with n hn1 hn2 hn3 hnlog
  intro a hsmall hW1 v hv hvlo
  have hN : 1 ≤ a.data.N:=by dsimp [ActualHighWallData.N];exact_mod_cast Nat.succ_pos n
  have H:=a.canonical_high_mass_noise_bounds hm hcl hAz hCt hC0 hCs hc hN hnlog hsmall hW1 hv hvlo (Q:=Q)
  exact ⟨H.1.trans hn1,H.2.1.trans hn2,H.2.2.trans hn3⟩

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
