module

public import ComparisonNativeActualIntermediateMassNoise
public import SKProof.Port.ComparisonActualOriginalQIntermediateMassPower
public import SKProof.Port.ComparisonActualOriginalQHighMassCriticalRates

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

theorem canonical_intermediate_mass_noise_bounds
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    {Cs c C v Q : ℝ} (hCs : 0 ≤ Cs) (hc : 0 < c)
    (hsmall : a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs)
    (hW1 : a.directTestWorkingScale ≤ 1)
    (hvlo : c*a.xs ≤ v) (hvupper : v ≤ C*a.directTestWorkingScale) :
    let B := actualIntermediateMassEffectiveScale a.directTestWorkingScale v
    (((Q^2*a.canonicalMassHeight v)/(a.canonicalMassPower v*(16*v)^2))^((2:ℝ)/3)*
      (B^2/a.xs^4) ≤ actualIntermediateMassVarianceConstant Q Cs Az cl c C C0*a.data.N^(-4*m)) ∧
    ((B^2/a.xs^4)/(a.canonicalMassPower v*v^2) ≤
      actualIntermediateMassInverseConstant Cs Az cl c C C0*a.data.N^(-6*m)) := by
  let W := a.directTestWorkingScale
  let B := actualIntermediateMassEffectiveScale W v
  let K := actualIntermediateMassPowerConstant Cs Az cl c C
  let Cy := actualHighMassHeightConstant c
  have hW : 0 < W := a.canonical_direct_test_band_pos
  have hx := a.hxs
  have hv : 0 < v := (mul_pos hc hx).trans_le hvlo
  have hB : 0 < B := actualIntermediateMassEffectiveScale_pos hW hv
  have hK : 0 ≤ K := by
    unfold K actualIntermediateMassPowerConstant
    exact mul_nonneg (sq_nonneg _) (zero_le_one.trans (le_max_left _ _))
  have hCy : 0 ≤ Cy := by dsimp [Cy,actualHighMassHeightConstant];positivity
  have hy0 : 0 ≤ a.canonicalMassHeight v := by unfold canonicalMassHeight;positivity
  have HP := a.canonical_intermediate_effective_power_size hcl hAz hCs hc hsmall hW1 hvlo hvupper
  have Hheight := a.canonical_high_mass_height_le hc hvlo
  have Hvariance := mass_high_variance_noise_le (Q:=Q) a.data.hN (a.canonical_mass_power_pos v)
    hB hv hx hy0 hCy hK Hheight HP
  have Hinv4 := a.canonical_high_mass_inverse_power hC0 4
  have Hinv6 := a.canonical_high_mass_inverse_power hC0 6
  simp only [Nat.cast_ofNat,show (4:ℝ)/6=(2:ℝ)/3 by norm_num] at Hinv4
  simp only [Nat.cast_ofNat,show (6:ℝ)/6=1 by norm_num,Real.rpow_one] at Hinv6
  have HvarInv := mul_le_mul_of_nonneg_left Hinv4
    (show 0 ≤ (Q^2*Cy*K/256)^((2:ℝ)/3) by positivity)
  have Hprod := actualIntermediateMassEffectiveScale_lower_product hx
    a.canonical_direct_test_band_ge_scale hc hvlo
  have Hsecond := mass_intermediate_inverse_noise_le a.data.hN (a.canonical_mass_power_pos v)
    hB hv hx hK (show 0 < (min 1 c)^2 by positivity) Hprod HP
  have HsecondInv := mul_le_mul_of_nonneg_left Hinv6
    (show 0 ≤ K/(min 1 c)^2 by positivity)
  constructor
  · apply Hvariance.trans
    dsimp only [actualIntermediateMassVarianceConstant]
    convert HvarInv using 1 <;> dsimp only [B,W,K,Cy] <;> ring
  · apply Hsecond.trans
    dsimp only [actualIntermediateMassInverseConstant]
    convert HsecondInv using 1; dsimp only [B,W,K]; ring

theorem eventually_actual_intermediate_mass_noise_polynomial
    {m delta cl cu Az C0 Ct D Bclock Cs c C : ℝ} (Q : ℝ)
    (hm : 0 < m) (_hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCs : 0 ≤ Cs) (hc : 0 < c) :
    ∀ᶠn : ℕ in atTop,
      ∀a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.xs^2 ≤ Cs*laplaceComparisonStrength a.data.d a.lam a.xs →
        a.directTestWorkingScale ≤ 1 →
        ∀v : ℝ,c*a.xs ≤ v → v ≤ C*a.directTestWorkingScale →
          let B := actualIntermediateMassEffectiveScale a.directTestWorkingScale v
          (((Q^2*a.canonicalMassHeight v)/(a.canonicalMassPower v*(16*v)^2))^((2:ℝ)/3)*
            (B^2/a.xs^4) ≤ a.data.N^(-(32*actualMassSavingExponent m delta))) ∧
          ((B^2/a.xs^4)/(a.canonicalMassPower v*v^2) ≤
            a.data.N^(-(32*actualMassSavingExponent m delta))) := by
  let eta := actualMassSavingExponent m delta
  have Heta := actualMassSavingExponent_bounds m delta
  have H1 := (tendsto_add_atTop_nat 1).eventually
    (eventually_absorb_fixed_coefficient (e:=-4*m) (eps:=-(32*eta))
      (by dsimp [eta];nlinarith [Heta.2.1]) (actualIntermediateMassVarianceConstant Q Cs Az cl c C C0))
  have H2 := (tendsto_add_atTop_nat 1).eventually
    (eventually_absorb_fixed_coefficient (e:=-6*m) (eps:=-(32*eta))
      (by dsimp [eta];nlinarith [Heta.2.1]) (actualIntermediateMassInverseConstant Cs Az cl c C C0))
  filter_upwards [H1,H2] with n hn1 hn2
  intro a hsmall hW1 v hvlo hvupper
  have H := a.canonical_intermediate_mass_noise_bounds hcl hAz hC0 hCs hc hsmall hW1 hvlo hvupper (Q:=Q)
  exact ⟨H.1.trans hn1,H.2.trans hn2⟩

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
