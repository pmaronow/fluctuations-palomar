module

public import SKProof.Port.ComparisonActualOriginalQFullThermalHighJointFactory
public import SKProof.Port.ComparisonActualOriginalQLimitRigidity
public import SKProof.Port.ComparisonActualOriginalQRadiusClocks
public import SKProof.Port.ComparisonActualOriginalQRadiusStripConcentration
public import SKProof.Port.ComparisonActualOriginalQWorkingScale
public import SKProof.Port.ComparisonActualOriginalQFullThermalGapIntegration
public import SKProof.Port.ComparisonActualOriginalQNormalizedScalarGap
public import SKProof.Port.ComparisonActualOriginalQRadiusScalarModulus
public import SKProof.Port.ComparisonActualOriginalQRadiusScalarRescaling
public import SKProof.Port.ComparisonActualOriginalQOriginalThermalNormUpperAlong
public import SKProof.Port.ComparisonActualOriginalQHighFlatRadiusGradient
public import SKProof.Port.ComparisonActualOriginalQScaledRadiusIntegrability
public import SKProof.Port.ComparisonActualOriginalQVirtualGapExistenceAlong
public import ComparisonNativeActualLocalScalarDensityBounds
public import SKProof.Port.OriginalQHighOnlyBridge

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option maxRecDepth 4000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal

private theorem eventually_rmin_le_of_positive_mass_original_q
    {dim : ℕ→ℕ} {m delta cl cu Az C0 Ct D Bclock T c : ℝ}
    {M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    (G : OriginalQComparableBandContext M T) (hc : 0 < c) :
    ∀ᶠn in atTop,∀r : ℝ,c*(M n).xs ≤ (M n).alpha.val.val r →
      (M n).data.rmin ≤ r := by
  filter_upwards [G.omission_over_test_zero_original_q.eventually (eventually_lt_nhds hc)]
    with n hn r hmass
  have hs : (M n).data.s < c*(M n).xs := (div_lt_iff₀ (M n).hxs).mp hn
  by_contra hr
  have H := (M n).alpha.val.property.2 (le_of_not_ge hr)
  rw [(M n).alpha.property.1] at H
  exact (hs.trans_le (hmass.trans H)).false

theorem exists_actual_selected_bad_history_original_scalar_gap_integral_along_comparable_macro_of_full_thermal_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (Atarget : ℝ) (hAtarget : 0 < Atarget)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs) :
    ∃eta : ℕ→ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ActualOriginalScalarGapIntegralOnBandAlong_original_q
        (G.hT) Atarget eta M  := by
  have hlo : ∀ᶠn in atTop,w0 ≤ (M n).directTestWorkingScale := by
    simpa only [hcanonical] using hWlower
  have hup : ∀ᶠn in atTop,(M n).directTestWorkingScale ≤ 1 := by
    simpa only [hcanonical] using hWupper
  exact actual_comparable_context_original_scalar_gap_integral_of_full_thermal_original_q
    Atarget hAtarget hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G Hfull

theorem exists_actual_selected_bad_history_original_scalar_gap_pointwise_along_comparable_macro_of_full_thermal_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (Atarget : ℝ) (hAtarget : 0 < Atarget)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ rate : ℕ→ℝ,
      (∀n,0 ≤ rate n) ∧ Tendsto rate atTop (𝓝 0) ∧
      ∀ᶠn in atTop,
        ∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
        ∀u : ℝ, 0 < u → u ≤ Atarget*(M n).xs →
          |orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u-
            scalarCovarianceResponse (G.hT)
              ((M n).inheritedScalarMassProfileBare
                (G.hT) htotal)
              (actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf u)| ≤
          C*(M n).xs^2*(Real.sqrt (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
            (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2)+1/(dim n+1:ℕ))+
              rate n*(M n).xs^3  := by
  have hlo : ∀ᶠn in atTop,w0 ≤ (M n).directTestWorkingScale := by
    simpa only [hcanonical] using hWlower
  have hup : ∀ᶠn in atTop,(M n).directTestWorkingScale ≤ 1 := by
    simpa only [hcanonical] using hWupper
  exact actual_comparable_context_original_scalar_gap_pointwise_of_full_thermal_original_q
    Atarget hAtarget hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G Hfull

end OAI.SKFluctuations.LaplaceWindowFormalization
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity ActualThetaZeroOverlapMinimum
open scoped Topology ENNReal
set_option maxHeartbeats 12000000

theorem exists_actual_selected_bad_history_normalized_scalar_gap_along_comparable_macro_of_full_thermal_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (Atarget : ℝ) (hAtarget : 0 < Atarget)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs) :
    ∃eta : ℕ→ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      (∀ᶠn in atTop,∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
        ∀v∈Icc (0:ℝ) 1,v ≤ Atarget*(M n).xs →
          Integrable (fun z : ParisiFinite.OrderPoint =>
            (M n).inheritedScalarCavityResidual (G.hT)
              htotal z/(M n).xs^3) (comparisonNormalizedClockMass (M n).xs v) ∧
          (∫z : ParisiFinite.OrderPoint,
            |(M n).inheritedScalarCavityResidual (G.hT)
              htotal z/(M n).xs^3| ∂comparisonNormalizedClockMass (M n).xs v) ≤ eta n) ∧
      (∀htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
        ∀v : ℕ→ℝ,(∀n,v n∈Icc (0:ℝ) 1) →
        (∀ᶠn in atTop,v n ≤ Atarget*(M n).xs) →
          (∀n,Integrable (fun z : ParisiFinite.OrderPoint =>
            (M n).inheritedScalarCavityResidual (G.hT)
              (htotal n) z/(M n).xs^3) (comparisonNormalizedClockMass (M n).xs (v n))) ∧
          Tendsto (fun n=>∫z : ParisiFinite.OrderPoint,
            |(M n).inheritedScalarCavityResidual (G.hT)
              (htotal n) z/(M n).xs^3| ∂comparisonNormalizedClockMass (M n).xs (v n))
            atTop (𝓝 0)) := by
  have hTemp : 0 < T := G.hT
  obtain ⟨eta,heta,hetalim,Hgap⟩ :=
    exists_actual_selected_bad_history_original_scalar_gap_integral_along_comparable_macro_of_full_thermal_original_q
      Atarget hAtarget hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim M G Hfull W hcanonical w0 hw0 hWlower hWupper hcompare
  have hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := G.xs_zero
  refine ⟨eta,heta,hetalim,
    actual_original_scalar_gap_normalized_envelope_along_original_q
      (G.hT) hAtarget eta M hxlim Hgap,?_⟩
  intro htotal v hv hvA
  exact actual_original_scalar_gap_normalized_l1_tendsto_zero_along_original_q
    (G.hT) hAtarget eta hetalim M htotal hxlim Hgap v hv hvA

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 20000000

theorem exists_actual_selected_bad_history_radius_scalar_gap_integral_along_comparable_macro_of_full_thermal_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs) :
    ∃eta : ℕ→ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ᶠn in atTop,
        ∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
        (∫r in (M n).actualRadiusTargetStrip c C,
          |orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf ((M n).alpha.val.val r)-
            scalarCovarianceResponse (G.hT)
              ((M n).inheritedScalarMassProfileBare
                (G.hT) htotal)
              (actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf ((M n).alpha.val.val r))|)/
          (M n).xs^4 ≤ eta n := by
  have hTemp : 0 < T := G.hT
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := G.xs_zero
  have Hthermal := actual_selected_bad_history_radius_strip_thermal_tendsto_zero_along_comparable_context
    (c:=c) (C:=C) Bclock hm hdelta (by linarith) hcl hcu hAz hC0 hCt hc
    dim hdim M hx G
  obtain ⟨Cp,hCp,rate,hrate,Hrate,Hpoint⟩ :=
    exists_actual_selected_bad_history_original_scalar_gap_pointwise_along_comparable_macro_of_full_thermal_original_q C hC
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G Hfull W hcanonical w0 hw0 hWlower hWupper hcompare
  let eta := fun n=>Cp*Real.sqrt (C*((∫r in (M n).actualRadiusTargetStrip c C,
      (M n).cavityRadiusPointDefect r)/(M n).xs^3))+
      Cp*C/((M n).data.N*(M n).xs)+C*rate n
  have Hsite:=actual_comparable_context_scalar_site_ratio_tendsto_zero_original_q hm hC0 dim hdim M G
  have Heta : Tendsto eta atTop (𝓝 0) := by
    have H:=(((Hthermal.const_mul C).sqrt.const_mul Cp).add (Hsite.const_mul (Cp*C))).add
      (Hrate.const_mul C)
    simpa only [eta,mul_zero,Real.sqrt_zero,add_zero,mul_one_div] using H
  refine ⟨eta,?_,Heta,?_⟩
  · intro n
    exact add_nonneg (add_nonneg (mul_nonneg hCp (Real.sqrt_nonneg _))
      (div_nonneg (mul_nonneg hCp hC.le)
        (mul_nonneg (M n).data.hN.le (M n).hxs.le)))
      (mul_nonneg hC.le (hrate n))
  · filter_upwards [Hpoint] with n hn
    obtain ⟨htotal,hn⟩:=hn
    refine ⟨htotal,?_⟩
    let F:=(M n).actualRadiusTargetStrip c C
    have := (M n).actual_radius_target_strip_finite_measure c C
    apply (M n).actual_original_radius_scalar_modulus_integral_le
      (G.hT) _ F
      ((M n).actual_radius_target_strip_measurable c C)
      (fun r hr=>⟨(M n).data.rmin_nonneg.trans hr.1.1,hr.1.2.trans (min_le_right _ _)⟩)
      hCp hC.le (hrate n)
    · simpa only [measureReal_restrict_apply_univ] using
        (M n).actual_radius_target_strip_measure_le c C hC.le
    · intro r hr
      exact hn ((M n).alpha.val.val r) ((mul_pos hc (M n).hxs).trans_le hr.2.1) hr.2.2

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 20000000

theorem actual_selected_bad_history_compact_radius_cavity_L1_along_comparable_macro_of_full_thermal_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c C a b : ℝ) (hc : 0 < c) (_hC : 0 < C) (ha : 0 ≤ a) (hab : a < b)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (hmass : ∀ᶠn in atTop,∀t∈Icc a b,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) ∧
        (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs) :
    Tendsto (fun n=>∫t in Icc a b,
      |(orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf ((M n).alpha.val.val ((M n).xs*t))-
        scalarCovarianceResponse (G.hT)
          ((M n).inheritedScalarMassProfileBare (G.hT) (htotal n))
          (actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf
            ((M n).alpha.val.val ((M n).xs*t))))/(M n).xs^3|) atTop (𝓝 0) := by
  have hTemp : 0 < T := G.hT
  let Cbig:=max 1 (max C b)
  have hbig : 0 < Cbig:=zero_lt_one.trans_le (le_max_left _ _)
  have hCb : C ≤ Cbig := (le_max_left _ _).trans (le_max_right _ _)
  have hbb : b ≤ Cbig := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨eta,heta,Heta,Hbound⟩:=
    exists_actual_selected_bad_history_radius_scalar_gap_integral_along_comparable_macro_of_full_thermal_original_q c Cbig hc hbig
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G Hfull W hcanonical w0 hw0 hWlower hWupper hcompare
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := G.xs_zero
  have hxb : Tendsto (fun n=>(M n).xs*b) atTop (𝓝 0) := by
    simpa only [zero_mul] using hx.mul_const b
  have hsmall : ∀ᶠn in atTop,(M n).xs*b ≤ 1 :=
    hxb.eventually (eventually_le_nhds zero_lt_one)
  apply squeeze_zero' (Eventually.of_forall (fun n=>integral_nonneg (fun t=>abs_nonneg _))) _ Heta
  filter_upwards [Hbound,hmass,hsmall,eventually_rmin_le_of_positive_mass_original_q G hc]
    with n hn hmN hsN hphysical
  obtain ⟨ht,hn⟩:=hn
  let f:=fun r=>orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf ((M n).alpha.val.val r)-
    scalarCovarianceResponse (G.hT)
      ((M n).inheritedScalarMassProfileBare (G.hT) (htotal n))
      (actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf ((M n).alpha.val.val r))
  have hf : IntegrableOn f ((M n).actualRadiusTargetStrip c Cbig) :=
    ((M n).original_scalar_radius_gap_integrableOn
      (G.hT) _).mono_set
      (fun r hr=>⟨(M n).data.rmin_nonneg.trans hr.1.1,hr.1.2.trans (min_le_right _ _)⟩)
  have H:=(M n).radius_scalar_residual_compact_integral_le
    (hphysical _ (hmN a ⟨le_rfl,hab.le⟩).1) hab.le hbb hsN
    (fun t ht=>⟨(hmN t ht).1,(hmN t ht).2.trans
      (mul_le_mul_of_nonneg_right hCb (M n).hxs.le)⟩) f hf
  exact H.trans hn

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity ActualThetaZeroOverlapMinimum
open scoped Topology ENNReal NNReal
set_option maxHeartbeats 20000000

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 24000000

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 16000000

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 20000000

theorem exists_actual_selected_bad_history_radius_scalar_gap_uniform_along_comparable_macro_of_full_thermal_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs) :
    ∃B : ℝ,0 < B ∧ ∀ᶠn in atTop,
      ∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
      ∀r∈(M n).actualRadiusTargetStrip c C,
        |(orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf ((M n).alpha.val.val r)-
          scalarCovarianceResponse (G.hT)
            ((M n).inheritedScalarMassProfileBare
              (G.hT) htotal)
            (actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf ((M n).alpha.val.val r)))/(M n).xs^3| ≤ B := by
  have hTemp : 0 < T := G.hT
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := G.xs_zero
  obtain ⟨Cp,hCp,rate,hrate,Hrate,Hpoint⟩:=
    exists_actual_selected_bad_history_original_scalar_gap_pointwise_along_comparable_macro_of_full_thermal_original_q C hC
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G Hfull W hcanonical w0 hw0 hWlower hWupper hcompare
  obtain ⟨Cd,hCd,HD⟩:=eventually_actual_original_thermal_norm_upper_along_original_q
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G C hC.le
  have Hsite:=actual_comparable_context_scalar_site_ratio_tendsto_zero_original_q hm hC0 dim hdim M G
  let B:=Cp*(Cd+1)+1
  have hB : 0 < B:=by dsimp only [B];positivity
  refine ⟨B,hB,?_⟩
  filter_upwards [Hpoint,HD,Hrate.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1)),
    Hsite.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))] with n hn hDn hrate1 hsite1
  obtain ⟨htotal,hn⟩:=hn
  refine ⟨htotal,?_⟩
  intro r hr
  let u:=(M n).alpha.val.val r
  have hu : 0 < u:=(mul_pos hc (M n).hxs).trans_le hr.2.1
  have hu1 : u ≤ 1:=((M n).alpha.val.property.1 r).2
  have huC : u ≤ C*(M n).xs:=hr.2.2
  have HP:=hn u hu huC
  have HDD:=hDn u ⟨hu,hu1⟩ huC
  have HN : 1/(dim n+1:ℕ) ≤ (M n).xs:=by
    have H:=(div_le_iff₀ (mul_pos (M n).data.hN (M n).hxs)).mp hsite1
    apply (div_le_iff₀ (show (0:ℝ)<(dim n+1:ℕ) from by exact_mod_cast Nat.zero_lt_succ _)).mpr
    simpa only [NativeOverlapContext.N,mul_comm,mul_one] using H
  rw [abs_div,abs_of_pos (pow_pos (M n).hxs 3)]
  apply (div_le_iff₀ (pow_pos (M n).hxs 3)).mpr
  have HM:=mul_le_mul_of_nonneg_left (add_le_add HDD HN) (mul_nonneg hCp (sq_nonneg (M n).xs))
  have HE:=mul_le_mul_of_nonneg_right hrate1 (pow_pos (M n).hxs 3).le
  apply HP.trans
  dsimp only [B]
  nlinarith only [HM,HE]

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy ActualThetaZeroOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 20000000

theorem actual_selected_bad_history_high_radius_uniform_identification_along_comparable_macro_of_full_thermal_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c C a b : ℝ) (hc : 0 < c) (hC : 0 < C) (ha : 0 ≤ a) (hab : a < b)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (hmass : ∀ᶠn in atTop,∀t∈Icc a b,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) ∧
        (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (g : ℝ→ℝ)
    (hG : ∀Q > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (G.hT)
        ((M n).inheritedScalarMassProfileBare (G.hT) (htotal n)))
      T (M n).xs) g atTop (Icc (0:ℝ) Q))
    (hg : ∀Q > 0,ContinuousOn g (Icc (0:ℝ) Q)) :
    let Gamma := fun n=>scalarCovarianceResponse (G.hT)
      ((M n).inheritedScalarMassProfileBare (G.hT) (htotal n))
    let S := fun n t=>orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf
      ((M n).alpha.val.val ((M n).xs*t))
    let K := fun n t=>actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf
      ((M n).alpha.val.val ((M n).xs*t))
    TendstoUniformlyOn (fun n t=>S n t/(M n).xs) (fun t=>t) atTop (Icc a b) ∧
    TendstoUniformlyOn (fun n t=>K n t/(T*(M n).xs)) (fun t=>t) atTop (Icc a b) ∧
    TendstoUniformlyOn (fun n t=>comparisonRescaledScalarResponse (Gamma n) T (M n).xs
      (K n t/(T*(M n).xs))) g atTop (Icc a b) ∧
    TendstoUniformlyOn (fun n t=>
      (((M n).b ((M n).alpha.val.val ((M n).xs*t))-T)*S n t+
        (M n).h ((M n).alpha.val.val ((M n).xs*t)))/(M n).xs^3)
      (fun _=>0) atTop (Icc a b) := by
  have hTemp : 0 < T := G.hT
  intro Gamma S K
  let h0 := fun n t=>(M n).h ((M n).alpha.val.val ((M n).xs*t))
  let b0 := fun n t=>(M n).b ((M n).alpha.val.val ((M n).xs*t))
  let Hctx := G
  let Gresponse := fun n=>comparisonRescaledScalarResponse (Gamma n) T (M n).xs
  have hbpos : 0 < b := ha.trans_lt hab
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := G.xs_zero
  obtain ⟨Cs,Q,hCs,hQ,Hclock,Hz⟩ := actual_comparable_context_positive_radius_clock_control_original_q
    c C a b hc hC hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M Hctx hx htotal hmass
  let Qbig := max Q b
  have hQbig : 0 < Qbig := hQ.trans_le (le_max_left _ _)
  have Hrange : ∀ᶠn in atTop,∀t∈Icc a b,K n t/(T*(M n).xs)∈Icc (0:ℝ) Qbig := by
    filter_upwards [Hclock] with n hn t ht
    exact ⟨(hn t ht).2.2.1,(hn t ht).2.2.2.trans (le_max_left _ _)⟩
  obtain ⟨CG,hCG,Hscalar⟩ := comparison_scalar_compact_response_eventually_bounded
    Gresponse g (hG Qbig hQbig) (hg Qbig hQbig)
  let Cbig := max 1 (max C b)
  have hbig : 0 < Cbig := zero_lt_one.trans_le (le_max_left _ _)
  have hCb : C ≤ Cbig := (le_max_left _ _).trans (le_max_right _ _)
  have hbb : b ≤ Cbig := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨CR,hCR,Hrho⟩ := exists_actual_selected_bad_history_radius_scalar_gap_uniform_along_comparable_macro_of_full_thermal_original_q
    c Cbig hc hbig hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim M Hctx Hfull W hcanonical w0 hw0 hWlower hWupper hcompare
  have Hsmall : ∀ᶠn in atTop,(M n).xs*b ≤ 1 := by
    have H : Tendsto (fun n=>(M n).xs*b) atTop (𝓝 0) := by simpa only [zero_mul] using hx.mul_const b
    exact H.eventually (eventually_le_nhds zero_lt_one)
  have Hr : ∀ᶠn in atTop,∀t∈Icc a b,|(S n t-Gamma n (K n t))/(M n).xs^3| ≤ CR := by
    filter_upwards [Hrho,Hsmall,hmass,eventually_rmin_le_of_positive_mass_original_q G hc]
      with n hn hs hmN hphysical t ht
    obtain ⟨htotalN,hn⟩ := hn
    apply hn ((M n).xs*t)
    refine ⟨⟨hphysical _ (hmN t ht).1,le_min ?_ ?_⟩,(hmN t ht).1,?_⟩
    · nlinarith only [ht.2,hbb,(M n).hxs]
    · exact (mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hs
    · exact (hmN t ht).2.trans (mul_le_mul_of_nonneg_right hCb (M n).hxs.le)
  have Hclosure := eventually_actual_high_flat_radius_gradient_closure_above_mass
    dim M hx hlarge G.omission_over_test_zero_original_q c hc a b ha hab Gamma T hTemp
  have Hnative : ∀ᶠn in atTop,∀t∈Icc a b,K n t=
      comparisonNativeScalarClock (h0 n t) (b0 n t) (M n).lam ((M n).xs*t) (S n t) := by
    filter_upwards [Hclosure,hmass] with n hn hmN t ht
    exact (hn t ht (hmN t ht).1).1

  let Cprod := |T| *(CG+CR)+1
  have hprod : 0 ≤ Cprod := by dsimp only [Cprod];positivity
  have Hbudget : ∀ᶠn in atTop,∀t∈Icc a b,
      |((M n).lam/(M n).xs^2)*(S n t/(M n).xs-t)| ≤ Cprod := by
    filter_upwards [Hnative,Hrange,Hscalar,Hr,(Metric.tendstoUniformlyOn_iff.mp Hz) 1 zero_lt_one]
      with n hn hmN hGbound hr hz t ht
    apply comparison_scalar_product_bound (Gamma n) hTemp.ne' (M n).hxs.ne'
    · rw [←hn t ht]
      exact hGbound _ (hmN t ht)
    · rw [←hn t ht]
      exact hr t ht
    · simpa only [Real.dist_eq,zero_sub,abs_neg] using (hz t ht).le
  have Hlarge : Tendsto (fun n=>(M n).lam/(M n).xs^2) atTop atTop :=
    tendsto_atTop_mono (fun n=>div_le_div_of_nonneg_right
      (laplaceComparisonStrength_le (M n).data.d (M n).hlam.le (M n).xs)
      (sq_nonneg (M n).xs)) hlarge
  obtain ⟨Hspin,HqNative⟩ := comparison_large_strength_uniform_spin_clock h0 b0 S
    (fun n=>(M n).lam) (fun n=>(M n).xs) hTemp (fun n=>(M n).hxs) hx hprod Hlarge Hbudget Hz
  have Hq : TendstoUniformlyOn (fun n t=>K n t/(T*(M n).xs)) (fun t=>t) atTop (Icc a b) :=
    HqNative.congr (Hnative.mono (fun n hn t ht=>
      congrArg (fun z=>z/(T*(M n).xs)) (hn t ht).symm))
  have HP := comparison_uniform_response_at_moving_clock Gresponse g
    (fun n t=>K n t/(T*(M n).xs))
    (fun t ht=>⟨ha.trans ht.1,ht.2.trans (le_max_right _ _)⟩)
    (hG Qbig hQbig) (hg Qbig hQbig) Hq Hrange
  exact ⟨Hspin,Hq,HP,Hz⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy ActualThetaZeroOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 20000000

theorem actual_selected_bad_history_high_radius_gradient_L1_along_comparable_macro_of_full_thermal_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c C a b : ℝ) (hc : 0 < c) (hC : 0 < C) (ha : 0 ≤ a) (hab : a < b)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (hmass : ∀ᶠn in atTop,∀t∈Icc a b,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) ∧
        (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (g : ℝ→ℝ)
    (hG : ∀Q > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (G.hT)
        ((M n).inheritedScalarMassProfileBare (G.hT) (htotal n)))
      T (M n).xs) g atTop (Icc (0:ℝ) Q))
    (hg : ∀Q > 0,ContinuousOn g (Icc (0:ℝ) Q)) :
    (∀ᶠn in atTop,IntegrableOn (M n).actualVirtualScaledGradient (Icc a b)) ∧
    Tendsto (fun n=>∫t in Icc a b,
      |(M n).actualVirtualScaledGradient t-(-2*T*g t)|) atTop (𝓝 0) := by
  have hTemp : 0 < T := G.hT
  let Gamma := fun n=>scalarCovarianceResponse (G.hT)
    ((M n).inheritedScalarMassProfileBare (G.hT) (htotal n))
  let S := fun n t=>orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf
    ((M n).alpha.val.val ((M n).xs*t))
  let K := fun n t=>actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf
    ((M n).alpha.val.val ((M n).xs*t))
  let P := fun n t=>comparisonRescaledScalarResponse (Gamma n) T (M n).xs
    (K n t/(T*(M n).xs))
  let rho := fun n t=>(S n t-Gamma n (K n t))/(M n).xs^3
  let zeta := fun n t=>
    (((M n).b ((M n).alpha.val.val ((M n).xs*t))-T)*S n t+
      (M n).h ((M n).alpha.val.val ((M n).xs*t)))/(M n).xs^3
  obtain ⟨_Hspin,_Hclock,HP,Hz⟩ := actual_selected_bad_history_high_radius_uniform_identification_along_comparable_macro_of_full_thermal_original_q
    c C a b hc hC ha hab hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim M G Hfull W hcanonical w0 hw0 hWlower hWupper hcompare htotal hmass hlarge g hG hg
  have Hr := actual_selected_bad_history_compact_radius_cavity_L1_along_comparable_macro_of_full_thermal_original_q
    c C a b hc hC ha hab hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim M G Hfull W hcanonical w0 hw0 hWlower hWupper hcompare htotal hmass
  have Hi n := (M n).actual_scaled_radius_scalar_integrability
    (G.hT) hTemp
    ((M n).inheritedScalarMassProfileBare (G.hT) (htotal n)) a b
  have hPi n : IntegrableOn (P n) (Icc a b) := (Hi n).2.2.2.1
  have hri n : IntegrableOn (rho n) (Icc a b) := (Hi n).2.2.1
  have hzi n : IntegrableOn (zeta n) (Icc a b) := (Hi n).2.2.2.2
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := G.xs_zero
  have Hclosure := eventually_actual_high_flat_radius_gradient_closure_above_mass
    dim M hx hlarge G.omission_over_test_zero_original_q c hc a b ha hab Gamma T hTemp
  have Heq : ∀ᶠn in atTop,∀t∈Icc a b,(M n).actualVirtualScaledGradient t=
      -2*T*(P n t+rho n t)-2*zeta n t := by
    filter_upwards [Hclosure,hmass] with n hn hmN t ht
    simpa only [P,rho,zeta,S,K,mul_div_assoc] using (hn t ht (hmN t ht).1).2
  have Hfi : ∀ᶠn in atTop,IntegrableOn (M n).actualVirtualScaledGradient (Icc a b) := by
    filter_upwards [Heq] with n hn
    apply (((hPi n).add (hri n)).const_mul (-2*T)).sub ((hzi n).const_mul 2) |>.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hn t ht).symm
  refine ⟨Hfi,?_⟩
  have hgi : IntegrableOn g (Icc a b) :=
    ((hg b (ha.trans_lt hab)).mono (fun t ht=>⟨ha.trans ht.1,ht.2⟩)).integrableOn_Icc
  exact comparison_scalar_density_eventual_L1_tendsto (fun n=>(M n).actualVirtualScaledGradient)
    P rho zeta g T a b Hfi hPi hri hzi hgi Heq HP Hr Hz

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy ActualThetaZeroOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 20000000

theorem eventually_actual_history_high_gradient_uniform_above_mass_along_comparable_macro_of_full_thermal_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c B : ℝ) (hc : 0 < c) (hB : 0 < B)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (g : ℝ→ℝ)
    (hG : ∀Q > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (G.hT)
        ((M n).inheritedScalarMassProfileBare (G.hT) (htotal n)))
      T (M n).xs) g atTop (Icc (0:ℝ) Q))
    (hg : ∀Q > 0,ContinuousOn g (Icc (0:ℝ) Q)) :
    ∃CG : ℝ,0 < CG ∧ ∀ᶠn in atTop,∀t∈Icc (0:ℝ) B,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) →
        |(M n).actualVirtualScaledGradient t| ≤ CG := by
  have hTemp : 0 < T := G.hT
  let Gamma := fun n=>scalarCovarianceResponse (G.hT)
    ((M n).inheritedScalarMassProfileBare (G.hT) (htotal n))
  let S := fun n t=>orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf
    ((M n).alpha.val.val ((M n).xs*t))
  let K := fun n t=>actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf
    ((M n).alpha.val.val ((M n).xs*t))
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := G.xs_zero
  let Cm := 1+cu*(B+Az)
  have hCm : 0 < Cm := by dsimp only [Cm];positivity
  have Hsmall : ∀ᶠn in atTop,(M n).xs*B ≤ 1 := by
    have H : Tendsto (fun n=>(M n).xs*B) atTop (𝓝 0) := by simpa only [zero_mul] using hx.mul_const B
    exact H.eventually (eventually_le_nhds zero_lt_one)
  have Hupper : ∀ᶠn in atTop,∀t∈Icc (0:ℝ) B,
      (M n).alpha.val.val ((M n).xs*t) ≤ Cm*(M n).xs := by
    filter_upwards [Hsmall] with n hn t ht
    let z := max ((M n).xs*B) (M n).z
    have hz : z∈Icc (M n).z 1 := ⟨le_max_right _ _,max_le hn (M n).hz.2⟩
    have hzsize : z ≤ (B+Az)*(M n).xs := by
      apply max_le
      · nlinarith only [mul_nonneg hAz (M n).hxs.le]
      · nlinarith only [(M n).hzxs,mul_nonneg hB.le (M n).hxs.le]
    have H := ((M n).alpha.val.property.2
      ((mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans (le_max_left _ _))).trans
      ((M n).regular z hz).2
    have HM := mul_le_mul_of_nonneg_left hzsize hcu.le
    dsimp only [Cm]
    nlinarith only [H,HM,(M n).hxs]
  obtain ⟨Cs,Q,hCs,hQ,Hclock⟩ := actual_comparable_context_radius_clock_bounds_original_q
    Cm 0 B hCm hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G hx htotal Hupper
  let epsBare:=1/(Cs+1)
  have hepsBare : 0 < epsBare:=by dsimp only [epsBare];positivity
  have Hbare:=G.positive_band_clocks_original_q c Cm epsBare hc hCm.le hepsBare
  obtain ⟨CP,hCP,HP⟩ := comparison_scalar_compact_response_eventually_bounded
    (fun n=>comparisonRescaledScalarResponse (Gamma n) T (M n).xs) g
    (hG Q hQ) (hg Q hQ)
  let Cbig := max Cm B
  have hbig : 0 < Cbig := hCm.trans_le (le_max_left _ _)
  obtain ⟨CR,hCR,HR⟩ := exists_actual_selected_bad_history_radius_scalar_gap_uniform_along_comparable_macro_of_full_thermal_original_q
    c Cbig hc hbig hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim M G Hfull W hcanonical w0 hw0 hWlower hWupper hcompare
  have Hclosure := eventually_actual_high_flat_radius_gradient_closure_above_mass
    dim M hx hlarge G.omission_over_test_zero_original_q c hc 0 B le_rfl hB Gamma T hTemp
  refine ⟨2*|T| *(CP+CR)+2,by positivity,?_⟩
  filter_upwards [Hsmall,Hupper,Hclock,HP,HR,Hclosure,
    Hbare,eventually_rmin_le_of_positive_mass_original_q G hc]
    with n hs hu hclock hp hr hclosure hbare hphysical t ht hlo
  obtain ⟨htotalN,hr⟩ := hr
  have hstrip : (M n).xs*t∈(M n).actualRadiusTargetStrip c Cbig := by
    refine ⟨⟨hphysical _ hlo,le_min ?_ ?_⟩,hlo,?_⟩
    · exact (mul_le_mul_of_nonneg_left (ht.2.trans (le_max_right _ _)) (M n).hxs.le).trans_eq (mul_comm _ _)
    · exact (mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hs
    · exact (hu t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (M n).hxs.le)
  have hP := hp _ (hclock t ht).2.2
  have hR : |(S n t-Gamma n (K n t))/(M n).xs^3| ≤ CR := hr _ hstrip
  have hZ : |(((M n).b ((M n).alpha.val.val ((M n).xs*t))-T)*S n t+
      (M n).h ((M n).alpha.val.val ((M n).xs*t)))/(M n).xs^3| ≤ 1 := by
    let u:=(M n).alpha.val.val ((M n).xs*t)
    have Hbare:=hbare u ⟨hlo,le_min (hu t ht) ((M n).alpha.val.property.1 _).2⟩
    have HS:=(hclock t ht)
    have Hmul:=mul_le_mul Hbare.1 HS.2.1 HS.1 (mul_nonneg hepsBare.le (sq_nonneg (M n).xs))
    have HA:=abs_add_le (((M n).b u-T)*S n t) ((M n).h u)
    rw [abs_mul,abs_of_nonneg HS.1] at HA
    rw [abs_div,abs_of_pos (pow_pos (M n).hxs 3)]
    apply (div_le_iff₀ (pow_pos (M n).hxs 3)).mpr
    have Heq : (Cs+1)*epsBare=1 := by dsimp only [epsBare];field_simp
    have Heq3:=congrArg (fun v : ℝ=>v*(M n).xs^3) Heq
    simp only [one_mul] at Heq3
    dsimp only [u] at HA Hmul Hbare
    nlinarith only [HA,Hmul,Hbare.2,Heq3]
  have H := comparison_scalar_density_error_bound (g:=0) (by
    simpa only [mul_div_assoc] using (hclosure t ht hlo).2)
  simp only [mul_zero,sub_zero] at H
  have HPmul := mul_le_mul_of_nonneg_left hP (show 0 ≤ 2*|T| by positivity)
  have HRmul := mul_le_mul_of_nonneg_left hR (show 0 ≤ 2*|T| by positivity)
  dsimp only [S,K] at hZ HRmul
  nlinarith only [H,HPmul,HRmul,hZ]

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy ActualThetaZeroOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 20000000

theorem actual_selected_bad_history_high_virtual_gap_data_along_comparable_macro_of_full_thermal_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    {a b B : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbB : b < B)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (g : ℝ→ℝ)
    (hG : ∀Q > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (G.hT)
        ((M n).inheritedScalarMassProfileBare (G.hT) (htotal n)))
      T (M n).xs) g atTop (Icc (0:ℝ) Q))
    (hg : ∀Q > 0,ContinuousOn g (Icc (0:ℝ) Q))
    (V : ℝ→ℝ) (hV : Monotone V) (hnegative : ∀t<0,V t=0)
    (hCDF : ∀s,Tendsto (fun n=>(M n).alpha.val.val ((M n).xs*s)/(M n).xs) atTop (𝓝 (V s)))
    (hasupport : a∈comparisonIncrementSupport V) (hbsupport : b∈comparisonIncrementSupport V)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport V) :
    Nonempty (ComparisonVirtualGapData g a b) := by
  have hTemp : 0 < T := G.hT
  have hmass : 0 < V ((a+b)/2) := comparison_increment_support_positive_cdf_after
    hV hnegative hasupport (by linarith)
  let c := V ((a+b)/2)/2
  let C := V ((a+b)/2)+1
  have hc : 0 < c := half_pos hmass
  have hC : 0 < C := by dsimp only [C];linarith
  have hB : 0 < B := (ha.trans_lt hab).trans hbB
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := G.xs_zero
  obtain ⟨KG,hKG,Hgradient⟩ := eventually_actual_history_high_gradient_uniform_above_mass_along_comparable_macro_of_full_thermal_original_q
    c B hc hB hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim M G Hfull W hcanonical w0 hw0 hWlower hWupper hcompare htotal hlarge g hG hg
  let f := fun t=>-2*T*g t
  have hf : IntegrableOn f (Icc a b) :=
    (((hg b (ha.trans_lt hab)).mono (fun t ht=>⟨ha.trans ht.1,ht.2⟩)).integrableOn_Icc).const_mul _
  have Hlocal : ∀s∈Ioo a b,∀t∈Ioo a b,s ≤ t →
      Tendsto (fun n=>∫r in Icc s t,|(M n).actualVirtualScaledGradient r-f r|) atTop (𝓝 0) := by
    intro s hs t ht hst
    rcases hst.eq_or_lt with rfl|hst
    · simp
    have Hmass := actual_compact_gap_mass_band_along_original_q dim M V hV hCDF hab hgap hmass hs ht
    exact (actual_selected_bad_history_high_radius_gradient_L1_along_comparable_macro_of_full_thermal_original_q
      c C s t hc hC (ha.trans hs.1.le) hst hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim M G Hfull W hcanonical w0 hw0 hWlower hWupper hcompare htotal Hmass hlarge g hG hg).2
  obtain ⟨K,hK,j,hj,hjbound,⟨P⟩⟩ := actual_virtual_gap_primitive_of_gradient_limit_along_original_q
    hdelta hcu.le hAz hC0 (by linarith) dim hdim M G hx V hV hCDF ha hab hbB
    hasupport hbsupport hgap hmass f hf ⟨KG,hKG.le,Hgradient⟩ Hlocal
  refine ⟨P.toGap (Or.inl ?_)⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hjpos : 0 < j t :=
    (div_pos zero_lt_one (sq_pos_of_pos (zero_lt_one.trans_le hK))).trans_le
      (hjbound t ⟨ht.1.le,ht.2.le⟩).1
  dsimp only [f]
  constructor
  · intro hgt
    exact mul_neg_of_pos_of_neg hjpos (mul_neg_of_neg_of_pos (by linarith) hgt)
  · intro hgt
    exact mul_pos hjpos (mul_pos_of_neg_of_neg (by linarith) hgt)

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_high_joint_scalar_limit_with_virtual_gaps_along_comparable_macro_of_full_thermal_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop) :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        ∃d : ActualOriginalQLocalScalarLimitData
          (G.hT) T
          (fun n=>M (phi n)) htotal,
          ∀a b : ℝ,0 ≤ a → a < b →
            a∈comparisonIncrementSupport d.V.mass → b∈comparisonIncrementSupport d.V.mass →
            (∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass) →
            Nonempty (ComparisonVirtualGapData
              (comparisonLocalScalarLimitResponse (G.hT)
                T d.beta d.U d.sigma) a b) := by
  have hTemp : 0 < T := G.hT
  obtain ⟨phi,hphi,htotal,⟨d⟩⟩ := exists_actual_selected_bad_history_high_joint_scalar_limit_along_comparable_macro_of_full_thermal_original_q
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G Hfull W hcanonical w0 hw0 hWlower hWupper
    hcompare hlarge
  refine ⟨phi,hphi,htotal,d,?_⟩
  intro a b ha hab hasupport hbsupport hgap
  let hT : 0<T := G.hT
  let g := comparisonLocalScalarLimitResponse hT T d.beta d.U d.sigma
  have hg : ∀R : ℝ,0<R → ContinuousOn g (Icc (0:ℝ) R) := by
    intro R hR
    have Hi : IntegrableOn
        (comparisonLocalScalarLimitSlope hT T d.beta d.U d.sigma) (uIcc (0:ℝ) R) := by
      simpa only [uIcc_of_le hR.le] using (d.limits R hR).1.integrableOn_Icc
    change ContinuousOn (fun r=>∫s in 0..r,
      comparisonLocalScalarLimitSlope hT T d.beta d.U d.sigma s) (Icc (0:ℝ) R)
    simpa only [uIcc_of_le hR.le] using intervalIntegral.continuousOn_primitive_interval Hi
  exact actual_selected_bad_history_high_virtual_gap_data_along_comparable_macro_of_full_thermal_original_q (B:=b+1)
    ha hab (by linarith) hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin
    (fun n=>dim (phi n)) (hdim.comp hphi.tendsto_atTop)
    (fun n=>M (phi n)) (G.comp_original_q phi hphi) (Hfull.comp hphi.tendsto_atTop) (fun n=>W (phi n)) (fun n=>hcanonical (phi n))
    w0 hw0 (hphi.tendsto_atTop.eventually hWlower) (hphi.tendsto_atTop.eventually hWupper) (fun n=>hcompare (phi n)) htotal
    (hlarge.comp hphi.tendsto_atTop) g (fun R hR=>(d.limits R hR).2.2) hg
    d.V.mass d.V.monotone d.radius_negative_axis_zero d.radius_inverse_cdf_limit
    hasupport hbsupport hgap

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_high_linear_profile_along_comparable_macro_of_full_thermal_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop) :
    ∃phi : ℕ→ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        ∃d : ActualOriginalQLocalScalarLimitData
          (G.hT) T
          (fun n=>M (phi n)) htotal,
          let kappa := (T/T)*scalarInitialDensityConstant
            (G.hT) d.beta
          (∀t>0,d.U.mass t=kappa*t) ∧ (∀t>0,d.V.mass t=kappa*t) ∧
            cl ≤ kappa ∧ kappa ≤ cu := by
  have hTemp : 0 < T := G.hT
  obtain ⟨phi,hphi,htotal,d,Hvirtual⟩ :=
    exists_actual_selected_bad_history_high_joint_scalar_limit_with_virtual_gaps_along_comparable_macro_of_full_thermal_original_q
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G Hfull W hcanonical w0 hw0 hWlower hWupper
      hcompare hlarge
  have Hlinear := d.global_profile_rigidity_of_HIGH_comparable_context
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    (hdim.comp hphi.tendsto_atTop) (G.comp_original_q phi hphi) (hlarge.comp hphi.tendsto_atTop) Hvirtual
  refine ⟨phi,hphi,htotal,d,Hlinear.1,Hlinear.2,?_⟩
  have hx : Tendsto (fun n=>(M (phi n)).xs) atTop (𝓝 0) :=
    (G.comp_original_q phi hphi).xs_zero
  let t := max Az 1
  have ht : 0 < t := zero_lt_one.trans_le (le_max_right _ _)
  have Hgrowth := d.radius_outer_growth hAz hx t (le_max_left _ _)
  rw [Hlinear.2 t ht] at Hgrowth
  exact ⟨le_of_mul_le_mul_right Hgrowth.1 ht,le_of_mul_le_mul_right Hgrowth.2 ht⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 16000000

theorem exists_actual_selected_bad_history_linear_profile_with_zero_scalar_limits_along_comparable_macro_of_full_thermal_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1 : ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs) :
    ∃phi : ℕ → ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0 : ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        ∃d : ActualOriginalQLocalScalarLimitData
          (G.hT) T
          (fun n => M (phi n)) htotal,
          let hT := G.hT
          let kappa := (T/T)*scalarInitialDensityConstant hT d.beta
          (∀t > 0,d.U.mass t=kappa*t) ∧ (∀t > 0,d.V.mass t=kappa*t) ∧
            cl ≤ kappa ∧ kappa ≤ cu ∧ d.sigma=0 ∧
            (∀t ≥ 0,comparisonLocalScalarLimitSlope hT T d.beta d.U d.sigma t=0) ∧
            (∀t ≥ 0,comparisonLocalScalarLimitResponse hT T d.beta d.U d.sigma t=0) ∧
            ∀R : ℝ,0 < R →
              TendstoUniformlyOn (fun n => comparisonLocalScalarSlope hT T
                ((M (phi n)).inheritedScalarMassProfileBare hT (htotal n)) (M (phi n)).xs)
                (fun _ => 0) atTop (Icc (0 : ℝ) R) ∧
              TendstoUniformlyOn (fun n => comparisonRescaledScalarResponse
                (scalarCovarianceResponse hT ((M (phi n)).inheritedScalarMassProfileBare hT (htotal n)))
                T (M (phi n)).xs) (fun _ => 0) atTop (Icc (0 : ℝ) R) := by
  have hTemp : 0 < T := G.hT
  have hlo : ∀ᶠn in atTop,w0 ≤ (M n).directTestWorkingScale := by
    simpa only [hcanonical] using hWlower
  have hlarge := actual_comparable_context_strength_ratio_atTop_of_working_scale_lower_original_q M G hw0 hlo
  obtain ⟨phi,hphi,htotal,d,Hlinear⟩ := exists_actual_selected_bad_history_high_linear_profile_along_comparable_macro_of_full_thermal_original_q
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G Hfull W hcanonical w0 hw0 hWlower hWupper hcompare hlarge
  have Hzero := d.scalar_primitives_zero_of_linear_profiles Hlinear.1 Hlinear.2.1
  exact ⟨phi,hphi,htotal,d,Hlinear.1,Hlinear.2.1,Hlinear.2.2.1,Hlinear.2.2.2,
    Hzero.1,Hzero.2.1,Hzero.2.2,
    d.compact_scalar_zero_limits_of_linear_profiles Hlinear.1 Hlinear.2.1⟩

end OAI.SKFluctuations.LaplaceWindowFormalization

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem exists_actual_selected_bad_history_complete_direct_profile_along_comparable_macro_of_full_thermal_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1 : ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (w0 : ℝ) (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ W n)
    (hWupper : ∀ᶠn in atTop,W n ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs) :
    ∃phi : ℕ → ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0 : ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        ∃d : ActualOriginalQLocalScalarLimitData
          (G.hT) T
          (fun n => M (phi n)) htotal,
          let hT := G.hT
          let kappa := (T/T)*scalarInitialDensityConstant hT d.beta
          (∀t > 0,d.U.mass t=kappa*t) ∧ (∀t > 0,d.V.mass t=kappa*t) ∧
            cl ≤ kappa ∧ kappa ≤ cu ∧
            2*T*Real.exp (-12*T) ≤ kappa ∧
            kappa ≤ T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) ∧
            TendstoLocallyUniformlyOn
              (fun n v=>(M (phi n)).sweepRadius ((M (phi n)).xs*v)/(M (phi n)).xs)
              (fun v=>v/kappa) atTop (Ioi (0:ℝ)) ∧ d.sigma=0 ∧
            (∀t ≥ 0,comparisonLocalScalarLimitSlope hT T d.beta d.U d.sigma t=0) ∧
            (∀t ≥ 0,comparisonLocalScalarLimitResponse hT T d.beta d.U d.sigma t=0) ∧
            ∀R : ℝ,0 < R →
              TendstoUniformlyOn (fun n => comparisonLocalScalarSlope hT T
                ((M (phi n)).inheritedScalarMassProfileBare hT (htotal n)) (M (phi n)).xs)
                (fun _ => 0) atTop (Icc (0 : ℝ) R) ∧
              TendstoUniformlyOn (fun n => comparisonRescaledScalarResponse
                (scalarCovarianceResponse hT ((M (phi n)).inheritedScalarMassProfileBare hT (htotal n)))
                T (M (phi n)).xs) (fun _ => 0) atTop (Icc (0 : ℝ) R) := by
  have hTemp : 0 < T := G.hT
  obtain ⟨phi,hphi,htotal,d,HU,HV,hklo,hkup,Hsigma,Hslope,Hresponse,Hlimits⟩ :=
    exists_actual_selected_bad_history_linear_profile_with_zero_scalar_limits_along_comparable_macro_of_full_thermal_original_q
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G Hfull W hcanonical w0 hw0 hWlower hWupper
      hcompare
  have Hdensity := comparison_local_scalar_initial_density_uniform_bounds
    (G.hT) hTemp.le d.beta
  exact ⟨phi,hphi,htotal,d,HU,HV,hklo,hkup,Hdensity.1,Hdensity.2,
    d.original_radius_locally_uniform_of_comparable_linear_profile hcl hklo (G.comp_original_q phi hphi) HV,
    Hsigma,Hslope,Hresponse,Hlimits⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
