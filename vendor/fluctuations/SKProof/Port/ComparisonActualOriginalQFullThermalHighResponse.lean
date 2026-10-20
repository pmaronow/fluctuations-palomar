module

public import SKProof.Port.ComparisonActualOriginalQPositiveBandHighWeighted
public import SKProof.Port.ComparisonActualOriginalQPositiveBareError
public import SKProof.Port.ComparisonActualOriginalQInitialCompactClock
public import SKProof.Port.ComparisonActualOriginalQNormalizedScalarGap
public import SKProof.Port.ComparisonActualOriginalQHighMassMismatchAlong
public import SKProof.Port.ComparisonActualOriginalQFullThermalGapIntegration
public import SKProof.Port.OriginalQHighOnlyBridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum ActualThetaZeroOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false

 theorem actual_comparable_context_macro_normalized_scalar_gap_of_full_thermal_original_q
    {m delta cl cu Az C0 Ct D Bclock T Cs w0 : ℝ}
    (C : ℝ) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hw0 : 0 < w0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hWlower : ∀ᶠn in atTop,w0 ≤ (M n).directTestWorkingScale)
    (hWupper : ∀ᶠn in atTop,(M n).directTestWorkingScale ≤ 1)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (A : ℕ→Set ParisiFinite.OrderPoint) (hA : ∀n,MeasurableSet (A n))
    (hcut : ∀n w,w∈A n → (w:ℝ) ≤ C*(M n).xs) :
    let nu:=fun n=>ENNReal.ofReal (1/(M n).xs) •
      (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict (A n)
    (∀n,Integrable (fun w : ParisiFinite.OrderPoint=>
      (M n).inheritedScalarCavityResidual G.hT (htotal n) w/(M n).xs^3) (nu n)) ∧
    Tendsto (fun n=>∫w : ParisiFinite.OrderPoint,
      |(M n).inheritedScalarCavityResidual G.hT (htotal n) w/(M n).xs^3|∂nu n) atTop (𝓝 0) := by
  obtain ⟨eta,heta,Heta,Hgap⟩:=
    actual_comparable_context_original_scalar_gap_integral_of_full_thermal_original_q
      C hC hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G Hfull
  let v:=fun n=>min (C*(M n).xs) 1
  have hv n : v n∈Icc (0:ℝ) 1:=
    ⟨le_min (mul_nonneg hC.le (M n).hxs.le) zero_le_one,min_le_right _ _⟩
  have Hzero:=actual_original_scalar_gap_normalized_l1_tendsto_zero_along_original_q
    G.hT hC eta Heta M htotal G.xs_zero Hgap v hv
    (Eventually.of_forall (fun n=>min_le_left _ _))
  let nu:=fun n=>ENNReal.ofReal (1/(M n).xs) •
    (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict (A n)
  have hnu n : nu n ≤ comparisonNormalizedClockMass (M n).xs (v n) := by
    intro s
    change (ENNReal.ofReal (1/(M n).xs) •
      (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict (A n)) s ≤
      (ENNReal.ofReal (1/(M n).xs) •
        (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v n}) s
    rw [Measure.smul_apply,Measure.smul_apply]
    exact mul_le_mul le_rfl ((Measure.restrict_mono
      (fun w hw=>le_min (hcut n w hw) w.property.2) le_rfl) s) zero_le zero_le
  refine ⟨fun n=>(Hzero.1 n).mono_measure (hnu n),?_⟩
  apply squeeze_zero (fun n=>integral_nonneg (fun _=>abs_nonneg _)) _ Hzero.2
  intro n
  exact integral_mono_measure (hnu n) (ae_of_all _ (fun _=>abs_nonneg _)) (Hzero.1 n).abs

 theorem actual_comparable_context_positive_band_HIGH_response_of_full_thermal_original_q
    {m delta cl cu Az C0 Ct D Bclock T Ccal w0 : ℝ}
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : OriginalQComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).sweepBf (M n).sweepHf u-
        (orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ (M n).directTestWorkingScale)
    (hWupper : ∀ᶠn in atTop,(M n).directTestWorkingScale ≤ 1)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (A : ℕ→Set ParisiFinite.OrderPoint) (hA : ∀n,MeasurableSet (A n))
    (hband : ∀n w,w∈A n → c*(M n).xs ≤ (w:ℝ) ∧ (w:ℝ) ≤ C*(M n).xs)
    (g : ℝ→ℝ)
    (hG : ∀Rclock > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse G.hT ((M n).inheritedScalarMassProfileBare G.hT (htotal n)))
      T (M n).xs) g atTop (Icc (0:ℝ) Rclock))
    (hg : ∀Rclock > 0,ContinuousOn g (Icc (0:ℝ) Rclock)) :
    let nu:=fun n=>ENNReal.ofReal (1/(M n).xs) •
      (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict (A n)
    let Gamma:=fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse G.hT ((M n).inheritedScalarMassProfileBare G.hT (htotal n)))
      T (M n).xs
    let q:=fun n (w : ParisiFinite.OrderPoint)=>
      actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf w/(T*(M n).xs)
    (∀n,Integrable (fun w=>Gamma n (q n w)) (nu n)) ∧
      Tendsto (fun n=>∫w,|Gamma n (q n w)|∂nu n) atTop (𝓝 0) ∧
    (∀n,Integrable (fun w=>q n w-(M n).sweepRadius w/(M n).xs) (nu n)) ∧
      Tendsto (fun n=>∫w,|q n w-(M n).sweepRadius w/(M n).xs|∂nu n) atTop (𝓝 0) := by
  let v:=fun n=>min (C*(M n).xs) 1
  have hv n : v n∈Icc (0:ℝ) 1:=
    ⟨le_min (mul_nonneg hC.le (M n).hxs.le) zero_le_one,min_le_right _ _⟩
  have hvc n : v n ≤ C*(M n).xs:=min_le_left _ _
  have hsub n : A n ⊆ {w : ParisiFinite.OrderPoint | (w:ℝ) ≤ v n}:=
    fun w hw=>le_min (hband n w hw).2 w.property.2
  have Hcav:=actual_comparable_context_macro_normalized_scalar_gap_of_full_thermal_original_q C hC hm hdelta hroom
    hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hw0 dim hdim M G Hfull hsmall hWlower hWupper
    htotal A hA (fun n w hw=>(hband n w hw).2)
  have Hbare:=G.positive_band_bare_error hm hdelta hroom hcl hcu hAz hC0 hCt hdim A hA
    c C hc hC hband
  obtain ⟨Rclock,hRclock,Hrange⟩:=actual_initial_compact_clock_range_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G G.xs_zero G.hT G.hT htotal C hC
    (by simpa only [one_mul] using G.initial_field_clock_original_q C 1 hC zero_lt_one)
  have HrangeA : ∀ᶠn in atTop,∀w : ParisiFinite.OrderPoint,w∈A n →
      actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf w/(T*(M n).xs)∈Icc (0:ℝ) Rclock := by
    filter_upwards [Hrange] with n hn w hw
    exact hn w (hband n w hw).2
  have Hweighted:=actual_high_strength_positive_band_weighted_mass_tendsto_zero_along
    hdelta hcl hAz hC0 (by linarith only [hm,hdelta]) dim hdim M G hlarge C hC.le v hv hvc
    A hA hsub G.hT G.hT htotal Hcav.2 Hbare.2
    Rclock HrangeA g (hG Rclock hRclock) (hg Rclock hRclock)
  let mu:=fun n=>(uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict (A n)
  let nu:=fun n=>ENNReal.ofReal (1/(M n).xs) • mu n
  let S:=fun n (w : ParisiFinite.OrderPoint)=>orderedPathS (dim n+1) (M n).sweepBf (M n).sweepHf w
  let rad:=fun n (w : ParisiFinite.OrderPoint)=>(M n).sweepRadius w
  let e:=fun n (w : ParisiFinite.OrderPoint)=>(M n).sweepCoefficient w
  let Gamma:=fun n=>scalarCovarianceResponse G.hT ((M n).inheritedScalarMassProfileBare G.hT (htotal n))
  let h0:=fun n (w : ParisiFinite.OrderPoint)=>(M n).h w
  let b0:=fun n (w : ParisiFinite.OrderPoint)=>(M n).b w
  have Hmixed n (w : ParisiFinite.OrderPoint) : comparisonScalarMassClockOn h0 b0 e S rad n w=
      actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf w :=
    ((M n).inherited_mixed_clock_eq_nativeScalarClock w.property).symm
  have Hcav' n : Integrable (fun w=>(S n w-Gamma n (comparisonScalarMassClockOn h0 b0 e S rad n w))/(M n).xs^3) (nu n) := by
    simp_rw [Hmixed];exact Hcav.1 n
  have Hcav0' : Tendsto (fun n=>∫w,|(S n w-Gamma n (comparisonScalarMassClockOn h0 b0 e S rad n w))/(M n).xs^3|∂nu n) atTop (𝓝 0) := by
    simp_rw [Hmixed];exact Hcav.2
  have Hresponse:=comparison_scalar_mass_response_L1_tendsto_on nu Gamma h0 b0 e S rad
    (fun n=>(M n).xs) G.hT (fun n=>(M n).hxs.ne') Hweighted.1 Hcav' Hbare.1
    Hweighted.2 Hcav0' Hbare.2
  have Hsquare:=actual_HIGH_original_retained_squared_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G hlarge v C hC hv hvc
  have hmu n : mu n ≤ (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict
      {w : ParisiFinite.OrderPoint | (w:ℝ) ≤ v n}:=
    Measure.restrict_mono (hsub n) le_rfl
  have hi n : Integrable (fun w=>S n w-rad n w) (mu n):=
    (((M n).original_retained_mismatch_integrable (v n)).1).mono_measure (hmu n)
  have hi2 n : Integrable (fun w=>(S n w-rad n w)^2) (mu n):=
    (((M n).original_retained_mismatch_integrable (v n)).2).mono_measure (hmu n)
  have HsquareA : Tendsto (fun n=>(∫w,(S n w-rad n w)^2∂mu n)/(M n).xs^3) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>div_nonneg (integral_nonneg (fun _=>sq_nonneg _)) (pow_nonneg (M n).hxs.le _)) _ Hsquare
    intro n
    exact div_le_div_of_nonneg_right (integral_mono_measure (hmu n)
      (ae_of_all _ (fun _=>sq_nonneg _)) ((M n).original_retained_mismatch_integrable (v n)).2)
      (pow_nonneg (M n).hxs.le _)
  have hmass n : (mu n).real univ ≤ C*(M n).xs := by
    rw [measureReal_restrict_apply' (hA n),univ_inter]
    exact (measureReal_mono (μ:=(uniformOrderMass : Measure ParisiFinite.OrderPoint)) (hsub n)).trans
      ((uniformOrderMass_atMost (hv n)).le.trans (hvc n))
  have Hspin0:=comparison_original_mass_normalized_L1_tendsto mu (fun _=>inferInstance)
    (fun n w=>S n w-rad n w) (fun n=>(M n).xs) (fun n=>(M n).hxs) hC.le
    hi hi2 hmass HsquareA
  have Hspin n : Integrable (fun w=>S n w/(M n).xs-rad n w/(M n).xs) (nu n) := by
    simpa only [sub_div,nu] using ((hi n).smul_measure ENNReal.ofReal_ne_top).div_const (M n).xs
  have Hspin0' : Tendsto (fun n=>∫w,|S n w/(M n).xs-rad n w/(M n).xs|∂nu n) atTop (𝓝 0) := by
    simpa only [sub_div,nu,mu] using Hspin0
  have HclockRate:=comparison_scalar_mass_clock_L1_tendsto_on nu h0 b0 e S rad (fun n=>(M n).xs)
    G.hT (fun n=>(M n).hxs.ne') G.xs_zero Hspin Hweighted.1 Hbare.1
    Hspin0' Hweighted.2 Hbare.2
  simp_rw [Hmixed] at Hresponse HclockRate
  exact ⟨Hresponse.1,Hresponse.2,HclockRate.1,HclockRate.2⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
