module

public import ComparisonNativeActualComparableBandShrinkingResponse
public import ComparisonActualHighOnlyComparableBandCavityBackend
public import ComparisonActualHighOnlyFullThermalFullHighResponse
public import ComparisonActualHighOnlyBoundedStrengthScalarResponse
public import ComparisonActualHighOnlyComparableBandCoupling
public import ComparisonActualHighOnlyCalibratedMassBand
public import ComparisonActualHighOnlyNormalizedScalarGap

@[expose] public section
set_option autoImplicit false

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum ActualHighOnlyOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false

 theorem actual_comparable_context_shrinking_normalized_scalar_gap_high_only
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (C : ℝ) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
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
    exists_actual_selected_bad_history_original_scalar_gap_integral_along_comparable_context_high_only
      C hC hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare
  let v:=fun n=>min (C*(M n).xs) 1
  have hv n : v n∈Icc (0:ℝ) 1:=
    ⟨le_min (mul_nonneg hC.le (M n).hxs.le) zero_le_one,min_le_right _ _⟩
  have Hzero:=actual_original_scalar_gap_normalized_l1_tendsto_zero_along_high_only
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

 theorem actual_comparable_context_shrinking_positive_HIGH_response_high_only
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (A : ℕ→Set ParisiFinite.OrderPoint) (hA : ∀n,MeasurableSet (A n))
    (hband : ∀n w,w∈A n → c*(M n).xs ≤ (w:ℝ) ∧ (w:ℝ) ≤ C*(M n).xs)
    (g : ℝ→ℝ)
    (hG : ∀Rclock > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse G.hT ((M n).inheritedScalarMassProfile G.hT (htotal n)))
      T (M n).xs) g atTop (Icc (0:ℝ) Rclock))
    (hg : ∀Rclock > 0,ContinuousOn g (Icc (0:ℝ) Rclock)) :
    let nu:=fun n=>ENNReal.ofReal (1/(M n).xs) •
      (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict (A n)
    let Gamma:=fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse G.hT ((M n).inheritedScalarMassProfile G.hT (htotal n)))
      T (M n).xs
    let q:=fun n (w : ParisiFinite.OrderPoint)=>
      actualMixedClock (dim n+1) (M n).bf (M n).hf w/(T*(M n).xs)
    (∀n,Integrable (fun w=>Gamma n (q n w)) (nu n)) ∧
      Tendsto (fun n=>∫w,|Gamma n (q n w)|∂nu n) atTop (𝓝 0) ∧
    (∀n,Integrable (fun w=>q n w-(M n).R w/(M n).xs) (nu n)) ∧
      Tendsto (fun n=>∫w,|q n w-(M n).R w/(M n).xs|∂nu n) atTop (𝓝 0) := by
  let v:=fun n=>min (C*(M n).xs) 1
  have hv n : v n∈Icc (0:ℝ) 1:=
    ⟨le_min (mul_nonneg hC.le (M n).hxs.le) zero_le_one,min_le_right _ _⟩
  have hvc n : v n ≤ C*(M n).xs:=min_le_left _ _
  have hsub n : A n ⊆ {w : ParisiFinite.OrderPoint | (w:ℝ) ≤ v n}:=
    fun w hw=>le_min (hband n w hw).2 w.property.2
  have Hcav:=actual_comparable_context_shrinking_normalized_scalar_gap_high_only C hC hm hdelta hroom
    hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare
    htotal A hA (fun n w hw=>(hband n w hw).2)
  have Hbare:=G.positive_band_bare_error hm hdelta hroom hcl hcu hAz hC0 hCt hdim A hA
    c C hc hC hband
  obtain ⟨Rclock,hRclock,Hrange⟩:=actual_initial_compact_clock_range_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G G.xs_zero G.hT G.hT htotal C hC
    (by simpa only [one_mul] using G.initial_field_clock C 1 hC zero_lt_one)
  have HrangeA : ∀ᶠn in atTop,∀w : ParisiFinite.OrderPoint,w∈A n →
      actualMixedClock (dim n+1) (M n).bf (M n).hf w/(T*(M n).xs)∈Icc (0:ℝ) Rclock := by
    filter_upwards [Hrange] with n hn w hw
    exact hn w (hband n w hw).2
  have Hweighted:=actual_high_strength_positive_band_weighted_mass_tendsto_zero_along
    hdelta hcl hAz hC0 (by linarith only [hm,hdelta]) dim hdim M G hlarge C hC.le v hv hvc
    A hA hsub G.hT G.hT htotal Hcav.2 Hbare.2
    Rclock HrangeA g (hG Rclock hRclock) (hg Rclock hRclock)
  let mu:=fun n=>(uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict (A n)
  let nu:=fun n=>ENNReal.ofReal (1/(M n).xs) • mu n
  let S:=fun n (w : ParisiFinite.OrderPoint)=>orderedPathS (dim n+1) (M n).bf (M n).hf w
  let rad:=fun n (w : ParisiFinite.OrderPoint)=>(M n).R w
  let e:=fun n (w : ParisiFinite.OrderPoint)=>(M n).coefficient w
  let Gamma:=fun n=>scalarCovarianceResponse G.hT ((M n).inheritedScalarMassProfile G.hT (htotal n))
  let h0:=fun n (w : ParisiFinite.OrderPoint)=>(M n).h w
  let b0:=fun n (w : ParisiFinite.OrderPoint)=>(M n).b w
  have Hmixed n (w : ParisiFinite.OrderPoint) : comparisonScalarMassClockOn h0 b0 e S rad n w=
      actualMixedClock (dim n+1) (M n).bf (M n).hf w :=
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

 theorem actual_comparable_context_shrinking_positive_bounded_response_high_only
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (K : ℝ) (hK : 0 ≤ K)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (A : ℕ→Set ParisiFinite.OrderPoint) (hA : ∀n,MeasurableSet (A n))
    (hband : ∀n w,w∈A n → c*(M n).xs ≤ (w:ℝ) ∧ (w:ℝ) ≤ C*(M n).xs)
 :
    let nu:=fun n=>ENNReal.ofReal (1/(M n).xs) •
      (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict (A n)
    let Gamma:=fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse G.hT ((M n).inheritedScalarMassProfile G.hT (htotal n)))
      T (M n).xs
    let q:=fun n (w : ParisiFinite.OrderPoint)=>
      actualMixedClock (dim n+1) (M n).bf (M n).hf w/(T*(M n).xs)
    (∀n,Integrable (fun w=>Gamma n (q n w)) (nu n)) ∧
      Tendsto (fun n=>∫w,|Gamma n (q n w)|∂nu n) atTop (𝓝 0) ∧
    (∀n,Integrable (fun w=>q n w-(M n).R w/(M n).xs) (nu n)) ∧
      Tendsto (fun n=>∫w,|q n w-(M n).R w/(M n).xs|∂nu n) atTop (𝓝 0) := by
  have Hcav:=actual_comparable_context_shrinking_normalized_scalar_gap_high_only C hC hm hdelta hroom
    hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare
    htotal A hA (fun n w hw=>(hband n w hw).2)
  have Hbare : ∀eps > 0,∀ᶠn in atTop,∀w : ParisiFinite.OrderPoint,w∈A n →
      |(M n).b w-T| ≤ eps*(M n).xs^2 ∧ |(M n).h w| ≤ eps*(M n).xs^3 := by
    intro eps heps
    filter_upwards [G.positive_band_clocks c C eps hc hC.le heps] with n hn w hw
    exact hn w ⟨(hband n w hw).1,le_min (hband n w hw).2 w.property.2⟩
  exact actual_inherited_local_temperature_restricted_response_tendsto_zero_along_high_only
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G (fun n=>(M n).xs)
    (fun _=>le_rfl) G.xs_zero G.pullback G.hT G.hT htotal A hA C K hC hK
    (fun n w hw=>(hband n w hw).2) hwork Hbare Hcav.1 Hcav.2

 theorem actual_comparable_context_shrinking_full_HIGH_response_high_only
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (C : ℝ) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (v : ℕ→ℝ) (hv : ∀n,v n∈Icc (0:ℝ) 1) (hvc : ∀n,v n ≤ C*(M n).xs)
    (g : ℝ→ℝ)
    (hG : ∀Rclock > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse G.hT ((M n).inheritedScalarMassProfile G.hT (htotal n)))
      T (M n).xs) g atTop (Icc (0:ℝ) Rclock))
    (hg : ∀Rclock > 0,ContinuousOn g (Icc (0:ℝ) Rclock)) :
    let nu:=fun n=>comparisonNormalizedClockMass (M n).xs (v n)
    let Gamma:=fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse G.hT ((M n).inheritedScalarMassProfile G.hT (htotal n)))
      T (M n).xs
    let q:=fun n (w : ParisiFinite.OrderPoint)=>
      actualMixedClock (dim n+1) (M n).bf (M n).hf w/(T*(M n).xs)
    (∀n,Integrable (fun w=>Gamma n (q n w)) (nu n)) ∧
      Tendsto (fun n=>∫w,|Gamma n (q n w)|∂nu n) atTop (𝓝 0) ∧
    (∀n,Integrable (fun w=>q n w-(M n).R w/(M n).xs) (nu n)) ∧
      Tendsto (fun n=>∫w,|q n w-(M n).R w/(M n).xs|∂nu n) atTop (𝓝 0) := by
  let nu:=fun n=>comparisonNormalizedClockMass (M n).xs (v n)
  let Gamma:=fun n=>scalarCovarianceResponse G.hT ((M n).inheritedScalarMassProfile G.hT (htotal n))
  let response:=fun n=>comparisonRescaledScalarResponse (Gamma n) T (M n).xs
  let q:=fun n (w : ParisiFinite.OrderPoint)=>actualMixedClock (dim n+1) (M n).bf (M n).hf w/(T*(M n).xs)
  let S:=fun n (w : ParisiFinite.OrderPoint)=>orderedPathS (dim n+1) (M n).bf (M n).hf w
  let rad:=fun n (w : ParisiFinite.OrderPoint)=>(M n).R w
  let e:=fun n (w : ParisiFinite.OrderPoint)=>(M n).coefficient w
  let h0:=fun n (w : ParisiFinite.OrderPoint)=>(M n).h w
  let b0:=fun n (w : ParisiFinite.OrderPoint)=>(M n).b w
  have Hmixed n (w : ParisiFinite.OrderPoint) : comparisonScalarMassClockOn h0 b0 e S rad n w=
      actualMixedClock (dim n+1) (M n).bf (M n).hf w :=
    ((M n).inherited_mixed_clock_eq_nativeScalarClock w.property).symm
  have hiWeighted n : Integrable (fun w=>e n w*(S n w-rad n w)/(M n).xs^3) (nu n):=
    (M n).original_weighted_mismatch_integrable _ _
  have hiBare n : Integrable (fun w=>((b0 n w-T)*S n w+h0 n w)/(M n).xs^3) (nu n):=
    (M n).inherited_bare_residual_integrable (T:=T) _ _
  have hiCavity n : Integrable (fun w=>(S n w-Gamma n
      (comparisonScalarMassClockOn h0 b0 e S rad n w))/(M n).xs^3) (nu n) := by
    simp_rw [Hmixed]
    exact (M n).inherited_scalar_cavity_residual_normalized_integrable G.hT (htotal n) _ _
  have hiResponse n : Integrable (fun w=>response n (q n w)) (nu n) := by
    have H:=(((hiWeighted n).div_const T).sub (hiCavity n)).sub ((hiBare n).div_const T)
    apply H.congr
    exact Eventually.of_forall (fun w=>by
      have HH:=comparison_scalar_mass_response_exact_on Gamma h0 b0 e S rad
        (fun n=>(M n).xs) G.hT.ne' (fun n=>(M n).hxs.ne') n w
      rw [Hmixed] at HH
      simpa only [Pi.sub_apply,Pi.add_apply,Hmixed] using HH.symm)
  have hiSpin n : Integrable (fun w=>S n w/(M n).xs-rad n w/(M n).xs) (nu n) := by
    simpa only [sub_div,nu,comparisonNormalizedClockMass] using
      ((((M n).original_retained_mismatch_integrable (v n)).1).smul_measure ENNReal.ofReal_ne_top).div_const (M n).xs
  have hiClock n : Integrable (fun w=>q n w-rad n w/(M n).xs) (nu n) := by
    have H:=(hiSpin n).add (((hiBare n).sub (hiWeighted n)).const_mul ((M n).xs^2/T))
    apply H.congr
    exact Eventually.of_forall (fun w=>by
      have HH:=comparison_scalar_mass_clock_exact_on h0 b0 e S rad
        (fun n=>(M n).xs) G.hT.ne' (fun n=>(M n).hxs.ne') n w
      rw [Hmixed] at HH
      simpa only [Pi.sub_apply,Pi.add_apply,Hmixed] using HH.symm)
  let L:=fun c n=>{w : ParisiFinite.OrderPoint | (w:ℝ)<c*(M n).xs}
  have hL c n : MeasurableSet (L c n):=measurableSet_lt measurable_subtype_coe measurable_const
  have hmass c (hc : 0<c) n : (nu n).real (L c n) ≤ c:=
    normalized_clock_mass_low_prefix_le (M n).hxs hc
  have Hpositive (c : ℝ) (hc : 0 < c) :=
    actual_comparable_context_shrinking_positive_HIGH_response_high_only c C hc hC hm hdelta hroom hcl hcu hAz hC0 hCt
      hCcal hc0 hc01 hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare hlarge htotal
      (fun n=>positiveOriginalMassBand (M n).xs (v n) c)
      (fun n=>positiveOriginalMassBand_measurable _ _ _)
      (fun n w hw=>⟨hw.1,hw.2.trans (hvc n)⟩) g hG hg
  have HpositiveResponse c (hc : 0<c) : Tendsto (fun n=>∫w in (L c n)ᶜ,
      |response n (q n w)|∂nu n) atTop (𝓝 0) := by
    simpa only [nu,L,normalized_clock_mass_restrict_positive_band] using (Hpositive c hc).2.1
  have HpositiveClock c (hc : 0<c) : Tendsto (fun n=>∫w in (L c n)ᶜ,
      |q n w-rad n w/(M n).xs|∂nu n) atTop (𝓝 0) := by
    simpa only [nu,L,normalized_clock_mass_restrict_positive_band] using (Hpositive c hc).2.2.2
  obtain ⟨Rclock,hRclock,Hrange⟩:=actual_initial_compact_clock_range_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G G.xs_zero G.hT G.hT htotal C hC
    (by simpa only [one_mul] using G.initial_field_clock C 1 hC zero_lt_one)
  obtain ⟨Bg,hBg⟩:=isCompact_Icc.bddAbove_image (hg Rclock hRclock).abs
  let B:=max 0 Bg+1
  have hB : 0 ≤ B:=by dsimp only [B];positivity
  have HresponseUniform:=(Metric.tendstoUniformlyOn_iff.mp (hG Rclock hRclock)) 1 zero_lt_one
  have HboundResponse : ∀ᶠn in atTop,∀ᵐw∂nu n,|response n (q n w)| ≤ B := by
    filter_upwards [Hrange,HresponseUniform] with n hnRange hnUniform
    have HH : ∀ᵐw∂(uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v n},
        |response n (q n w)| ≤ B := by
      filter_upwards [ae_restrict_mem (measurableSet_le measurable_subtype_coe measurable_const)] with w hw
      have hq : q n w∈Icc (0:ℝ) Rclock:=hnRange w (hw.trans (hvc n))
      have Hg : |g (q n w)| ≤ Bg:=hBg (mem_image_of_mem _ hq)
      have Hdist : |g (q n w)-response n (q n w)|<1 := by
        simpa only [Real.dist_eq] using hnUniform _ hq
      have Habs:=abs_add_le (response n (q n w)-g (q n w)) (g (q n w))
      rw [sub_add_cancel,abs_sub_comm] at Habs
      dsimp only [B]
      linarith [le_max_right 0 Bg]
    rw [ae_iff] at HH ⊢
    change (ENNReal.ofReal (1/(M n).xs) •
      (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v n}) _=0
    rw [Measure.smul_apply,HH,smul_zero]
  let Cr:=(Az+1/cl)*(1+C)
  have hCr : 0 ≤ Cr:=by dsimp only [Cr];positivity
  have HboundClock : ∀ᶠn in atTop,∀ᵐw∂nu n,|q n w-rad n w/(M n).xs| ≤ Rclock+Cr := by
    filter_upwards [Hrange] with n hnRange
    have HH : ∀ᵐw∂(uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v n},
        |q n w-rad n w/(M n).xs| ≤ Rclock+Cr := by
      filter_upwards [ae_restrict_mem (measurableSet_le measurable_subtype_coe measurable_const)] with w hw
      have hq : q n w∈Icc (0:ℝ) Rclock:=hnRange w (hw.trans (hvc n))
      have hr0 : 0 ≤ rad n w:=
        (omittedSweepQuantile_bounds zero_le_one ⟨(M n).data.hs.1,(M n).data.hs1⟩ (M n).context.hc (M n).context.hk (M n).context.hkc
          (M n).context.hm (M n).context.hM (M n).alpha w).1
      have hr : rad n w/(M n).xs ≤ Cr := by
        have H:=(M n).inverse_radius_le_source_mass hcl hAz w.property
        have HH:=mul_le_mul_of_nonneg_left
          (show (M n).xs+(w:ℝ) ≤ (1+C)*(M n).xs by linarith [hw.trans (hvc n)])
          (show 0 ≤ Az+1/cl by positivity)
        apply (div_le_iff₀ (M n).hxs).mpr
        dsimp only [Cr]
        nlinarith only [H,HH]
      have Habs:=abs_sub_le (q n w) 0 (rad n w/(M n).xs)
      simp only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hq.1,
        abs_of_nonneg (div_nonneg hr0 (M n).hxs.le)] at Habs
      linarith only [Habs,hq.2,hr]
    rw [ae_iff] at HH ⊢
    change (ENNReal.ofReal (1/(M n).xs) •
      (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v n}) _=0
    rw [Measure.smul_apply,HH,smul_zero]
  have Hresponse:=bounded_integral_tendsto_zero_of_positive_cut nu
    (fun n w=>response n (q n w)) hiResponse L hL B hB HboundResponse hmass HpositiveResponse
  have Hclock:=bounded_integral_tendsto_zero_of_positive_cut nu
    (fun n w=>q n w-rad n w/(M n).xs) hiClock L hL (Rclock+Cr)
    (add_nonneg hRclock.le hCr) HboundClock hmass HpositiveClock
  exact ⟨hiResponse,Hresponse,hiClock,Hclock⟩

 theorem actual_comparable_context_shrinking_full_bounded_response_high_only
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (C : ℝ) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (K : ℝ) (hK : 0 ≤ K)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (v : ℕ→ℝ) (hv : ∀n,v n∈Icc (0:ℝ) 1) (hvc : ∀n,v n ≤ C*(M n).xs)
    (g : ℝ→ℝ)
    (hG : ∀Rclock > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse G.hT ((M n).inheritedScalarMassProfile G.hT (htotal n)))
      T (M n).xs) g atTop (Icc (0:ℝ) Rclock))
    (hg : ∀Rclock > 0,ContinuousOn g (Icc (0:ℝ) Rclock)) :
    let nu:=fun n=>comparisonNormalizedClockMass (M n).xs (v n)
    let Gamma:=fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse G.hT ((M n).inheritedScalarMassProfile G.hT (htotal n)))
      T (M n).xs
    let q:=fun n (w : ParisiFinite.OrderPoint)=>
      actualMixedClock (dim n+1) (M n).bf (M n).hf w/(T*(M n).xs)
    (∀n,Integrable (fun w=>Gamma n (q n w)) (nu n)) ∧
      Tendsto (fun n=>∫w,|Gamma n (q n w)|∂nu n) atTop (𝓝 0) ∧
    (∀n,Integrable (fun w=>q n w-(M n).R w/(M n).xs) (nu n)) ∧
      Tendsto (fun n=>∫w,|q n w-(M n).R w/(M n).xs|∂nu n) atTop (𝓝 0) := by
  let nu:=fun n=>comparisonNormalizedClockMass (M n).xs (v n)
  let Gamma:=fun n=>scalarCovarianceResponse G.hT ((M n).inheritedScalarMassProfile G.hT (htotal n))
  let response:=fun n=>comparisonRescaledScalarResponse (Gamma n) T (M n).xs
  let q:=fun n (w : ParisiFinite.OrderPoint)=>actualMixedClock (dim n+1) (M n).bf (M n).hf w/(T*(M n).xs)
  let S:=fun n (w : ParisiFinite.OrderPoint)=>orderedPathS (dim n+1) (M n).bf (M n).hf w
  let rad:=fun n (w : ParisiFinite.OrderPoint)=>(M n).R w
  let e:=fun n (w : ParisiFinite.OrderPoint)=>(M n).coefficient w
  let h0:=fun n (w : ParisiFinite.OrderPoint)=>(M n).h w
  let b0:=fun n (w : ParisiFinite.OrderPoint)=>(M n).b w
  have Hmixed n (w : ParisiFinite.OrderPoint) : comparisonScalarMassClockOn h0 b0 e S rad n w=
      actualMixedClock (dim n+1) (M n).bf (M n).hf w :=
    ((M n).inherited_mixed_clock_eq_nativeScalarClock w.property).symm
  have hiWeighted n : Integrable (fun w=>e n w*(S n w-rad n w)/(M n).xs^3) (nu n):=
    (M n).original_weighted_mismatch_integrable _ _
  have hiBare n : Integrable (fun w=>((b0 n w-T)*S n w+h0 n w)/(M n).xs^3) (nu n):=
    (M n).inherited_bare_residual_integrable (T:=T) _ _
  have hiCavity n : Integrable (fun w=>(S n w-Gamma n
      (comparisonScalarMassClockOn h0 b0 e S rad n w))/(M n).xs^3) (nu n) := by
    simp_rw [Hmixed]
    exact (M n).inherited_scalar_cavity_residual_normalized_integrable G.hT (htotal n) _ _
  have hiResponse n : Integrable (fun w=>response n (q n w)) (nu n) := by
    have H:=(((hiWeighted n).div_const T).sub (hiCavity n)).sub ((hiBare n).div_const T)
    apply H.congr
    exact Eventually.of_forall (fun w=>by
      have HH:=comparison_scalar_mass_response_exact_on Gamma h0 b0 e S rad
        (fun n=>(M n).xs) G.hT.ne' (fun n=>(M n).hxs.ne') n w
      rw [Hmixed] at HH
      simpa only [Pi.sub_apply,Pi.add_apply,Hmixed] using HH.symm)
  have hiSpin n : Integrable (fun w=>S n w/(M n).xs-rad n w/(M n).xs) (nu n) := by
    simpa only [sub_div,nu,comparisonNormalizedClockMass] using
      ((((M n).original_retained_mismatch_integrable (v n)).1).smul_measure ENNReal.ofReal_ne_top).div_const (M n).xs
  have hiClock n : Integrable (fun w=>q n w-rad n w/(M n).xs) (nu n) := by
    have H:=(hiSpin n).add (((hiBare n).sub (hiWeighted n)).const_mul ((M n).xs^2/T))
    apply H.congr
    exact Eventually.of_forall (fun w=>by
      have HH:=comparison_scalar_mass_clock_exact_on h0 b0 e S rad
        (fun n=>(M n).xs) G.hT.ne' (fun n=>(M n).hxs.ne') n w
      rw [Hmixed] at HH
      simpa only [Pi.sub_apply,Pi.add_apply,Hmixed] using HH.symm)
  let L:=fun c n=>{w : ParisiFinite.OrderPoint | (w:ℝ)<c*(M n).xs}
  have hL c n : MeasurableSet (L c n):=measurableSet_lt measurable_subtype_coe measurable_const
  have hmass c (hc : 0<c) n : (nu n).real (L c n) ≤ c:=
    normalized_clock_mass_low_prefix_le (M n).hxs hc
  have Hpositive (c : ℝ) (hc : 0 < c) :=
    actual_comparable_context_shrinking_positive_bounded_response_high_only c C hc hC hm hdelta hroom hcl hcu hAz hC0 hCt
      hCcal hc0 hc01 hmargin hcapmargin hgapmargin dim hdim M G W hcanonical hWlim hcompare K hK hwork htotal
      (fun n=>positiveOriginalMassBand (M n).xs (v n) c)
      (fun n=>positiveOriginalMassBand_measurable _ _ _)
      (fun n w hw=>⟨hw.1,hw.2.trans (hvc n)⟩)
  have HpositiveResponse c (hc : 0<c) : Tendsto (fun n=>∫w in (L c n)ᶜ,
      |response n (q n w)|∂nu n) atTop (𝓝 0) := by
    simpa only [nu,L,normalized_clock_mass_restrict_positive_band] using (Hpositive c hc).2.1
  have HpositiveClock c (hc : 0<c) : Tendsto (fun n=>∫w in (L c n)ᶜ,
      |q n w-rad n w/(M n).xs|∂nu n) atTop (𝓝 0) := by
    simpa only [nu,L,normalized_clock_mass_restrict_positive_band] using (Hpositive c hc).2.2.2
  obtain ⟨Rclock,hRclock,Hrange⟩:=actual_initial_compact_clock_range_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G G.xs_zero G.hT G.hT htotal C hC
    (by simpa only [one_mul] using G.initial_field_clock C 1 hC zero_lt_one)
  obtain ⟨Bg,hBg⟩:=isCompact_Icc.bddAbove_image (hg Rclock hRclock).abs
  let B:=max 0 Bg+1
  have hB : 0 ≤ B:=by dsimp only [B];positivity
  have HresponseUniform:=(Metric.tendstoUniformlyOn_iff.mp (hG Rclock hRclock)) 1 zero_lt_one
  have HboundResponse : ∀ᶠn in atTop,∀ᵐw∂nu n,|response n (q n w)| ≤ B := by
    filter_upwards [Hrange,HresponseUniform] with n hnRange hnUniform
    have HH : ∀ᵐw∂(uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v n},
        |response n (q n w)| ≤ B := by
      filter_upwards [ae_restrict_mem (measurableSet_le measurable_subtype_coe measurable_const)] with w hw
      have hq : q n w∈Icc (0:ℝ) Rclock:=hnRange w (hw.trans (hvc n))
      have Hg : |g (q n w)| ≤ Bg:=hBg (mem_image_of_mem _ hq)
      have Hdist : |g (q n w)-response n (q n w)|<1 := by
        simpa only [Real.dist_eq] using hnUniform _ hq
      have Habs:=abs_add_le (response n (q n w)-g (q n w)) (g (q n w))
      rw [sub_add_cancel,abs_sub_comm] at Habs
      dsimp only [B]
      linarith [le_max_right 0 Bg]
    rw [ae_iff] at HH ⊢
    change (ENNReal.ofReal (1/(M n).xs) •
      (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v n}) _=0
    rw [Measure.smul_apply,HH,smul_zero]
  let Cr:=(Az+1/cl)*(1+C)
  have hCr : 0 ≤ Cr:=by dsimp only [Cr];positivity
  have HboundClock : ∀ᶠn in atTop,∀ᵐw∂nu n,|q n w-rad n w/(M n).xs| ≤ Rclock+Cr := by
    filter_upwards [Hrange] with n hnRange
    have HH : ∀ᵐw∂(uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v n},
        |q n w-rad n w/(M n).xs| ≤ Rclock+Cr := by
      filter_upwards [ae_restrict_mem (measurableSet_le measurable_subtype_coe measurable_const)] with w hw
      have hq : q n w∈Icc (0:ℝ) Rclock:=hnRange w (hw.trans (hvc n))
      have hr0 : 0 ≤ rad n w:=
        (omittedSweepQuantile_bounds zero_le_one ⟨(M n).data.hs.1,(M n).data.hs1⟩ (M n).context.hc (M n).context.hk (M n).context.hkc
          (M n).context.hm (M n).context.hM (M n).alpha w).1
      have hr : rad n w/(M n).xs ≤ Cr := by
        have H:=(M n).inverse_radius_le_source_mass hcl hAz w.property
        have HH:=mul_le_mul_of_nonneg_left
          (show (M n).xs+(w:ℝ) ≤ (1+C)*(M n).xs by linarith [hw.trans (hvc n)])
          (show 0 ≤ Az+1/cl by positivity)
        apply (div_le_iff₀ (M n).hxs).mpr
        dsimp only [Cr]
        nlinarith only [H,HH]
      have Habs:=abs_sub_le (q n w) 0 (rad n w/(M n).xs)
      simp only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hq.1,
        abs_of_nonneg (div_nonneg hr0 (M n).hxs.le)] at Habs
      linarith only [Habs,hq.2,hr]
    rw [ae_iff] at HH ⊢
    change (ENNReal.ofReal (1/(M n).xs) •
      (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v n}) _=0
    rw [Measure.smul_apply,HH,smul_zero]
  have Hresponse:=bounded_integral_tendsto_zero_of_positive_cut nu
    (fun n w=>response n (q n w)) hiResponse L hL B hB HboundResponse hmass HpositiveResponse
  have Hclock:=bounded_integral_tendsto_zero_of_positive_cut nu
    (fun n w=>q n w-rad n w/(M n).xs) hiClock L hL (Rclock+Cr)
    (add_nonneg hRclock.le hCr) HboundClock hmass HpositiveClock
  exact ⟨hiResponse,Hresponse,hiClock,Hclock⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
