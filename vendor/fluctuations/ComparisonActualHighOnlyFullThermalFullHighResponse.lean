module

public import ComparisonActualHighOnlyFullThermalHighResponse
public import ComparisonNativeActualPositiveBandTruncation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum ActualHighOnlyOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false

 theorem actual_comparable_context_full_HIGH_response_high_only_of_full_thermal
    {m delta cl cu Az C0 Ct D Bclock T Ccal w0 : ℝ}
    (C : ℝ) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (Hfull : Tendsto (fun n=>(∫u in (0:ℝ)..1,Real.sqrt
      (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))/(M n).xs^2) atTop (𝓝 0))
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hw0 : 0 < w0)
    (hWlower : ∀ᶠn in atTop,w0 ≤ (M n).canonicalDirectTestBandScale)
    (hWupper : ∀ᶠn in atTop,(M n).canonicalDirectTestBandScale ≤ 1)
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
    actual_comparable_context_positive_band_HIGH_response_high_only_of_full_thermal c C hc hC hm hdelta hroom hcl hcu hAz hC0 hCt
      dim hdim M G Hfull hsmall hw0 hWlower hWupper hlarge htotal
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

end OAI.SKFluctuations.LaplaceWindowFormalization
