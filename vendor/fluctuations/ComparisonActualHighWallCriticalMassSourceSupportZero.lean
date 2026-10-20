module

public import ComparisonActualHighWallMassSourceNormalizedRates
public import ComparisonLocalizedScalarSupportEventuallyIntegrable
public import ComparisonCriticalPositiveWallSupportSpinSelection
public import ComparisonActualHighWallCriticalScalarCalibration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000

theorem actual_high_wall_critical_mass_source_support_zero
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D) (hT : 0 < T)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hTeq : ∀n,(M n).data.T=T)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (hMassSource : ∀C>0,Tendsto (fun n=>
      (∫u in 0..C*(M n).xs,
        |orderedPathS (dim n+1) (M n).bf (M n).hf u-
          scalarCovarianceResponse hT
            ((M n).data.scalarMassProfile (M n).alpha)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf u)|)/
        (M n).xs^4) atTop (𝓝 0))
    (V : NonnegativeMassProfile)
    (hV : ∀t : ℝ,Tendsto (fun n=>
      (M n).actualRadiusMassProfile.val ((M n).xs*t)/(M n).xs)
      atTop (𝓝 (V.mass t)))
    (g : ℝ→ℝ)
    (hG : ∀Q>0,TendstoUniformlyOn
      (fun n=>comparisonRescaledScalarResponse
        (scalarCovarianceResponse hT
          ((M n).data.scalarMassProfile (M n).alpha)) T (M n).xs)
      g atTop (Icc (0:ℝ) Q))
    (hgc : ∀Q>0,ContinuousOn g (Icc (0:ℝ) Q)) :
    ∀t : ℝ, (0<t) → (t ∈ comparisonIncrementSupport V.mass) → g t=0 := by
  intro t ht hsupport
  let R := t+1
  let C := starMassBandConstant cu Az+cu*(|R|+1)+1
  let x := fun n=>(M n).xs
  let v := fun n=>min (C*x n) 1
  let mu := fun n=>comparisonNormalizedClockMass (x n) (v n)
  let radius := fun n (w : ParisiFinite.OrderPoint)=>
    (M n).data.wallRadius (M n).alpha w/x n
  let clock := fun n (w : ParisiFinite.OrderPoint)=>
    actualScalarClockQuantile T (dim n+1) (M n).bf (M n).hf w/x n
  let Gamma := fun n=>scalarCovarianceResponse hT
    ((M n).data.scalarMassProfile (M n).alpha)
  let G := fun n=>comparisonRescaledScalarResponse (Gamma n) T (x n)
  let F := fun a n=>{w : ParisiFinite.OrderPoint | a*x n ≤ (w:ℝ)}
  have hCbase := star_mass_band_constant_pos hcu hAz
  have hC : 0 < C := by dsimp only [C];positivity
  have hC1 : 1 ≤ C := by
    dsimp only [C]
    have H : 0 ≤ cu*(|R|+1) := by positivity
    linarith [hCbase]
  have hCband : starMassBandConstant cu Az ≤ C := by
    dsimp only [C]
    have H : 0 ≤ cu*(|R|+1) := by positivity
    linarith
  have hRC : R < C/cu := by
    apply (lt_div_iff₀ hcu).mpr
    dsimp only [C]
    have H := mul_le_mul_of_nonneg_right (le_abs_self R) hcu.le
    nlinarith
  have hv n : v n∈Icc (0:ℝ) 1 :=
    ⟨le_min (mul_nonneg hC.le (M n).hxs.le) zero_le_one,min_le_right _ _⟩
  have Hsmall : ∀ᶠn in atTop,C*x n ≤ 1 :=
    (hx.const_mul C).eventually
      (eventually_le_nhds (show C*(0:ℝ)<1 by simp))
  have Hhigh : ∀ᶠn in atTop,(M n).data.s ≤ C*x n := by
    filter_upwards [hsRatio.eventually (eventually_le_nhds hC)] with n hn
    exact (div_le_iff₀ (M n).hxs).mp hn
  have Hcut : ∀ᶠn in atTop,x n*R <
      (M n).data.wallRadius (M n).alpha (v n) := by
    filter_upwards [Hsmall,Hhigh] with n hnSmall hnHigh
    dsimp only [v]
    rw [min_eq_left hnSmall]
    have HR := ((M n).actual_closed_regular_mass_band_radius_bounds
      hcl hcu hAz (M n).hxs le_rfl hCband hnSmall hnHigh
      (show C*x n∈Icc (C*x n) (C*x n) from ⟨le_rfl,le_rfl⟩)).1
    have H := mul_lt_mul_of_pos_right hRC (M n).hxs
    exact (show x n*R < (C/cu)*x n by nlinarith only [H]).trans_le HR
  have hrm n : Measurable (radius n) :=
    (((M n).data.wallRadius_monotone (M n).alpha).measurable.comp
      measurable_subtype_coe).div_const _
  have Hpositive : ∀eps : ℝ,0 < eps→∃c : ℝ,0 < c ∧
      ∀ᶠn in atTop,c ≤ (mu n).real {w | |radius n w-t| < eps} :=
    comparison_actual_radius_cdf_support_mass
      (fun n=>(M n).data.wallRadius (M n).alpha) x v V.mass
      (fun n=>((M n).data.wallRadius_monotone (M n).alpha).monotoneOn _)
      (fun n u _=>⟨(M n).data.hrbounds.1.le.trans
        ((M n).data.wallRadius_bounds (M n).alpha u).1,
        ((M n).data.wallRadius_bounds (M n).alpha u).2⟩)
      (fun n=>(M n).hxs) hv Hcut
      (by intro a _;simpa only [ActualHighWallOverlapMinimum.actualRadiusMassProfile]
        using hV a)
      (by dsimp only [R];linarith) (fun δ hδ _=>hsupport δ hδ)
  obtain ⟨Hsource0,Hmean0,_Hclock0⟩ :=
    ActualHighWallOverlapMinimum.actual_high_wall_critical_normalized_mass_rates
      hm hdelta hroom hcl hcu hAz hC0 hCt hD hT dim hdim M
      hfixed hTeq hx hsRatio hMassSource C hC1
  dsimp only [mu,v,x] at Hsource0 Hmean0
  have hsourceInt n : Integrable (fun w : ParisiFinite.OrderPoint=>
      (orderedPathS (dim n+1) (M n).bf (M n).hf w-
        Gamma n (actualMixedClock (dim n+1) (M n).bf (M n).hf w))/x n^3)
      (mu n) := by
    have hi : IntervalIntegrable (fun u=>
        orderedPathS (dim n+1) (M n).bf (M n).hf u-
          Gamma n (actualMixedClock (dim n+1) (M n).bf (M n).hf u))
        volume 0 1 := by
      have hi0 := (M n).original_scalar_gap_intervalIntegrable
        (show (1:ℝ)∈Icc (0:ℝ) 1 by norm_num)
      cases hTeq n
      simpa only [Gamma] using hi0
    have hi1 := unitInterval.measurePreserving_coe.integrable_comp_of_integrable
      ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hi)
    have hi2 : Integrable (fun w : ParisiFinite.OrderPoint=>
        orderedPathS (dim n+1) (M n).bf (M n).hf w-
          Gamma n (actualMixedClock (dim n+1) (M n).bf (M n).hf w))
        ((uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict
          {w | (w:ℝ)≤v n}) := hi1.integrableOn
    simpa only [mu,comparisonNormalizedClockMass] using
      (hi2.smul_measure ENNReal.ofReal_ne_top).div_const (x n^3)
  have hmeanInt n : Integrable (fun w : ParisiFinite.OrderPoint=>
      orderedPathS (dim n+1) (M n).bf (M n).hf w/x n-
        (M n).data.wallRadius (M n).alpha w/x n) (mu n) := by
    have hi : IntervalIntegrable
        (fun u=>orderedPathS (dim n+1) (M n).bf (M n).hf u-
          (M n).data.wallRadius (M n).alpha u) volume 0 1 :=
      (show MonotoneOn (orderedPathS (dim n+1) (M n).bf (M n).hf) (uIcc (0:ℝ) 1) by
        simpa only [uIcc_of_le zero_le_one] using (M n).full_mass_mean_monotone).intervalIntegrable.sub
        (((M n).data.wallRadius_lipschitz (M n).alpha).continuous.intervalIntegrable 0 1)
    have hi1 := unitInterval.measurePreserving_coe.integrable_comp_of_integrable
      ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hi)
    have hi2 : Integrable (fun w : ParisiFinite.OrderPoint=>
        orderedPathS (dim n+1) (M n).bf (M n).hf w-
          (M n).data.wallRadius (M n).alpha w)
        ((uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict
          {w | (w:ℝ)≤v n}) := hi1.integrableOn
    simpa only [mu,comparisonNormalizedClockMass,sub_div] using
      (hi2.smul_measure ENNReal.ofReal_ne_top).div_const (x n)
  have hqmeas n : Measurable (clock n) := by
    have hm : Monotone (fun w : ParisiFinite.OrderPoint=>
        actualScalarClockQuantile T (dim n+1) (M n).bf (M n).hf w) := by
      intro a b hab
      exact actualScalarClockQuantile_monotone hT (dim n+1) (by omega)
        (M n).bf (M n).hf ((M n).data.bf_monotone (M n).alpha)
        ((M n).data.hf_monotone (M n).alpha) a.property b.property hab
    exact hm.measurable.div_const _
  have hGcont n : Continuous (G n) := by
    have hGamma : Continuous (Gamma n) := by
      change Continuous (fun y=>scalarPlantedEnergy hT
        ((M n).data.scalarMassProfile (M n).alpha) (y/T))
      exact (scalarPlantedEnergy_continuous hT _).comp
        (continuous_id.div_const T)
    change Continuous (fun y=>(Gamma n (T*x n*y)-x n*y)/x n^3)
    exact (((hGamma.comp (continuous_const.mul continuous_id)).sub
      (continuous_const.mul continuous_id)).div_const _)
  have hGmeas n : Measurable (fun w=>G n (clock n w)) :=
    (hGcont n).measurable.comp (hqmeas n)
  have Hloc : ∀a>0,a<C→
      (∀ᶠn in atTop,Integrable (fun w=>|G n (clock n w)|)
        ((mu n).restrict (F a n))) ∧
      (∀ᶠn in atTop,Integrable (fun w=>|clock n w-radius n w|)
        ((mu n).restrict (F a n))) ∧
      Tendsto (fun n=>∫w,|G n (clock n w)|∂(mu n).restrict (F a n)) atTop (𝓝 0) ∧
      Tendsto (fun n=>∫w,|clock n w-radius n w|∂(mu n).restrict (F a n)) atTop (𝓝 0) := by
    intro a ha haC
    have Habove : ∀ᶠn in atTop,(M n).data.s≤a*x n := by
      filter_upwards [hsRatio.eventually (eventually_le_nhds ha)] with n hn
      exact (div_le_iff₀ (M n).hxs).mp hn
    have Htemp : ∀ᶠn in atTop,(M n).data.d^2≤T := by
      have H := (hx.pow 2).eventually
        (eventually_le_nhds (show (0:ℝ)^2<T by simpa using hT))
      filter_upwards [H] with n hn
      simpa only [←hfixed n] using hn
    have hpoint : ∀ᶠn in atTop,∀w∈F a n,
        |G n (clock n w)| ≤
          |(orderedPathS (dim n+1) (M n).bf (M n).hf w-
            Gamma n (actualMixedClock (dim n+1) (M n).bf (M n).hf w))/x n^3|+
          (1/T)*|orderedPathS (dim n+1) (M n).bf (M n).hf w/x n-
            radius n w| ∧
        |clock n w-radius n w| ≤
          |orderedPathS (dim n+1) (M n).bf (M n).hf w/x n-
            radius n w| := by
      filter_upwards [Habove,Htemp] with n hnAbove hnTemp w hw
      have hu : (w:ℝ)∈Icc (M n).data.s 1 :=
        ⟨hnAbove.trans hw,w.property.2⟩
      have hwp : 0<(w:ℝ) := (mul_pos ha (M n).hxs).trans_le hw
      have hqe : clock n w = actualMixedClock (dim n+1) (M n).bf (M n).hf w/(T*x n) := by
        dsimp only [clock,x]
        rw [actualScalarClockQuantile_on (dim n+1) (M n).bf (M n).hf hwp]
        ring
      constructor
      · have HB := (M n).high_mass_scalar_response_source_bound (hfixed n)
          (Gamma n) hu
        dsimp only at HB
        rw [hTeq n] at HB
        simpa only [G,x,radius,hqe] using HB
      · have HB := (M n).high_mass_mixed_clock_radius_abs_le_mean_radius_abs
          (by simpa only [hTeq n] using hnTemp) hu
        rw [hTeq n] at HB
        dsimp only [clock,radius,x]
        rw [actualScalarClockQuantile_on (dim n+1) (M n).bf (M n).hf hwp]
        have Hdiv := div_le_div_of_nonneg_right HB (M n).hxs.le
        simpa only [x,←sub_div,abs_div,abs_of_pos (M n).hxs] using Hdiv
    let A := fun n (w : ParisiFinite.OrderPoint)=>
      |(orderedPathS (dim n+1) (M n).bf (M n).hf w-
        Gamma n (actualMixedClock (dim n+1) (M n).bf (M n).hf w))/x n^3|
    let B := fun n (w : ParisiFinite.OrderPoint)=>
      |orderedPathS (dim n+1) (M n).bf (M n).hf w/x n-radius n w|
    have hAB n : Integrable (fun w=>A n w+(1/T)*B n w)
        ((mu n).restrict (F a n)) :=
      ((hsourceInt n).abs.integrableOn).add
        (((hmeanInt n).abs.integrableOn).const_mul (1/T))
    have hBi n : Integrable (B n) ((mu n).restrict (F a n)) :=
      (hmeanInt n).abs.integrableOn
    have HGint : ∀ᶠn in atTop,Integrable (fun w=>|G n (clock n w)|)
        ((mu n).restrict (F a n)) := by
      filter_upwards [hpoint] with n hn
      apply (hAB n).mono' (hGmeas n).abs.aestronglyMeasurable
      filter_upwards [ae_restrict_mem (measurableSet_le measurable_const measurable_subtype_coe)]
        with w hw
      simpa only [Real.norm_eq_abs,abs_abs] using (hn w hw).1
    have HKint : ∀ᶠn in atTop,Integrable (fun w=>|clock n w-radius n w|)
        ((mu n).restrict (F a n)) := by
      filter_upwards [hpoint] with n hn
      apply (hBi n).mono' ((hqmeas n).sub (hrm n)).abs.aestronglyMeasurable
      filter_upwards [ae_restrict_mem (measurableSet_le measurable_const measurable_subtype_coe)]
        with w hw
      simpa only [Real.norm_eq_abs,abs_abs,Pi.sub_apply,B] using (hn w hw).2
    have Hresponse : Tendsto
        (fun n=>∫w,|G n (clock n w)|∂(mu n).restrict (F a n))
        atTop (𝓝 0) := by
      have Hbound := Hsource0.add (Hmean0.const_mul (1/T))
      simp only [zero_add,mul_zero] at Hbound
      apply squeeze_zero' (Eventually.of_forall (fun _=>integral_nonneg (fun _=>abs_nonneg _))) _ Hbound
      filter_upwards [hpoint,HGint] with n hn hGi
      have hAi : Integrable (A n) (mu n) := (hsourceInt n).abs
      have hBfull : Integrable (B n) (mu n) := (hmeanInt n).abs
      have Hmono := integral_mono_ae hGi (hAB n)
        (by filter_upwards [ae_restrict_mem (measurableSet_le measurable_const measurable_subtype_coe)]
          with w hw;exact (hn w hw).1)
      have HrestrA : (∫w,A n w∂(mu n).restrict (F a n))≤∫w,A n w∂mu n :=
        setIntegral_le_integral hAi (ae_of_all _ (fun _=>abs_nonneg _))
      have HrestrB : (∫w,B n w∂(mu n).restrict (F a n))≤∫w,B n w∂mu n :=
        setIntegral_le_integral hBfull (ae_of_all _ (fun _=>abs_nonneg _))
      rw [integral_add (hAi.integrableOn) ((hBfull.integrableOn).const_mul (1/T)),
        integral_const_mul] at Hmono
      dsimp only [A,B] at Hmono HrestrA HrestrB
      have H := add_le_add HrestrA
        (mul_le_mul_of_nonneg_left HrestrB (one_div_nonneg.mpr hT.le))
      exact Hmono.trans H
    have Hclock : Tendsto
        (fun n=>∫w,|clock n w-radius n w|∂(mu n).restrict (F a n))
        atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun _=>integral_nonneg (fun _=>abs_nonneg _))) _ Hmean0
      filter_upwards [hpoint,HKint] with n hn hKi
      have hBi := hBi n
      have Hmono := integral_mono_ae hKi hBi
        (by filter_upwards [ae_restrict_mem (measurableSet_le measurable_const measurable_subtype_coe)]
          with w hw;exact (hn w hw).2)
      exact Hmono.trans
        (setIntegral_le_integral (hmeanInt n).abs (ae_of_all _ (fun _=>abs_nonneg _)))
    exact ⟨HGint,HKint,Hresponse,Hclock⟩
  exact comparison_scalar_zero_of_localized_mass_eventually_integrable
    mu (fun _=>inferInstance) radius clock G g F hC ht
    (by dsimp only [R];linarith)
    (fun a _ _ n=>measurableSet_le measurable_const measurable_subtype_coe)
    (fun a ha _ n=>comparison_normalized_lower_mass_le (M n).hxs ha.le)
    hrm Hpositive Hloc (hG R (by dsimp only [R];linarith))
    ((hgc R (by dsimp only [R];linarith)).continuousAt
      (Icc_mem_nhds ht (by dsimp only [R];linarith)))

end OAI.SKFluctuations.LaplaceWindowFormalization
