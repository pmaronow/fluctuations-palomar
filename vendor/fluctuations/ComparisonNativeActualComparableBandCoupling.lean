module

public import ComparisonNativeActualPositiveBandTruncation
public import ComparisonNativeActualLocalTemperatureClockCoupling
public import ComparisonNativeGeneralScalarCuts
public import ComparisonNativeActualHistoryLocalTemperatureCouplingAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Measure.Subtype.measureSpace

 theorem actual_comparable_context_original_scalar_radius_coupling
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (C : ℝ) (hC : 0 < C) (v : ℕ→ℝ) (hv : ∀n,v n∈Icc (0:ℝ) 1)
    (hvc : ∀n,v n ≤ C*(M n).xs) :
    Tendsto (fun n=>∫w : ParisiFinite.OrderPoint,
      |actualScalarClockQuantile T (dim n+1) (M n).bf (M n).hf w/(M n).xs-
        (M n).R w/(M n).xs|∂comparisonNormalizedClockMass (M n).xs (v n)) atTop (𝓝 0) := by
  let nu:=fun n=>comparisonNormalizedClockMass (M n).xs (v n)
  let S:=fun n (w : ParisiFinite.OrderPoint)=>orderedPathS (dim n+1) (M n).bf (M n).hf w
  let rad:=fun n (w : ParisiFinite.OrderPoint)=>(M n).R w
  let Q:=fun n (w : ParisiFinite.OrderPoint)=>actualScalarClockQuantile T (dim n+1) (M n).bf (M n).hf w
  let f:=fun n w=>Q n w/(M n).xs-rad n w/(M n).xs
  have hi n : Integrable (f n) (nu n) := by
    have hmQ : Measurable (Q n) :=
      (show Monotone (Q n) from fun u v huv=>actualScalarClockQuantile_monotone
        G.hT (dim n+1) (by omega) (M n).bf (M n).hf (M n).inherited_bf_monotone
          (M n).inherited_hf_monotone u.property v.property huv).measurable
    have hmR : Measurable (rad n) :=
      (comparisonSweepQuantile_continuous (M n).context.hc (M n).context.hk (M n).context.hkc
        (M n).context.hm (M n).context.hM (M n).alpha).measurable.comp measurable_subtype_coe
    have Hsigned : Integrable (fun w=>Q n w-rad n w) (nu n) := by
      apply (integrable_const (2:ℝ)).mono' (hmQ.sub hmR).aestronglyMeasurable
      filter_upwards [] with w
      have hq:=actualScalarClockQuantile_bounds G.hT (dim n+1) (by omega) (M n).bf (M n).hf
        (M n).inherited_bf_monotone (M n).inherited_hf_monotone
        ((M n).inherited_total_clock_le (htotal n)) w w.property
      have hr:=comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk (M n).context.hkc
        (M n).context.hm (M n).context.hM (M n).alpha w
      change Q n w∈Icc (0:ℝ) 1 at hq
      change rad n w∈Icc (0:ℝ) 1 at hr
      have H:=abs_sub_le (Q n w) 0 (rad n w)
      simp only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hq.1,abs_of_nonneg hr.1] at H
      change |Q n w-rad n w| ≤ 2
      linarith only [H,hq.2,hr.2]
    simpa only [f,sub_div] using Hsigned.div_const (M n).xs
  let mu:=fun n=>(uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v n}
  have Hsquare:=regular_original_retained_squared_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M (fun n=>(M n).xs) v
    (fun _=>le_rfl) G.xs_zero G.pullback C hC hv hvc
  have Hspin:=comparison_original_mass_normalized_L1_tendsto mu (fun _=>inferInstance)
    (fun n w=>S n w-rad n w) (fun n=>(M n).xs) (fun n=>(M n).hxs) hC.le
    (fun n=>((M n).original_retained_mismatch_integrable (v n)).1)
    (fun n=>((M n).original_retained_mismatch_integrable (v n)).2)
    (fun n=>by rw [comparison_original_retained_mass_exact (hv n)];exact hvc n) Hsquare
  have hiSpin n : Integrable (fun w=>(S n w-rad n w)/(M n).xs) (nu n) :=
    ((((M n).original_retained_mismatch_integrable (v n)).1).smul_measure ENNReal.ofReal_ne_top).div_const _
  have Hspin' : Tendsto (fun n=>∫w,|(S n w-rad n w)/(M n).xs|∂nu n) atTop (𝓝 0) := by
    simpa only [mu,nu,comparisonNormalizedClockMass] using Hspin
  have hnMass n : (nu n).real univ ≤ C := by
    unfold nu comparisonNormalizedClockMass
    rw [measureReal_ennreal_smul_apply,ENNReal.toReal_ofReal (one_div_nonneg.mpr (M n).hxs.le),
      measureReal_restrict_apply MeasurableSet.univ,univ_inter,uniformOrderMass_atMost (hv n)]
    exact (mul_le_mul_of_nonneg_left (hvc n) (one_div_nonneg.mpr (M n).hxs.le)).trans_eq (by field_simp [(M n).hxs.ne'])
  have Hupper : ∀n,∀ᵐ(w : ParisiFinite.OrderPoint)∂nu n,(w:ℝ) ≤ v n := by
    intro n
    have H : ∀ᵐ(w : ParisiFinite.OrderPoint)∂(uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict
        {w : ParisiFinite.OrderPoint | (w:ℝ)≤v n},(w:ℝ)≤v n :=
      ae_restrict_mem (measurableSet_le measurable_subtype_coe measurable_const)
    rw [ae_iff] at H ⊢
    change (ENNReal.ofReal (1/(M n).xs) •
      (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ)≤v n}) _=0
    rw [Measure.smul_apply,H,smul_zero]
  let L:=fun c n=>{w : ParisiFinite.OrderPoint | (w:ℝ)<c*(M n).xs}
  have hL c n : MeasurableSet (L c n):=measurableSet_lt measurable_subtype_coe measurable_const
  have hmass c (hc : 0<c) n : (nu n).real (L c n) ≤ c:=
    normalized_clock_mass_low_prefix_le (M n).hxs hc
  obtain ⟨B,hB,Hmean⟩:=eventually_actual_minimum_mass_mean_upper (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cs:=B*(1+C)
  have hCs : 0 ≤ Cs:=by dsimp only [Cs];positivity
  let E:=(Cs+1)/T
  have hE : 0 ≤ E:=by dsimp only [E];have hT:=G.hT;positivity
  have Hpositive c (hc : 0<c) : Tendsto (fun n=>∫w in (L c n)ᶜ,|f n w|∂nu n) atTop (𝓝 0) := by
    have Hrate:=((Hspin'.const_mul 2).add (((G.xs_zero.pow 2).const_mul (E*C))))
    simp only [mul_zero,zero_pow (by norm_num : (2:ℕ)≠0),add_zero] at Hrate
    apply squeeze_zero' (Eventually.of_forall (fun _=>integral_nonneg (fun _=>abs_nonneg _))) _ Hrate
    filter_upwards [hdim.eventually Hmean,G.positive_band_clocks c C 1 hc hC.le zero_lt_one] with n hnMean hnClock
    have Hpoint : ∀ᵐw∂(nu n).restrict (L c n)ᶜ,
        |f n w| ≤ 2*|(S n w-rad n w)/(M n).xs|+E*(M n).xs^2 := by
      filter_upwards [ae_restrict_mem (hL c n).compl,ae_restrict_of_ae (Hupper n)] with w hw hwU
      have hwpos : c*(M n).xs ≤ (w:ℝ):=le_of_not_gt hw
      have hwC : (w:ℝ) ≤ C*(M n).xs:=hwU.trans (hvc n)
      have hS : S n w ≤ Cs*(M n).xs := by
        have H:=hnMean (M n) w ⟨(mul_pos hc (M n).hxs).trans_le hwpos,w.property.2⟩
        have HH:=mul_le_mul_of_nonneg_left (show (M n).xs+(w:ℝ) ≤ (1+C)*(M n).xs by linarith only [hwC]) hB.le
        exact H.trans (by dsimp only [Cs];nlinarith only [HH])
      have Hclock:=hnClock w ⟨hwpos,le_min hwC w.property.2⟩
      have H:=(M n).inherited_local_temperature_scalar_quantile_radius_abs_le_of_eq4
        G.hT G.hT (htotal n) w.property (show (0:ℝ)≤1 by norm_num) Hclock.1 Hclock.2 hS
      simp only [one_mul,div_self G.hT.ne'] at H
      dsimp only [f]
      rw [←sub_div,abs_div,abs_of_pos (M n).hxs]
      apply (div_le_iff₀ (M n).hxs).mpr
      have Habs : |(S n w-rad n w)/(M n).xs| *(M n).xs = |S n w-rad n w| := by
        rw [abs_div,abs_of_pos (M n).hxs]
        field_simp [(M n).hxs.ne']
      dsimp only [Q,S,rad,E] at H Habs ⊢
      nlinarith only [H,Habs]
    have H:=integral_mono_ae (hi n).abs.restrict
      (((hiSpin n).abs.restrict.const_mul 2).add (integrable_const (E*(M n).xs^2))) Hpoint
    simp only [Pi.add_apply] at H
    rw [integral_add ((hiSpin n).abs.restrict.const_mul 2) (integrable_const _),integral_const_mul,
      integral_const,smul_eq_mul] at H
    have HM : ((nu n).restrict (L c n)ᶜ).real univ ≤ C := by
      rw [measureReal_restrict_apply MeasurableSet.univ,univ_inter]
      exact (measureReal_mono (μ:=nu n) (show (L c n)ᶜ⊆univ from subset_univ _)).trans (hnMass n)
    have HspinMono : (∫w in (L c n)ᶜ,|(S n w-rad n w)/(M n).xs|∂nu n) ≤
        ∫w,|(S n w-rad n w)/(M n).xs|∂nu n :=
      integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun _=>abs_nonneg _)) (hiSpin n).abs
    have HH:=mul_le_mul_of_nonneg_left HM (mul_nonneg hE (sq_nonneg (M n).xs))
    nlinarith only [H,HspinMono,HH]
  obtain ⟨Rclock,hRclock,Hrange⟩:=actual_initial_compact_clock_range_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M G.xs_zero G.hT G.hT htotal C hC
    (by simpa only [one_mul] using G.initial_field_clock C 1 hC zero_lt_one)
  let Cr:=(Az+1/cl)*(1+C)
  have hCr : 0 ≤ Cr:=by dsimp only [Cr];positivity
  have Hbound : ∀ᶠn in atTop,∀ᵐw∂nu n,|f n w| ≤ Rclock+Cr := by
    filter_upwards [Hrange,G.total_root] with n hnRange hnRoot
    filter_upwards [Hupper n] with w hw
    have hq : Q n w/(M n).xs∈Icc (0:ℝ) Rclock := by
      dsimp only [Q]
      rw [(M n).inherited_local_temperature_scalar_quantile_eq_mixed_of_root T hnRoot.2 w.property.1]
      simpa only [div_div] using hnRange w (hw.trans (hvc n))
    have hr0 : 0 ≤ rad n w:=
      (comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk (M n).context.hkc
        (M n).context.hm (M n).context.hM (M n).alpha w).1
    have hr : rad n w/(M n).xs ≤ Cr := by
      have H:=(M n).inverse_radius_le_source_mass hcl hAz w.property
      have HH:=mul_le_mul_of_nonneg_left
        (show (M n).xs+(w:ℝ) ≤ (1+C)*(M n).xs by linarith [hw.trans (hvc n)])
        (show 0 ≤ Az+1/cl by positivity)
      apply (div_le_iff₀ (M n).hxs).mpr
      dsimp only [Cr]
      nlinarith only [H,HH]
    have Habs:=abs_sub_le (Q n w/(M n).xs) 0 (rad n w/(M n).xs)
    simp only [sub_zero,zero_sub,abs_neg,abs_of_nonneg hq.1,
      abs_of_nonneg (div_nonneg hr0 (M n).hxs.le)] at Habs
    exact Habs.trans (add_le_add hq.2 hr)
  exact bounded_integral_tendsto_zero_of_positive_cut nu f hi L hL (Rclock+Cr)
    (add_nonneg hRclock.le hCr) Hbound hmass Hpositive

 theorem actual_comparable_context_initial_mixed_radius_coupling
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*(M n).xs,
      |actualMixedClock (dim n+1) (M n).bf (M n).hf u/T-(M n).R u|)/(M n).xs^2) atTop (𝓝 0) := by
  let v:=fun n=>min (C*(M n).xs) 1
  have hv n : v n∈Icc (0:ℝ) 1:=
    ⟨le_min (mul_nonneg hC.le (M n).hxs.le) zero_le_one,min_le_right _ _⟩
  have H:=actual_comparable_context_original_scalar_radius_coupling hm hdelta hroom
    hcl hcu hAz hC0 hCt dim hdim M G htotal C hC v hv (fun _=>min_le_left _ _)
  apply H.congr'
  have Hunit:=((G.xs_zero.const_mul C).eventually
    (eventually_le_nhds (by simp : C*(0:ℝ)<1)))
  filter_upwards [Hunit,G.total_root] with n hn hnRoot
  dsimp only [v]
  rw [min_eq_left hn]
  unfold comparisonNormalizedClockMass
  rw [integral_smul_measure,ENNReal.toReal_ofReal (one_div_nonneg.mpr (M n).hxs.le)]
  simp_rw [←sub_div,abs_div,abs_of_pos (M n).hxs]
  rw [integral_div,comparison_original_retained_integral_eq_interval
    (show C*(M n).xs∈Icc (0:ℝ) 1 from ⟨(mul_pos hC (M n).hxs).le,hn⟩)
    (fun u=>|actualScalarClockQuantile T (dim n+1) (M n).bf (M n).hf u-(M n).R u|)]
  have Heq : (∫u in 0..C*(M n).xs,
      |actualScalarClockQuantile T (dim n+1) (M n).bf (M n).hf u-(M n).R u|)=
      ∫u in 0..C*(M n).xs,
      |actualMixedClock (dim n+1) (M n).bf (M n).hf u/T-(M n).R u| := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (mul_pos hC (M n).hxs).le] at hu
    dsimp only
    rw [(M n).inherited_local_temperature_scalar_quantile_eq_mixed_of_root T hnRoot.2 hu.1]
  rw [Heq]
  simp only [smul_eq_mul]
  ring

end OAI.SKFluctuations.LaplaceWindowFormalization
