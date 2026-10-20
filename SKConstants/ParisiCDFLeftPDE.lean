module

public import SKConstants.ParisiCDFGapPDE

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

lemma scalarCDFOperator_constant_heat {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β c s : ℝ)
    (hc : c ∈ Icc (0 : ℝ) 1) (t : ℝ≥0) (ht : t ≤ 1) :
    scalarCDFOperator β (fun _ => c) s t f =
      varianceLogHeat c ((Real.toNNReal (β^2)*t : ℝ≥0) : ℝ) f := by
  funext x
  rw [scalarCDFOperator_eq_chain hf hLip β (fun _ => hc) monotone_const [(c,t)]
    (by simpa using hc) s t ht (by simp [chainDuration]) ⟨by simp, trivial⟩ x]
  change scalarTimeStep β c t f x = _
  rw [scalarTimeStep_eq_logSemigroup hLip.continuous.measurable,
    ← varianceLogHeat_eq_logSemigroup hLip.continuous.measurable]

theorem scalarCDFValue_left_heat_error_coefficient (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1)
    {r q c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (hr0 : 0 ≤ r) (hrq : r ≤ q) (hq1 : q ≤ 1) (x : ℝ) :
    |scalarCDFValue β α r (Real.toNNReal (1-r)) x -
      varianceLogHeat c (β^2*(q-r))
        (scalarCDFValue β α q (Real.toNNReal (1-q))) x| ≤
      scalarTimeMassConstantK β 1*(∫ z in r..q, |α z-c|) := by
  have hqt : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith
  have hrt : Real.toNNReal (q-r) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith
  have hf := scalarCDFValue_regular β ha α.mono q _ hqt
  have hLip := scalarCDFValue_lipschitz β ha α.mono q _ hqt
  have H := scalarCDFOperator_cdf_lipschitz hf hLip β ha α.mono
    (fun _ => hc) monotone_const r (Real.toNNReal (q-r)) hrt x
  rw [scalarCDFOperator_constant_heat hf hLip β c r hc _ hrt] at H
  have hv : ((Real.toNNReal (β^2)*Real.toNNReal (q-r) : ℝ≥0) : ℝ) = β^2*(q-r) := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg β),
      Real.coe_toNNReal _ (sub_nonneg.mpr hrq)]
  rw [hv, Real.coe_toNNReal _ (sub_nonneg.mpr hrq), add_sub_cancel] at H
  rw [scalarCDFValue_suffix_semigroup β α ha h1 hr0 hrq hq1]
  exact H

lemma hasDerivWithinAt_left_of_integral_error {f g η : ℝ → ℝ} {q d C : ℝ}
    (hη : Measurable η) (hηc : ContinuousWithinAt η (Iio q) q) (hη0 : η q = 0)
    (hC : 0 ≤ C) (hfg : f q = g q)
    (hg : HasDerivWithinAt g d (Iio q) q)
    (herr : ∀ᶠ r in 𝓝[<] q, |f r-g r| ≤ C*|∫ z in q..r, η z|) :
    HasDerivWithinAt f d (Iio q) q := by
  let I (r : ℝ) := ∫ z in q..r, η z
  have hηc' : ContinuousWithinAt η (Iic q) q := by
    apply hηc.insert.mono
    intro z hz
    rcases eq_or_lt_of_le hz with he | hz
    · exact Or.inl he
    · exact Or.inr hz
  have hI : HasDerivWithinAt I 0 (Iic q) q := by
    simpa only [hη0] using intervalIntegral.integral_hasDerivWithinAt_right
      (a := q) (b := q) (s := Iic q) (t := Iic q) IntervalIntegrable.refl
      hη.stronglyMeasurable.stronglyMeasurableAtFilter hηc'
  have hlimI := ((hasDerivWithinAt_iff_tendsto_slope' (show q ∉ Iio q by simp)).mp
    (hI.mono Iio_subset_Iic_self)).abs.const_mul C
  have hzero : Tendsto (fun r => slope f q r-slope g q r) (𝓝[<] q) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun r => norm_nonneg _)) _
      (by simpa only [abs_zero, mul_zero] using hlimI)
    filter_upwards [herr, self_mem_nhdsWithin] with r hr hrq
    have hne : r-q ≠ 0 := sub_ne_zero.mpr (ne_of_lt hrq)
    rw [Real.norm_eq_abs]
    have he : slope f q r-slope g q r = (f r-g r)/(r-q) := by
      simp only [slope_def_field, hfg]
      ring
    rw [he, abs_div]
    have hbound := div_le_div_of_nonneg_right hr (abs_nonneg (r-q))
    simpa only [slope_def_field, I, intervalIntegral.integral_same, sub_zero,
      abs_div, mul_div_assoc] using hbound
  have hg' := (hasDerivWithinAt_iff_tendsto_slope' (show q ∉ Iio q by simp)).mp hg
  apply (hasDerivWithinAt_iff_tendsto_slope' (show q ∉ Iio q by simp)).mpr
  convert hzero.add hg' using 1
  · funext r
    ring
  · simp

theorem scalarCDFValue_time_derivative_left_of_tendsto
    (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {q c : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hc : c ∈ Icc (0 : ℝ) 1)
    (hαc : Tendsto (α : ℝ → ℝ) (𝓝[<] q) (𝓝 c))
    (x : ℝ) :
    HasDerivWithinAt (fun r => scalarCDFValue β α r (Real.toNNReal (1-r)) x)
      (-(β^2/2)*(scalarCDFHessian β α q (Real.toNNReal (1-q)) x +
        c*(scalarCDFGradient β α q (Real.toNNReal (1-q)) x)^2)) (Iio q) q := by
  let f := scalarCDFValue β α q (Real.toNNReal (1-q))
  let g (r : ℝ) := varianceLogHeat c (β^2*(q-r)) f x
  have hf : RegularDatum f := scalarCDFValue_regularDatum β α ha hβ hq0.le hq1
  have hqt : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith
  have hLip : LipschitzWith 1 f := scalarCDFValue_lipschitz β ha α.mono q _ hqt
  have houter : HasDerivWithinAt (fun v => varianceLogHeat c v f x)
      ((1/2:ℝ)*varianceTilted c 0 f (generatorWeight c f) x)
      (Ici 0) (β^2*(q-q)) := by
    simpa only [sub_self, mul_zero] using
      varianceLogHeat_time_derivative hf hLip c (by norm_num : (0:ℝ) ≤ 0) x
  have H := houter.comp q
    ((((hasDerivAt_const q q).sub (hasDerivAt_id q)).const_mul (β^2)).hasDerivWithinAt
      (s := Iic q)) (by intro r hr; exact mul_nonneg (sq_nonneg β) (sub_nonneg.mpr hr))
  have hgen := varianceLogHeat_generator_identity hf hLip c (by norm_num : (0:ℝ) ≤ 0) x
  have hzero : varianceLogHeat c 0 f = f := by
    funext z
    by_cases hc0 : c = 0
    · simp [varianceLogHeat, hc0, varianceHeat, scaled]
    · simp [varianceLogHeat, hc0, varianceHeat, scaled, mul_div_cancel_left₀ _ hc0]
  rw [hzero] at hgen
  rw [(scalarCDFValue_hasDerivAt β ha α.mono q _ hqt x).deriv,
    show deriv (deriv f) x = scalarCDFHessian β α q (Real.toNNReal (1-q)) x by
      change deriv (deriv (scalarCDFValue β α q (Real.toNNReal (1-q)))) x = _
      rw [← scalarCDF_gradient_eq_deriv ha α.mono β q _ hqt]
      exact (scalarCDFGradient_hasDerivAt β ha α.mono q _ hqt x).deriv] at hgen
  have hg : HasDerivWithinAt g
      (-(β^2/2)*(scalarCDFHessian β α q (Real.toNNReal (1-q)) x +
        c*(scalarCDFGradient β α q (Real.toNNReal (1-q)) x)^2)) (Iio q) q := by
    have hd : (1/2:ℝ)*varianceTilted c 0 f (generatorWeight c f) x *
        (β^2*(0-1)) = -(β^2/2)*
          (scalarCDFHessian β α q (Real.toNNReal (1-q)) x +
            c*(scalarCDFGradient β α q (Real.toNNReal (1-q)) x)^2) := by
      rw [hgen]
      ring
    simpa only [g, Function.comp_def, Pi.sub_apply, id_eq, sub_self, mul_zero] using
      (H.congr_deriv hd).mono Iio_subset_Iic_self
  have hfg : scalarCDFValue β α q (Real.toNNReal (1-q)) x = g q := by
    simp only [g, sub_self, mul_zero, hzero, f]
  let η (z : ℝ) := if z = q then 0 else |α z-c|
  have hηm : Measurable η := by
    exact measurable_const.ite (measurableSet_singleton q)
      ((α.mono.measurable.sub measurable_const).abs)
  have hη0 : η q = 0 := by simp [η]
  have hηc : ContinuousWithinAt η (Iio q) q := by
    have Hη := (hαc.sub_const c).abs
    apply (show Tendsto η (𝓝[<] q) (𝓝 (η q)) from ?_)
    rw [hη0]
    apply (show Tendsto (fun z => |α z-c|) (𝓝[<] q) (𝓝 0) by
      simpa only [sub_self, abs_zero] using Hη).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [η, if_neg (ne_of_lt hz)]
  have hηint (r : ℝ) : (∫ z in q..r, η z) = ∫ z in q..r, |α z-c| := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne q] with z hz _
    simp only [η, if_neg hz]
  apply hasDerivWithinAt_left_of_integral_error
    (C := scalarTimeMassConstantK β 1) hηm hηc hη0
    (scalarTimeMassConstantK_nonneg β 1) hfg hg
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hq0)] with r hr hr0
  rw [hηint]
  have HE := scalarCDFValue_left_heat_error_coefficient β α ha h1 hc hr0.le hr.le hq1.le x
  apply HE.trans
  rw [intervalIntegral.integral_symm q r]
  exact mul_le_mul_of_nonneg_left (neg_le_abs _) (scalarTimeMassConstantK_nonneg β 1)

theorem scalarCDFValue_time_derivative_leftLimit
    (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (x : ℝ) :
    HasDerivWithinAt (fun r => scalarCDFValue β α r (Real.toNNReal (1-r)) x)
      (-(β^2/2)*(scalarCDFHessian β α q (Real.toNNReal (1-q)) x +
        Function.leftLim (α : ℝ → ℝ) q*
          (scalarCDFGradient β α q (Real.toNNReal (1-q)) x)^2)) (Iio q) q := by
  apply scalarCDFValue_time_derivative_left_of_tendsto β α ha h1 hβ hq0 hq1
  · exact isClosed_Icc.mem_of_tendsto (α.mono.tendsto_leftLim q)
      (Eventually.of_forall ha)
  · exact α.mono.tendsto_leftLim q

theorem scalarCDFValue_time_derivative_left
    (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hαc : ContinuousAt (α : ℝ → ℝ) q)
    (x : ℝ) :
    HasDerivWithinAt (fun r => scalarCDFValue β α r (Real.toNNReal (1-r)) x)
      (-(β^2/2)*(scalarCDFHessian β α q (Real.toNNReal (1-q)) x +
        α q*(scalarCDFGradient β α q (Real.toNNReal (1-q)) x)^2)) (Iio q) q :=
  scalarCDFValue_time_derivative_left_of_tendsto β α ha h1 hβ hq0 hq1 (ha q)
    (hαc.tendsto.mono_left nhdsWithin_le_nhds) x

end SKConstants.ParisiFullSupport
