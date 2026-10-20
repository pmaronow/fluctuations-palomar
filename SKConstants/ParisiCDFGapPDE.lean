module

public import SKConstants.ParisiCDFSmoothFamily
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.CDFSuffixSemigroup
public import SKConstants.Upstream.OAI.Probability.SKSupport.Foundations.DerivWithinVarianceHeatWeightExp

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

theorem scalarCDFValue_constant_interval_heat (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1)
    {a b c q : ℝ} (ha0 : 0 ≤ a) (hb1 : b ≤ 1)
    (hc : c ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc a b)
    (hconstant : ∀ z ∈ Ico a b, α z = c) :
    scalarCDFValue β α q (Real.toNNReal (1-q)) =
      varianceLogHeat c (β^2*(b-q))
        (scalarCDFValue β α b (Real.toNNReal (1-b))) := by
  have hb0 : 0 ≤ b := ha0.trans (hq.1.trans hq.2)
  have ht1 : Real.toNNReal (1-b) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith
  let t := Real.toNNReal (b-q)
  have ht : (t : ℝ) = b-q := Real.coe_toNNReal _ (sub_nonneg.mpr hq.2)
  have htb : t ≤ 1 := by
    rw [← NNReal.coe_le_coe, ht, NNReal.coe_one]
    linarith [ha0.trans hq.1]
  have hmodel : TimeChainModels (α : ℝ → ℝ) q [(c,t)] := by
    refine ⟨?_, trivial⟩
    intro z hz
    apply hconstant z
    exact ⟨hq.1.trans hz.1, by simpa only [ht, add_sub_cancel] using hz.2⟩
  have hf := scalarCDFValue_regular β ha α.mono b _ ht1
  have hLip := scalarCDFValue_lipschitz β ha α.mono b _ ht1
  rw [scalarCDFValue_suffix_semigroup β α ha h1 (ha0.trans hq.1) hq.2 hb1]
  funext x
  rw [scalarCDFOperator_eq_chain hf hLip β ha α.mono [(c,t)]
    (by simpa using hc) q t htb (by simp [chainDuration]) hmodel x]
  change scalarTimeStep β c t (scalarCDFValue β α b (Real.toNNReal (1-b))) x = _
  rw [scalarTimeStep_eq_logSemigroup hLip.continuous.measurable]
  have hv : ((Real.toNNReal (β^2)*t : ℝ≥0) : ℝ) = β^2*(b-q) := by
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (sq_nonneg β), ht]
  rw [← varianceLogHeat_eq_logSemigroup hLip.continuous.measurable, hv]

theorem scalarCDFValue_time_derivative_on_constant_interval
    (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0 : ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {a b c q : ℝ} (ha0 : 0 ≤ a) (hb1 : b < 1)
    (hc : c ∈ Icc (0 : ℝ) 1) (hq : q ∈ Ioo a b)
    (hconstant : ∀ z ∈ Ico a b, α z = c) (x : ℝ) :
    HasDerivAt (fun r => scalarCDFValue β α r (Real.toNNReal (1-r)) x)
      (-(β^2/2)*(scalarCDFHessian β α q (Real.toNNReal (1-q)) x +
        c*(scalarCDFGradient β α q (Real.toNNReal (1-q)) x)^2)) q := by
  let f := scalarCDFValue β α b (Real.toNNReal (1-b))
  let v := β^2*(b-q)
  have hv : 0 < v := mul_pos (sq_pos_of_ne_zero hβ) (sub_pos.mpr hq.2)
  have hf : RegularDatum f :=
    scalarCDFValue_regularDatum β α ha hβ (ha0.trans (hq.1.le.trans hq.2.le)) hb1
  have htb : Real.toNNReal (1-b) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith [ha0.trans (hq.1.le.trans hq.2.le)]
  have hLip : LipschitzWith 1 f := scalarCDFValue_lipschitz β ha α.mono b _ htb
  have hd := ((varianceLogHeat_time_derivative hf hLip c hv.le x).hasDerivAt
    (Ici_mem_nhds hv)).comp q
    (((hasDerivAt_const q b).sub (hasDerivAt_id q)).const_mul (β^2))
  have he : scalarCDFValue β α q (Real.toNNReal (1-q)) = varianceLogHeat c v f :=
    scalarCDFValue_constant_interval_heat β α ha h1 ha0 hb1.le hc ⟨hq.1.le,hq.2.le⟩ hconstant
  have htq : Real.toNNReal (1-q) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_one]
    linarith [ha0.trans hq.1.le]
  have hG : deriv (varianceLogHeat c v f) x =
      scalarCDFGradient β α q (Real.toNNReal (1-q)) x := by
    rw [← he]
    exact (scalarCDFValue_hasDerivAt β ha α.mono q _ htq x).deriv
  have hH : deriv (deriv (varianceLogHeat c v f)) x =
      scalarCDFHessian β α q (Real.toNNReal (1-q)) x := by
    rw [← he, ← scalarCDF_gradient_eq_deriv ha α.mono β q _ htq]
    exact (scalarCDFGradient_hasDerivAt β ha α.mono q _ htq x).deriv
  have hgen := varianceLogHeat_generator_identity hf hLip c hv.le x
  rw [hG, hH] at hgen
  have hd' : HasDerivAt (fun r => varianceLogHeat c (β^2*(b-r)) f x)
      (-(β^2/2)*(scalarCDFHessian β α q (Real.toNNReal (1-q)) x +
        c*(scalarCDFGradient β α q (Real.toNNReal (1-q)) x)^2)) q := by
    have hscalar : (1/2:ℝ)*varianceTilted c v f (generatorWeight c f) x *
        (β^2*(0-1)) = -(β^2/2)*
          (scalarCDFHessian β α q (Real.toNNReal (1-q)) x +
            c*(scalarCDFGradient β α q (Real.toNNReal (1-q)) x)^2) := by
      rw [hgen]
      ring
    simpa only [Function.comp_def, Pi.sub_apply, id_eq] using hd.congr_deriv hscalar
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hq.1 hq.2] with r hr
  exact congrFun (scalarCDFValue_constant_interval_heat β α ha h1 ha0 hb1.le hc
    ⟨hr.1.le,hr.2.le⟩ hconstant) x

end SKConstants.ParisiFullSupport
