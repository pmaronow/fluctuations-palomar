module

public import SKConstants.ParisiCDFCompactRate

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

theorem scalarCDFValue_integral_time_jets (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T a b : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (ha0 : 0 ≤ a)
    (hab : a ≤ b) (hbT : b ≤ T) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (scalarCDFValue β α b (Real.toNNReal (1-b))) x -
      iteratedDeriv n (scalarCDFValue β α a (Real.toNNReal (1-a))) x =
        ∫ r in a..b, iteratedDeriv n (compactCDFValueRate β α T r) x := by
  have htime : (fun z => scalarCDFValue β α b (Real.toNNReal (1-b)) z -
      scalarCDFValue β α a (Real.toNNReal (1-a)) z) =
      fun z => ∫ r in a..b, compactCDFValueRate β α T r z := by
    funext z
    rw [scalarCDFValue_integral_time_equation β α ha h1 hβ ha0 hab
      (hbT.trans_lt hT1) z]
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc a b := by simpa only [uIcc_of_le hab] using hr
    exact (compactCDFValueRate_eq β α ha hT1.le
      ⟨ha0.trans hr'.1, hr'.2.trans hbT⟩ z).symm
  have H := congrArg (fun f : ℝ → ℝ => iteratedDeriv n f x) htime
  rw [(compactCDFValueRate_family β α ha h1 hβ hT0 hT1).iteratedDeriv_integral] at H
  have hb0 : 0 ≤ b := ha0.trans hab
  have hfa := (scalarCDFValue_regularDatum β α ha hβ ha0
    (hab.trans hbT |>.trans_lt hT1)).smooth
  have hfb := (scalarCDFValue_regularDatum β α ha hβ hb0 (hbT.trans_lt hT1)).smooth
  have hda := (hfa.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt (x := x)
  have hdb := (hfb.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt (x := x)
  simpa only [iteratedDeriv_fun_sub hdb hda] using H

theorem scalarCDFValue_time_derivative_right_jets (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {T q : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (hq0 : 0 ≤ q) (hqT : q < T)
    (n : ℕ) (x : ℝ) :
    HasDerivWithinAt
      (fun r => iteratedDeriv n (scalarCDFValue β α r (Real.toNNReal (1-r))) x)
      (iteratedDeriv n (compactCDFValueRate β α T q) x) (Ioi q) q := by
  have hR := compactCDFValueRate_family β α ha h1 hβ hT0 hT1
  have hm : Measurable (fun r => iteratedDeriv n (compactCDFValueRate β α T r) x) :=
    measurable_fixed_space (F := fun r => iteratedDeriv n (compactCDFValueRate β α T r))
      (hR.iteratedDeriv n).measurable x
  have HD := intervalIntegral.integral_hasDerivWithinAt_right
    (a := q) (b := q) (s := Ici q) (t := Ioi q) IntervalIntegrable.refl
    hm.stronglyMeasurable.stronglyMeasurableAtFilter
    (compactCDFValueRate_right_smooth β α ha h1 hβ hT0 hT1 n q x)
  have H := (HD.mono Ioi_subset_Ici_self).add_const
    (iteratedDeriv n (scalarCDFValue β α q (Real.toNNReal (1-q))) x)
  apply H.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hqT)] with r hr hrT
    have HE := scalarCDFValue_integral_time_jets β α ha h1 hβ hT0 hT1 hq0
      hr.le hrT.le n x
    linarith [HE]
  · simp only [intervalIntegral.integral_same, zero_add]

theorem scalarCDFValue_time_derivative_right (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1 = 1) (hβ : β ≠ 0)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (x : ℝ) :
    HasDerivWithinAt (fun r => scalarCDFValue β α r (Real.toNNReal (1-r)) x)
      (scalarCDFValueRate β α q x) (Ioi q) q := by
  let T := (q+1)/2
  have hT0 : 0 ≤ T := by dsimp [T]; linarith
  have hT1 : T < 1 := by dsimp [T]; linarith
  have hqT : q < T := by dsimp [T]; linarith
  have H := scalarCDFValue_time_derivative_right_jets β α ha h1 hβ hT0 hT1 hq0 hqT 0 x
  simpa only [iteratedDeriv_zero,
    compactCDFValueRate_eq β α ha hT1.le ⟨hq0,hqT.le⟩ x] using H

end SKConstants.ParisiFullSupport
