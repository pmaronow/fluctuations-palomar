module

public import SKConstants.ScalarDeterministicWeightedPaths
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

theorem scalarStieltjesWeightedPath_difference_le
    (f : StieltjesFunction ℝ) (hf : Continuous f) (T : ℝ≥0)
    (B C : ScalarContinuousPath T) (t : Icc (0 : ℝ) (T : ℝ)) :
    |scalarStieltjesWeightedPath f hf T B t - scalarStieltjesWeightedPath f hf T C t| ≤
      (|f t| + (f t-f 0))*‖B-C‖ := by
  have hBC : Continuous (IccExtend T.coe_nonneg B - IccExtend T.coe_nonneg C) :=
    B.continuous.Icc_extend'.sub C.continuous.Icc_extend'
  have hInt : IntervalIntegrable (IccExtend T.coe_nonneg B) f.measure 0 t :=
    (B.continuous.Icc_extend'.continuousOn.integrableOn_compact isCompact_uIcc).intervalIntegrable
  have hInt' : IntervalIntegrable (IccExtend T.coe_nonneg C) f.measure 0 t :=
    (C.continuous.Icc_extend'.continuousOn.integrableOn_compact isCompact_uIcc).intervalIntegrable
  have he : scalarStieltjesWeightedPath f hf T B t - scalarStieltjesWeightedPath f hf T C t =
      f t*(B t-C t) - ∫ s in (0 : ℝ)..(t : ℝ),
        (IccExtend T.coe_nonneg B s-IccExtend T.coe_nonneg C s) ∂f.measure := by
    rw [intervalIntegral.integral_sub hInt hInt']
    dsimp [scalarStieltjesWeightedPath]
    ring
  have hmass : (f.measure (Ioc (0 : ℝ) (t : ℝ))).toReal = f t-f 0 := by
    rw [f.measure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr (f.mono t.property.1))]
  have hb : ‖∫ s in (0 : ℝ)..(t : ℝ),
      (IccExtend T.coe_nonneg B s-IccExtend T.coe_nonneg C s) ∂f.measure‖ ≤
        (f t-f 0)*‖B-C‖ := by
    rw [intervalIntegral.integral_of_le t.property.1]
    have hbound := norm_setIntegral_le_of_norm_le_const
      (f := fun s => IccExtend T.coe_nonneg B s-IccExtend T.coe_nonneg C s)
      (C := ‖B-C‖) (μ := f.measure) (s := Ioc (0 : ℝ) (t : ℝ))
      (by rw [f.measure_Ioc]; exact ENNReal.ofReal_lt_top)
      (fun s hs => show ‖(B-C) (projIcc 0 (T : ℝ) T.coe_nonneg s)‖ ≤ ‖B-C‖ from
        (B-C).norm_coe_le_norm _)
    simpa only [Measure.real_def, hmass, mul_comm] using hbound

  rw [he]
  have ht : ‖B t-C t‖ ≤ ‖B-C‖ := (B-C).norm_coe_le_norm t
  have hm := mul_le_mul_of_nonneg_left ht (abs_nonneg (f t))
  have hsum := norm_sub_le (f t*(B t-C t))
    (∫ s in (0 : ℝ)..(t : ℝ), (IccExtend T.coe_nonneg B s-IccExtend T.coe_nonneg C s) ∂f.measure)
  simp only [Real.norm_eq_abs, norm_mul] at hsum hm hb
  nlinarith

def scalarStieltjesPathBound (f : StieltjesFunction ℝ) (T : ℝ≥0) : ℝ :=
  |f 0| + |f T| + (f T-f 0)

theorem scalarStieltjesPathBound_nonneg (f : StieltjesFunction ℝ) (T : ℝ≥0) :
    0 ≤ scalarStieltjesPathBound f T := by
  unfold scalarStieltjesPathBound
  have hm := f.mono T.coe_nonneg
  positivity

theorem scalarStieltjesWeightedPath_norm_difference_le
    (f : StieltjesFunction ℝ) (hf : Continuous f) (T : ℝ≥0)
    (B C : ScalarContinuousPath T) :
    ‖scalarStieltjesWeightedPath f hf T B-scalarStieltjesWeightedPath f hf T C‖ ≤
      scalarStieltjesPathBound f T * ‖B-C‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (scalarStieltjesPathBound_nonneg f T)
    (norm_nonneg (B-C)))).mpr
  intro t
  have ht := scalarStieltjesWeightedPath_difference_le f hf T B C t
  have h0 := f.mono t.property.1
  have hT := f.mono t.property.2
  have ha : |f t| ≤ |f 0|+|f T| := by
    rw [abs_le]
    constructor <;> linarith [le_abs_self (f 0), neg_le_abs (f 0),
      le_abs_self (f T), neg_le_abs (f T)]
  have hbudget : |f t|+(f t-f 0) ≤ scalarStieltjesPathBound f T := by
    unfold scalarStieltjesPathBound
    linarith
  exact ht.trans (mul_le_mul_of_nonneg_right hbudget (norm_nonneg (B-C)))

theorem scalarTwoDriverWeightedPath_norm_difference_le
    (f g : StieltjesFunction ℝ) (hf : Continuous f) (hg : Continuous g) (T : ℝ≥0)
    (B C D E : ScalarContinuousPath T) :
    ‖scalarTwoDriverWeightedPath f g hf hg T (B,D)-
      scalarTwoDriverWeightedPath f g hf hg T (C,E)‖ ≤
    scalarStieltjesPathBound f T * ‖B-C‖ + scalarStieltjesPathBound g T * ‖D-E‖ := by
  have he : scalarTwoDriverWeightedPath f g hf hg T (B,D)-
      scalarTwoDriverWeightedPath f g hf hg T (C,E) =
    -(scalarStieltjesWeightedPath f hf T B-scalarStieltjesWeightedPath f hf T C) +
      (scalarStieltjesWeightedPath g hg T D-scalarStieltjesWeightedPath g hg T E) := by
    unfold scalarTwoDriverWeightedPath
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  rw [norm_neg]
  exact add_le_add (scalarStieltjesWeightedPath_norm_difference_le f hf T B C)
    (scalarStieltjesWeightedPath_norm_difference_le g hg T D E)

end SKConstants
