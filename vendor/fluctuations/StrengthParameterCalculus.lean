module

public import ConcreteComparisonStrength

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

def laplaceStrengthParameterDeriv (d lam r : ℝ) : ℝ :=
  laplaceComparisonShape (lam*r/d^3) +
    (lam*r/d^3)*laplaceComparisonShapeDeriv (lam*r/d^3)

theorem laplaceStrength_parameter_hasDerivAt (d lam r : ℝ) :
    HasDerivAt (fun l => laplaceComparisonStrength d l r)
      (laplaceStrengthParameterDeriv d lam r) lam := by
  have ht := ((hasDerivAt_id lam).mul_const r).div_const (d^3)
  have hd := (hasDerivAt_id lam).mul
    ((laplaceComparisonShape_hasDerivAt (lam*r/d^3)).comp lam ht)
  convert hd using 1
  · rfl
  · unfold laplaceStrengthParameterDeriv
    simp only [Function.comp_apply, id_eq]
    ring

theorem laplaceStrengthParameterDeriv_eq (d lam r : ℝ) :
    laplaceStrengthParameterDeriv d lam r =
      if lam*r/d^3 ≤ 1 then 1 else 1/(lam*r/d^3) := by
  unfold laplaceStrengthParameterDeriv
  by_cases ht : lam*r/d^3 ≤ 1
  · simp [laplaceComparisonShape, laplaceComparisonShapeDeriv, ht]
  · have htpos : 0 < lam*r/d^3 := lt_trans zero_lt_one (lt_of_not_ge ht)
    simp only [laplaceComparisonShape,laplaceComparisonShapeDeriv,if_neg ht]
    field_simp
    ring

theorem laplaceStrengthParameterDeriv_mem (d lam r : ℝ) :
    laplaceStrengthParameterDeriv d lam r ∈ Ioc (0:ℝ) 1 := by
  rw [laplaceStrengthParameterDeriv_eq]
  split_ifs with ht
  · norm_num
  · have htpos : 0 < lam*r/d^3 := lt_trans zero_lt_one (lt_of_not_ge ht)
    exact ⟨one_div_pos.mpr htpos,(div_le_one htpos).mpr (lt_of_not_ge ht).le⟩

theorem laplaceStrengthParameterDeriv_le_shape (d lam r : ℝ) :
    laplaceStrengthParameterDeriv d lam r ≤ laplaceComparisonShape (lam*r/d^3) := by
  rw [laplaceStrengthParameterDeriv_eq]
  by_cases ht : lam*r/d^3 ≤ 1
  · simp [laplaceComparisonShape, ht]
  · simp only [if_neg ht,laplaceComparisonShape]
    have htpos : 0 < lam*r/d^3 := lt_trans zero_lt_one (lt_of_not_ge ht)
    apply div_le_div_of_nonneg_right _ htpos.le
    have hh := Real.log_pos (lt_of_not_ge ht)
    linarith

theorem laplaceStrength_logParameterDeriv_le (d r : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    lam*laplaceStrengthParameterDeriv d lam r ≤ laplaceComparisonStrength d lam r := by
  exact mul_le_mul_of_nonneg_left (laplaceStrengthParameterDeriv_le_shape d lam r) hlam

theorem laplaceStrengthParameterDeriv_continuous_radius (d lam : ℝ) :
    Continuous (laplaceStrengthParameterDeriv d lam) := by
  have ht : Continuous (fun r : ℝ => lam*r/d^3) :=
    (continuous_const.mul continuous_id).div_const _
  exact (laplaceComparisonShape_contDiff.continuous.comp ht).add
    (ht.mul (laplaceComparisonShapeDeriv_continuous.comp ht))

theorem laplaceStrength_parameter_lipschitz (d r : ℝ) :
    LipschitzWith 1 (fun lam => laplaceComparisonStrength d lam r) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun lam => (laplaceStrength_parameter_hasDerivAt d lam r).differentiableAt)
  intro lam
  rw [(laplaceStrength_parameter_hasDerivAt d lam r).deriv]
  change ‖laplaceStrengthParameterDeriv d lam r‖ ≤ (1:ℝ)
  rw [Real.norm_eq_abs,abs_of_pos (laplaceStrengthParameterDeriv_mem d lam r).1]
  exact (laplaceStrengthParameterDeriv_mem d lam r).2

theorem laplaceStrength_parameter_displacement (d r lam lam' : ℝ) :
    |laplaceComparisonStrength d lam r-laplaceComparisonStrength d lam' r| ≤ |lam-lam'| := by
  simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using
    (laplaceStrength_parameter_lipschitz d r).dist_le_mul lam lam'

theorem laplaceStrength_parameter_monotone (d r : ℝ) :
    Monotone (fun lam => laplaceComparisonStrength d lam r) := by
  apply monotone_of_deriv_nonneg
    (fun lam => (laplaceStrength_parameter_hasDerivAt d lam r).differentiableAt)
  intro lam
  rw [(laplaceStrength_parameter_hasDerivAt d lam r).deriv]
  exact (laplaceStrengthParameterDeriv_mem d lam r).1.le

theorem laplaceComparisonStrength_zero (d r : ℝ) :
    laplaceComparisonStrength d 0 r = 0 := by
  simp [laplaceComparisonStrength,comparisonStrength]

theorem laplaceComparisonStrength_nonneg (d r : ℝ) {lam : ℝ} (hlam : 0 ≤ lam) :
    0 ≤ laplaceComparisonStrength d lam r := by
  exact mul_nonneg hlam (laplaceComparisonShape_pos _).le

theorem laplaceComparisonStrength_monotonicities_nonneg {d lam : ℝ}
    (hd : d ≠ 0) (hlam : 0 ≤ lam) :
    AntitoneOn (laplaceComparisonStrength d lam) (Icc (0:ℝ) 1) ∧
      MonotoneOn (fun r => laplaceComparisonStrength d lam r*r) (Icc (0:ℝ) 1) := by
  rcases eq_or_lt_of_le hlam with he|he
  · subst lam
    constructor
    · intro u hu v hv huv
      simp only [laplaceComparisonStrength_zero]
      exact le_rfl
    · intro u hu v hv huv
      simp only [laplaceComparisonStrength_zero, zero_mul]
      exact le_rfl
  · exact laplaceComparisonStrength_monotonicities hd he le_rfl

end OAI.SKFluctuations.LaplaceWindowFormalization
