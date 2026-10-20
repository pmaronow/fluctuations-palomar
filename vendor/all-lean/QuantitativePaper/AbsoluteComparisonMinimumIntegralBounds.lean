module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

@[expose] public section

/-! Integrability of the actual singular minimum error. Its reciprocal
branch is used away from zero; its square-root branch dominates at zero. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativePaper
set_option maxHeartbeats 1000000

def absoluteComparisonMinimumError (N l r : ℝ) : ℝ :=
  min (1/(N*r*l)) (2*(N*r)^(-(1:ℝ)/2))

theorem absoluteComparisonMinimumError_nonneg (N l r : ℝ)
    (hN : 0≤N) (hl : 0≤l) (hr : 0≤r) : 0≤absoluteComparisonMinimumError N l r :=
  le_min (by positivity) (by positivity)

theorem absoluteComparisonMinimumError_measurable (N l : ℝ) :
    Measurable (absoluteComparisonMinimumError N l) := by
  unfold absoluteComparisonMinimumError
  fun_prop

theorem absoluteComparisonMinimumError_intervalIntegrable (N l : ℝ)
    (hN : 0≤N) (hl : 0≤l) :
    IntervalIntegrable (absoluteComparisonMinimumError N l) volume 0 1 := by
  have hi : IntervalIntegrable (fun r : ℝ=>2*N^(-(1:ℝ)/2)*r^(-(1:ℝ)/2)) volume 0 1:=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  apply hi.mono_fun' (absoluteComparisonMinimumError_measurable N l).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with r hr
  have hr0 : 0≤r := (by simpa only [uIoc_of_le zero_le_one] using hr : r∈Ioc (0:ℝ) 1).1.le
  rw [Real.norm_eq_abs,abs_of_nonneg (absoluteComparisonMinimumError_nonneg N l r hN hl hr0)]
  unfold absoluteComparisonMinimumError
  calc
    _≤2*(N*r)^(-(1:ℝ)/2):=min_le_right _ _
    _=_:=by rw [Real.mul_rpow hN hr0];ring

theorem absoluteComparisonMinimumError_early_integral (N l : ℝ)
    (hN : 0<N) (hN1 : 1≤N) (hl : 0≤l) :
    (∫r in (0:ℝ)..1/N,absoluteComparisonMinimumError N l r)≤4/N := by
  have hs : Icc (0:ℝ) (1/N)⊆Icc 0 1:=by
    intro r hr
    exact ⟨hr.1,hr.2.trans (by rw [div_le_one hN];exact hN1)⟩
  have hi:IntervalIntegrable (absoluteComparisonMinimumError N l) volume 0 (1/N):=
    (absoluteComparisonMinimumError_intervalIntegrable N l hN.le hl).mono_set
      (by simpa only [uIcc_of_le (show (0:ℝ)≤1/N by positivity),uIcc_of_le zero_le_one] using hs)
  have hj:IntervalIntegrable (fun r : ℝ=>2*N^(-(1:ℝ)/2)*r^(-(1:ℝ)/2)) volume 0 (1/N):=
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  have hm:=intervalIntegral.integral_mono_on (show (0:ℝ)≤1/N by positivity) hi hj
    (fun r hr=>by
      unfold absoluteComparisonMinimumError
      calc _≤2*(N*r)^(-(1:ℝ)/2):=min_le_right _ _
           _=_:=by rw [Real.mul_rpow hN.le hr.1];ring)
  rw [intervalIntegral.integral_const_mul,integral_rpow (Or.inl (by norm_num))] at hm
  have he : (1/N)^((1:ℝ)/2)=N^(-(1:ℝ)/2):=by
    rw [one_div,Real.inv_rpow hN.le]
    rw [show -(1:ℝ)/2=-((1:ℝ)/2) by ring,Real.rpow_neg hN.le]
  have hp : N^(-(1:ℝ)/2)*N^(-(1:ℝ)/2)=1/N:=by
    rw [←Real.rpow_add hN]
    norm_num [Real.rpow_neg_one,one_div]
  norm_num at hm
  rw [show N⁻¹^((1:ℝ)/2)=N^(-(1:ℝ)/2) by simpa only [one_div] using he] at hm
  have hm' : (∫u in (0:ℝ)..1/N,absoluteComparisonMinimumError N l u)≤
      4*(N^(-(1:ℝ)/2)*N^(-(1:ℝ)/2)):=by
    convert hm using 1 <;> ring
  simpa only [hp,mul_one_div] using hm'

end QuantitativePaper
