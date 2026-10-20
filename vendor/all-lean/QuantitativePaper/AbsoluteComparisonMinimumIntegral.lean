module

public import QuantitativePaper.AbsoluteComparisonMinimumIntegralBounds

@[expose] public section

/-! The literal integrable minimum envelope and its logarithmic bound. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativePaper
set_option maxHeartbeats 1000000

theorem absoluteComparisonMinimumError_late_integral (N l : ℝ)
    (hN : 0<N) (hN1 : 1≤N) (hl : 0<l) :
    (∫r in (1/N:ℝ)..1,absoluteComparisonMinimumError N l r)≤Real.log (2+N)/(N*l) := by
  have ha : 0<1/N := by positivity
  have ha1 : 1/N≤(1:ℝ) := by rw [div_le_one hN];exact hN1
  have hG : (fun r : ℝ=>1/(N*r*l))=(fun r : ℝ=>1/(N*l)*(1/r)):=by
    ext r
    simp only [one_div,mul_inv_rev]
    ring
  have hir : IntervalIntegrable (fun r : ℝ=>1/r) volume (1/N) 1 := by
    apply intervalIntegral.intervalIntegrable_one_div
    · intro r hr
      have hr' : r∈Icc (1/N:ℝ) 1 := by simpa only [uIcc_of_le ha1] using hr
      exact (ha.trans_le hr'.1).ne'
    · exact continuous_id.continuousOn
  have hGint : IntervalIntegrable (fun r : ℝ=>1/(N*r*l)) volume (1/N) 1:=by
    rw [hG]
    exact hir.const_mul _
  have hmin : IntervalIntegrable (absoluteComparisonMinimumError N l) volume (1/N) 1:=
    (absoluteComparisonMinimumError_intervalIntegrable N l hN.le hl.le).mono_set (by
      simp only [uIcc_of_le ha1,uIcc_of_le zero_le_one]
      exact fun r hr=>⟨ha.le.trans hr.1,hr.2⟩)
  have hm:=intervalIntegral.integral_mono_on ha1 hmin hGint (fun r hr=>min_le_left _ _)
  rw [hG,intervalIntegral.integral_const_mul,integral_one_div_of_pos ha zero_lt_one] at hm
  simp only [one_div_one_div] at hm
  calc
    _≤1/(N*l)*Real.log N:=hm
    _≤1/(N*l)*Real.log (2+N):=mul_le_mul_of_nonneg_left
      (Real.log_le_log hN (by linarith)) (by positivity)
    _=_:=by ring

theorem absoluteComparisonMinimumError_integral (N l : ℝ)
    (hN1 : 1≤N) (hl : 0<l) :
    (∫r in (0:ℝ)..1,absoluteComparisonMinimumError N l r)≤
      4/N+Real.log (2+N)/(N*l) := by
  have hN : 0<N:=lt_of_lt_of_le zero_lt_one hN1
  have h01:=absoluteComparisonMinimumError_intervalIntegrable N l hN.le hl.le
  have ha0 : (0:ℝ)≤1/N:=by positivity
  have ha1 : 1/N≤(1:ℝ):=by rw [div_le_one hN];exact hN1
  have hi : IntervalIntegrable (absoluteComparisonMinimumError N l) volume 0 (1/N):=
    h01.mono_set (by simp only [uIcc_of_le ha0,uIcc_of_le zero_le_one];exact
      fun r hr=>⟨hr.1,hr.2.trans ha1⟩)
  have hj : IntervalIntegrable (absoluteComparisonMinimumError N l) volume (1/N) 1:=
    h01.mono_set (by simp only [uIcc_of_le ha1,uIcc_of_le zero_le_one];exact
      fun r hr=>⟨ha0.trans hr.1,hr.2⟩)
  rw [←intervalIntegral.integral_add_adjacent_intervals hi hj]
  exact add_le_add (absoluteComparisonMinimumError_early_integral N l hN hN1 hl.le)
    (absoluteComparisonMinimumError_late_integral N l hN hN1 hl)

theorem absoluteComparisonMinimumError_time_integral (N l : ℝ)
    (hN1 : 1≤N) (hl : 0<l) :
    (∫t in (0:ℝ)..1,min (1/(N*(1-t)*l)) (2*(N*(1-t))^(-(1:ℝ)/2)))≤
      4/N+Real.log (2+N)/(N*l) := by
  change (∫t in (0:ℝ)..1,absoluteComparisonMinimumError N l (1-t))≤_
  rw [intervalIntegral.integral_comp_sub_left]
  norm_num
  exact absoluteComparisonMinimumError_integral N l hN1 hl

theorem absoluteComparisonMinimumError_time_intervalIntegrable (N l : ℝ)
    (hN : 0≤N) (hl : 0≤l) :
    IntervalIntegrable (fun t : ℝ=>min (1/(N*(1-t)*l))
      (2*(N*(1-t))^(-(1:ℝ)/2))) volume 0 1 := by
  have hi:=(absoluteComparisonMinimumError_intervalIntegrable N l hN hl).comp_sub_left 1
  simpa only [sub_zero,sub_self,absoluteComparisonMinimumError] using hi.symm

end QuantitativePaper
