module

public import QuantitativePaper.MovingTraceRate
public import QuantitativePaper.AbsoluteComparisonPowerNormalization

@[expose] public section

/-! Both genuine physical trace bounds, after exact temperature cancellation. -/
noncomputable section
open Set MeasureTheory Paper
namespace QuantitativePaper
set_option maxHeartbeats 1400000
variable {n : ℕ}

theorem absolute_trace_min_bound (hn : 0<n) (μ : ParisiMeasure)
    (β lam r : ℝ) (hβ : 0<β) (hs : lam/β∈Ioo (0:ℝ) 1)
    (hr : r∈Ioc (0:ℝ) 1) (hμ : μ∈scalarFloor (lam/β))
    (hmin : ∀ρ∈scalarFloor (lam/β), vectorMeasureFunctional n μ β (1-r) (lam/β) ≤
      vectorMeasureFunctional n ρ β (1-r) (lam/β)) :
    β*vectorInterpolationTraceError (n:=n) μ (lam/β) β (1-r) (by linarith [hr.1]) ≤
      min (1/((n:ℝ)*r*lam)) (2*((n:ℝ)*r)^(-1/2:ℝ)) := by
  have ht : 1-r<1:=by linarith [hr.1]
  have hN : 0<(n:ℝ):=Nat.cast_pos.mpr hn
  have hlam : 0<lam:=(div_pos_iff_of_pos_right hβ).mp hs.1
  have hf:=vector_free_trace_floor_bound hn μ (lam/β) β (1-r) hβ.ne' ht hs hμ hmin
  change vectorInterpolationTraceError (n:=n) μ (lam/β) β (1-r) ht.le ≤ _ at hf
  have hm:=vectorInterpolationTraceError_moving_rate hn μ (lam/β) β (1-r) hs hμ hβ.ne' ht hmin
  have hm' := hm.trans (mul_le_mul_of_nonneg_left
    ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num : (0:ℝ)≤2))
  have hf' := mul_le_mul_of_nonneg_left hf hβ.le
  have hm'' := mul_le_mul_of_nonneg_left hm' hβ.le
  have hnz : (n:ℝ)≠0:=hN.ne'
  have hfnorm : β*(1/(((n:ℝ)*((1-(1-r))*β^2))*(lam/β)))=1/((n:ℝ)*r*lam) := by
    field_simp [hβ.ne',hnz,hr.1.ne',hlam.ne']
    <;> ring
  have hnorm : β*(((n:ℝ)*((1-(1-r))*β^2))^(-1/2:ℝ))=((n:ℝ)*r)^(-1/2:ℝ) := by
    rw [show (n:ℝ)*((1-(1-r))*β^2)=((n:ℝ)*r)*β^2 by ring]
    simpa only [Real.rpow_zero,mul_one] using
      absolute_shell_power_normalization ((n:ℝ)*r) β 1 (-1/2) 0
        (mul_pos hN hr.1) hβ (by norm_num) (by norm_num)
  rw [hfnorm] at hf'
  have hmfinal : β*vectorInterpolationTraceError (n:=n) μ (lam/β) β (1-r) ht.le ≤
      2*((n:ℝ)*r)^(-1/2:ℝ) := by
    calc
      _ ≤ β*(2*(((n:ℝ)*((1-(1-r))*β^2))^(-1/2:ℝ))) := by convert hm'' using 1 <;> norm_num
      _ = 2*(β*(((n:ℝ)*((1-(1-r))*β^2))^(-1/2:ℝ))) := by ring
      _ = _ := by rw [hnorm]
  exact le_min hf' hmfinal

end QuantitativePaper
