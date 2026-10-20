module

public import QuantitativePaper.AbsoluteComparisonMinimumIntegral
public import FourPapersCommon.InterpolationPowerIntegral

@[expose] public section

/-! Integrating the actual singular comparison budget. The pointwise
defect estimate is explicit here; the final model comparison discharges it. -/
noncomputable section
open Set MeasureTheory FourPapersCommon
namespace QuantitativePaper
set_option maxHeartbeats 1200000

theorem absoluteComparisonIntegratedBudget_of_minimum_integral
    (N lam eta A B D : ℝ) (hN : 1≤N) (hlam : 0<lam) (heta : 0≤eta)
    (hA : 0≤A) (hB : 0≤B) (hD : 0≤D)
    (hmin : (∫r in (0:ℝ)..1,absoluteComparisonMinimumError N lam r)≤
      4/N+Real.log (2+N)/(N*lam))
    (f : ℝ→ℝ) (hf : IntervalIntegrable f volume 0 1)
    (hbound : ∀ᵐt∂volume.restrict (Ioo (0:ℝ) 1),
      f t≤min (1/(N*(1-t)*lam)) (2*(N*(1-t))^(-(1/2:ℝ)))+
        A*(N*(1-t))^(-(3/4:ℝ))*lam^(-(1/2:ℝ))+
        B*N^(-(2/3:ℝ))*(1-t)^(-(65/66:ℝ))*(D+lam^(-(1/3:ℝ))*eta^(1/11:ℝ))) :
    (∫t in (0:ℝ)..1,f t)≤4/N+Real.log (2+N)/(N*lam)+
      4*A*N^(-(3/4:ℝ))*lam^(-(1/2:ℝ))+
      66*B*N^(-(2/3:ℝ))*(D+lam^(-(1/3:ℝ))*eta^(1/11:ℝ)) := by
  have hNpos : 0<N:=zero_lt_one.trans_le hN
  let g0 : ℝ→ℝ:=fun t=>absoluteComparisonMinimumError N lam (1-t)
  let g1 : ℝ→ℝ:=fun t=>A*(N*(1-t))^(-(3/4:ℝ))*lam^(-(1/2:ℝ))
  let g2 : ℝ→ℝ:=fun t=>B*N^(-(2/3:ℝ))*(1-t)^(-(65/66:ℝ))*
    (D+lam^(-(1/3:ℝ))*eta^(1/11:ℝ))
  have hi0 : IntervalIntegrable g0 volume 0 1 := by
    simpa only [g0,sub_zero,sub_self] using
      ((absoluteComparisonMinimumError_intervalIntegrable N lam hNpos.le hlam.le).comp_sub_left 1).symm
  have he0 : (∫t in (0:ℝ)..1,g0 t)≤4/N+Real.log (2+N)/(N*lam) := by
    dsimp only [g0]
    rw [intervalIntegral.integral_comp_sub_left (absoluteComparisonMinimumError N lam) 1]
    simpa only [sub_zero,sub_self] using hmin
  obtain ⟨hi1base,he1base⟩:=interpolation_power_integral N (-(3/4:ℝ)) hNpos (by norm_num)
  have hi1 : IntervalIntegrable g1 volume 0 1:=
    (hi1base.const_mul A).mul_const _
  have he1 : (∫t in (0:ℝ)..1,g1 t)=4*A*N^(-(3/4:ℝ))*lam^(-(1/2:ℝ)) := by
    dsimp only [g1]
    rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul,he1base]
    norm_num <;> ring <;> simp
  obtain ⟨hi2base,he2base⟩:=interpolation_power_integral 1 (-(65/66:ℝ)) (by norm_num) (by norm_num)
  simp only [one_mul] at hi2base he2base
  have hi2 : IntervalIntegrable g2 volume 0 1:=
    (hi2base.const_mul (B*N^(-(2/3:ℝ)))).mul_const _
  have he2 : (∫t in (0:ℝ)..1,g2 t)=66*B*N^(-(2/3:ℝ))*
      (D+lam^(-(1/3:ℝ))*eta^(1/11:ℝ)) := by
    dsimp only [g2]
    rw [intervalIntegral.integral_mul_const,intervalIntegral.integral_const_mul,he2base]
    norm_num <;> ring <;> simp
  have hae : ∀ᵐt∂volume.restrict (Icc (0:ℝ) 1),f t≤g0 t+g1 t+g2 t := by
    rw [←restrict_Ioo_eq_restrict_Icc]
    simpa only [g0,g1,g2,absoluteComparisonMinimumError,
      show -(1:ℝ)/2=-(1/2:ℝ) by ring] using hbound
  have hh:=intervalIntegral.integral_mono_ae_restrict zero_le_one hf ((hi0.add hi1).add hi2) hae
  rw [intervalIntegral.integral_add (hi0.add hi1) hi2,
    intervalIntegral.integral_add hi0 hi1,he1,he2] at hh
  exact hh.trans (by linarith [he0])

theorem absolute_comparison_integrated_budget
    (N lam eta A B D : ℝ) (hN : 1≤N) (hlam : 0<lam) (heta : 0≤eta)
    (hA : 0≤A) (hB : 0≤B) (hD : 0≤D)
    (f : ℝ→ℝ) (hf : IntervalIntegrable f volume 0 1)
    (hbound : ∀ᵐt∂volume.restrict (Ioo (0:ℝ) 1),
      f t≤min (1/(N*(1-t)*lam)) (2*(N*(1-t))^(-(1/2:ℝ)))+
        A*(N*(1-t))^(-(3/4:ℝ))*lam^(-(1/2:ℝ))+
        B*N^(-(2/3:ℝ))*(1-t)^(-(65/66:ℝ))*(D+lam^(-(1/3:ℝ))*eta^(1/11:ℝ))) :
    (∫t in (0:ℝ)..1,f t)≤4/N+Real.log (2+N)/(N*lam)+
      4*A*N^(-(3/4:ℝ))*lam^(-(1/2:ℝ))+
      66*B*N^(-(2/3:ℝ))*(D+lam^(-(1/3:ℝ))*eta^(1/11:ℝ)) :=
  absoluteComparisonIntegratedBudget_of_minimum_integral N lam eta A B D hN hlam heta hA hB hD
    (absoluteComparisonMinimumError_integral N lam hN hlam) f hf hbound

end QuantitativePaper
