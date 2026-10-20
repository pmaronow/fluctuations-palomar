module

public import ComparisonActualGeneralTargetLocalThermalModulus

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory
open scoped Topology
set_option autoImplicit false

theorem integrated_local_error_bound
    {l r A B : ℝ} (hlr : l ≤ r)
    (D R : ℝ → ℝ)
    (hD : IntervalIntegrable D volume l r)
    (hR : IntervalIntegrable (fun u => |R u|) volume l r)
    (hpoint : ∀u∈Icc l r, |R u| ≤ A+B*D u) :
    (∫u in l..r, |R u|) ≤ A*(r-l)+B*(∫u in l..r,D u) := by
  have hbound : IntervalIntegrable (fun u => A+B*D u) volume l r :=
    intervalIntegrable_const.add (hD.const_mul B)
  have H:=intervalIntegral.integral_mono_on hlr hR hbound hpoint
  simpa only [intervalIntegral.integral_add intervalIntegrable_const (hD.const_mul B),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    smul_eq_mul, mul_comm A] using H

theorem normalized_local_thermal_residual_integral_bound
    {d Ccut C a : ℝ} (hd : 0 < d) (hCcut : 0 ≤ Ccut)
    (D R : ℝ → ℝ)
    (hD : IntervalIntegrable D volume 0 (Ccut*d))
    (hR : IntervalIntegrable (fun u => |R u|) volume 0 (Ccut*d))
    (hpoint : ∀u∈Icc (0:ℝ) (Ccut*d),
      |R u| ≤ C*(d^4+d^2*D u+d*(∫v in 0..Ccut*d,D v)+a*d^3)) :
    (∫u in 0..Ccut*d, |R u|)/d^4 ≤
      C*(Ccut*d+(Ccut+1)*((∫u in 0..Ccut*d,D u)/d^2)+Ccut*a) := by
  let I := ∫u in 0..Ccut*d,D u
  have H := integrated_local_error_bound (mul_nonneg hCcut hd.le) D R hD hR
    (A:=C*(d^4+d*I+a*d^3)) (B:=C*d^2) (by
      intro u hu
      have HH:=hpoint u hu
      dsimp only [I]
      convert HH using 1; ring)
  have hp : 0 < d^4:=pow_pos hd _
  have HH:=div_le_div_of_nonneg_right H hp.le
  convert HH using 1
  simp only [sub_zero]
  dsimp [I]
  field_simp; ring

theorem local_thermal_residual_integral_tendsto_zero
    {Ccut C : ℝ} (hCcut : 0 ≤ Ccut)
    (d a : ℕ → ℝ) (D R : ℕ → ℝ → ℝ)
    (hd : ∀n, 0 < d n)
    (hdlim : Tendsto d atTop (𝓝 0))
    (halim : Tendsto a atTop (𝓝 0))
    (hIlim : Tendsto
      (fun n => (∫u in 0..Ccut*d n,D n u)/(d n)^2) atTop (𝓝 0))
    (hD : ∀n, IntervalIntegrable (D n) volume 0 (Ccut*d n))
    (hR : ∀n, IntervalIntegrable (fun u => |R n u|) volume 0 (Ccut*d n))
    (hpoint : ∀n,∀u∈Icc (0:ℝ) (Ccut*d n),
      |R n u| ≤ C*((d n)^4+(d n)^2*D n u+
        d n*(∫v in 0..Ccut*d n,D n v)+a n*(d n)^3)) :
    Tendsto (fun n => (∫u in 0..Ccut*d n, |R n u|)/(d n)^4)
      atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun n => C*(Ccut*d n+(Ccut+1)*
        ((∫u in 0..Ccut*d n,D n u)/(d n)^2)+Ccut*a n)) atTop (𝓝 0) := by
    have H := (((hdlim.const_mul Ccut).add (hIlim.const_mul (Ccut+1))).add
      (halim.const_mul Ccut)).const_mul C
    simpa only [mul_zero,zero_add,add_zero] using H
  apply squeeze_zero
  · intro n
    exact div_nonneg
      (intervalIntegral.integral_nonneg (mul_nonneg hCcut (hd n).le)
        (fun _ _ => abs_nonneg _)) (pow_nonneg (hd n).le _)
  · intro n
    exact normalized_local_thermal_residual_integral_bound (hd n) hCcut (D n) (R n)
      (hD n) (hR n) (hpoint n)
  · exact hupper

end OAI.SKFluctuations.Cavity
