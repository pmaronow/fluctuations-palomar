module

public import ComparisonActualGeneralLocalThermalIntegralBridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory
open scoped Topology
set_option autoImplicit false

theorem normalized_local_thermal_factor_residual_integral_bound
    {d Ccut C a : ℝ} (hd : 0 < d) (hCcut : 0 ≤ Ccut)
    (D Eta R : ℝ → ℝ)
    (hD : IntervalIntegrable D volume 0 (Ccut*d))
    (hEta : IntervalIntegrable Eta volume 0 (Ccut*d))
    (hR : IntervalIntegrable (fun u => |R u|) volume 0 (Ccut*d))
    (hpoint : ∀u∈Icc (0:ℝ) (Ccut*d),
      |R u| ≤ C*(d^4+d^2*D u+d*(∫v in 0..Ccut*d,D v)+a*d^3+d^3*Eta u)) :
    (∫u in 0..Ccut*d, |R u|)/d^4 ≤
      C*(Ccut*d+(Ccut+1)*((∫u in 0..Ccut*d,D u)/d^2)+
        Ccut*a+(∫u in 0..Ccut*d,Eta u)/d) := by
  let I := ∫u in 0..Ccut*d,D u
  let J := ∫u in 0..Ccut*d,Eta u
  let F := fun u => D u+d*Eta u
  have hF : IntervalIntegrable F volume 0 (Ccut*d) := hD.add (hEta.const_mul d)
  have HF : (∫u in 0..Ccut*d,F u)=I+d*J := by
    simp only [F,intervalIntegral.integral_add hD (hEta.const_mul d),
      intervalIntegral.integral_const_mul,I,J]
  have H := integrated_local_error_bound (mul_nonneg hCcut hd.le) F R hF hR
    (A:=C*(d^4+d*I+a*d^3)) (B:=C*d^2) (by
      intro u hu
      have HH:=hpoint u hu
      dsimp [F,I]
      convert HH using 1; ring)
  have hp : 0 < d^4:=pow_pos hd _
  have HH:=div_le_div_of_nonneg_right H hp.le
  rw [HF] at HH
  convert HH using 1
  simp only [sub_zero]
  dsimp [I,J]
  field_simp; ring

theorem local_thermal_factor_residual_integral_tendsto_zero
    {Ccut C : ℝ} (hCcut : 0 ≤ Ccut)
    (d a : ℕ → ℝ) (D Eta R : ℕ → ℝ → ℝ)
    (hd : ∀n, 0 < d n)
    (hdlim : Tendsto d atTop (𝓝 0))
    (halim : Tendsto a atTop (𝓝 0))
    (hIlim : Tendsto
      (fun n => (∫u in 0..Ccut*d n,D n u)/(d n)^2) atTop (𝓝 0))
    (hJlim : Tendsto
      (fun n => (∫u in 0..Ccut*d n,Eta n u)/(d n)) atTop (𝓝 0))
    (hD : ∀n, IntervalIntegrable (D n) volume 0 (Ccut*d n))
    (hEta : ∀n, IntervalIntegrable (Eta n) volume 0 (Ccut*d n))
    (hR : ∀n, IntervalIntegrable (fun u => |R n u|) volume 0 (Ccut*d n))
    (hpoint : ∀n,∀u∈Icc (0:ℝ) (Ccut*d n),
      |R n u| ≤ C*((d n)^4+(d n)^2*D n u+
        d n*(∫v in 0..Ccut*d n,D n v)+a n*(d n)^3+
        (d n)^3*Eta n u)) :
    Tendsto (fun n => (∫u in 0..Ccut*d n, |R n u|)/(d n)^4)
      atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun n => C*(Ccut*d n+(Ccut+1)*
        ((∫u in 0..Ccut*d n,D n u)/(d n)^2)+Ccut*a n+
        (∫u in 0..Ccut*d n,Eta n u)/(d n))) atTop (𝓝 0) := by
    have H := ((((hdlim.const_mul Ccut).add (hIlim.const_mul (Ccut+1))).add
      (halim.const_mul Ccut)).add hJlim).const_mul C
    simpa only [mul_zero,zero_add,add_zero] using H
  apply squeeze_zero
  · intro n
    exact div_nonneg
      (intervalIntegral.integral_nonneg (mul_nonneg hCcut (hd n).le)
        (fun _ _ => abs_nonneg _)) (pow_nonneg (hd n).le _)
  · intro n
    exact normalized_local_thermal_factor_residual_integral_bound (hd n) hCcut
      (D n) (Eta n) (R n) (hD n) (hEta n) (hR n) (hpoint n)
  · exact hupper

end OAI.SKFluctuations.Cavity
