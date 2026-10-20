module

public import ComparisonActualGeneralFinitePowerFamilyResidualIntegral

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory
open scoped Topology BigOperators
set_option autoImplicit false

theorem integrated_local_error_bound_Ioo
    {l r A B : ℝ} (hlr : l ≤ r)
    (D R : ℝ → ℝ)
    (hD : IntervalIntegrable D volume l r)
    (hR : IntervalIntegrable (fun u => |R u|) volume l r)
    (hpoint : ∀u∈Ioo l r, |R u| ≤ A+B*D u) :
    (∫u in l..r, |R u|) ≤ A*(r-l)+B*(∫u in l..r,D u) := by
  have hbound : IntervalIntegrable (fun u => A+B*D u) volume l r :=
    intervalIntegrable_const.add (hD.const_mul B)
  have H:=intervalIntegral.integral_mono_on_of_le_Ioo hlr hR hbound hpoint
  simpa only [intervalIntegral.integral_add intervalIntegrable_const (hD.const_mul B),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    smul_eq_mul, mul_comm A] using H

theorem normalized_local_thermal_factor_residual_integral_bound_Ioo
    {d Ccut C a : ℝ} (hd : 0 < d) (hCcut : 0 ≤ Ccut)
    (D Eta R : ℝ → ℝ)
    (hD : IntervalIntegrable D volume 0 (Ccut*d))
    (hEta : IntervalIntegrable Eta volume 0 (Ccut*d))
    (hR : IntervalIntegrable (fun u => |R u|) volume 0 (Ccut*d))
    (hpoint : ∀u∈Ioo (0:ℝ) (Ccut*d),
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
  have H := integrated_local_error_bound_Ioo (mul_nonneg hCcut hd.le) F R hF hR
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

theorem finite_power_family_local_residual_integral_Ioo_tendsto_zero
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (k : ι → ℕ) (K c : ι → ℝ)
    {Ccut C : ℝ} (hCcut : 0 ≤ Ccut)
    (d a site : ℕ → ℝ) (D R : ℕ → ℝ → ℝ)
    (Eta : ι → ℕ → ℝ → ℝ)
    (hd : ∀n, 0 < d n) (hsite : ∀n, 0 ≤ site n)
    (hdlim : Tendsto d atTop (𝓝 0))
    (halim : Tendsto a atTop (𝓝 0))
    (hIlim : Tendsto
      (fun n => (∫u in 0..Ccut*d n,D n u)/(d n)^2) atTop (𝓝 0))
    (hsitelim : Tendsto (fun n => site n/d n) atTop (𝓝 0))
    (hD : ∀n, IntervalIntegrable (D n) volume 0 (Ccut*d n))
    (hR : ∀n, IntervalIntegrable (fun u => |R n u|) volume 0 (Ccut*d n))
    (hDpos : ∀n,∀u∈Icc (0:ℝ) (Ccut*d n),0≤D n u)
    (hK : ∀j∈s,0≤K j)
    (hEta : ∀j∈s,∀n, IntervalIntegrable (Eta j n) volume 0 (Ccut*d n))
    (hEtapos : ∀j∈s,∀n,∀u∈Icc (0:ℝ) (Ccut*d n),0≤Eta j n u)
    (hpow : ∀j∈s,∀n,∀u∈Icc (0:ℝ) (Ccut*d n),
      (Eta j n u)^(k j+1) ≤ K j*(D n u+site n)/d n)
    (hpoint : ∀n,∀u∈Ioo (0:ℝ) (Ccut*d n),
      |R n u| ≤ C*((d n)^4+(d n)^2*D n u+
        d n*(∫v in 0..Ccut*d n,D n v)+a n*(d n)^3+
        (d n)^3*(∑j∈s,c j*Eta j n u))) :
    Tendsto (fun n => (∫u in 0..Ccut*d n, |R n u|)/(d n)^4)
      atTop (𝓝 0) := by
  let EtaSum : ℕ → ℝ → ℝ := fun n u => ∑j∈s,c j*Eta j n u
  have hEtaSum (n : ℕ) :
      IntervalIntegrable (EtaSum n) volume 0 (Ccut*d n) := by
    convert IntervalIntegrable.sum s
      (fun j hj => (hEta j hj n).const_mul (c j)) using 1
    ext u
    simp only [EtaSum, Finset.sum_apply]
  have hJlim : Tendsto
      (fun n => (∫u in 0..Ccut*d n,EtaSum n u)/d n) atTop (𝓝 0) :=
    finite_power_family_normalized_integral_tendsto_zero s k K c hCcut
      d site D Eta hd hsite hIlim hsitelim hD hDpos hK hEta hEtapos hpow
  have hupper : Tendsto
      (fun n => C*(Ccut*d n+(Ccut+1)*
        ((∫u in 0..Ccut*d n,D n u)/(d n)^2)+Ccut*a n+
        (∫u in 0..Ccut*d n,EtaSum n u)/d n)) atTop (𝓝 0) := by
    have H := ((((hdlim.const_mul Ccut).add (hIlim.const_mul (Ccut+1))).add
      (halim.const_mul Ccut)).add hJlim).const_mul C
    simpa only [mul_zero,zero_add,add_zero] using H
  apply squeeze_zero
  · intro n
    exact div_nonneg
      (intervalIntegral.integral_nonneg (mul_nonneg hCcut (hd n).le)
        (fun _ _ => abs_nonneg _)) (pow_nonneg (hd n).le _)
  · intro n
    exact normalized_local_thermal_factor_residual_integral_bound_Ioo
      (hd n) hCcut (D n) (EtaSum n) (R n) (hD n)
      (hEtaSum n) (hR n) (by simpa only [EtaSum] using hpoint n)
  · exact hupper

theorem finite_power_family_separate_coefficients_residual_integral_Ioo_tendsto_zero
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (k : ι → ℕ) (K c : ι → ℝ)
    {Ccut C : ℝ} (hCcut : 0 ≤ Ccut) (hC : 0 < C)
    (d a site : ℕ → ℝ) (D R : ℕ → ℝ → ℝ)
    (Eta : ι → ℕ → ℝ → ℝ)
    (hd : ∀n, 0 < d n) (hsite : ∀n, 0 ≤ site n)
    (hdlim : Tendsto d atTop (𝓝 0))
    (halim : Tendsto a atTop (𝓝 0))
    (hIlim : Tendsto
      (fun n => (∫u in 0..Ccut*d n,D n u)/(d n)^2) atTop (𝓝 0))
    (hsitelim : Tendsto (fun n => site n/d n) atTop (𝓝 0))
    (hD : ∀n, IntervalIntegrable (D n) volume 0 (Ccut*d n))
    (hR : ∀n, IntervalIntegrable (fun u => |R n u|) volume 0 (Ccut*d n))
    (hDpos : ∀n,∀u∈Icc (0:ℝ) (Ccut*d n),0≤D n u)
    (hK : ∀j∈s,0≤K j)
    (hEta : ∀j∈s,∀n, IntervalIntegrable (Eta j n) volume 0 (Ccut*d n))
    (hEtapos : ∀j∈s,∀n,∀u∈Icc (0:ℝ) (Ccut*d n),0≤Eta j n u)
    (hpow : ∀j∈s,∀n,∀u∈Icc (0:ℝ) (Ccut*d n),
      (Eta j n u)^(k j+1) ≤ K j*(D n u+site n)/d n)
    (hpoint : ∀n,∀u∈Ioo (0:ℝ) (Ccut*d n),
      |R n u| ≤ C*((d n)^4+(d n)^2*D n u+
        d n*(∫v in 0..Ccut*d n,D n v))+
        (d n)^3*(a n+∑j∈s,c j*Eta j n u)) :
    Tendsto (fun n => (∫u in 0..Ccut*d n, |R n u|)/(d n)^4)
      atTop (𝓝 0) := by
  let aa : ℕ → ℝ := fun n => a n/C
  let cc : ι → ℝ := fun j => c j/C
  have halim' : Tendsto aa atTop (𝓝 0) := by
    simpa only [aa,div_eq_mul_inv,mul_comm,mul_zero] using
      halim.const_mul C⁻¹
  have hpoint' (n : ℕ) (u : ℝ) (hu : u∈Ioo (0:ℝ) (Ccut*d n)) :
      |R n u| ≤ C*((d n)^4+(d n)^2*D n u+
        d n*(∫v in 0..Ccut*d n,D n v)+aa n*(d n)^3+
        (d n)^3*(∑j∈s,cc j*Eta j n u)) := by
    have hsumEq : (∑j∈s,cc j*Eta j n u) =
        (∑j∈s,c j*Eta j n u)/C := by
      dsimp only [cc]
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    calc
      |R n u| ≤ C*((d n)^4+(d n)^2*D n u+
          d n*(∫v in 0..Ccut*d n,D n v))+
          (d n)^3*(a n+∑j∈s,c j*Eta j n u) := hpoint n u hu
      _ = C*((d n)^4+(d n)^2*D n u+
          d n*(∫v in 0..Ccut*d n,D n v)+aa n*(d n)^3+
          (d n)^3*(∑j∈s,cc j*Eta j n u)) := by
        rw [hsumEq]
        dsimp only [aa]
        field_simp [hC.ne']
        ring
  exact finite_power_family_local_residual_integral_Ioo_tendsto_zero
    s k K cc hCcut d aa site D R Eta hd hsite hdlim halim' hIlim
    hsitelim hD hR hDpos hK hEta hEtapos hpow hpoint'

end OAI.SKFluctuations.Cavity
