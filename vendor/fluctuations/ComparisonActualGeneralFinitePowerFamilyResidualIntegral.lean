module

public import ComparisonActualGeneralPowerFactorAbsorption
public import ComparisonActualGeneralLocalThermalFactorIntegralBridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory
open scoped Topology BigOperators
set_option autoImplicit false

theorem finite_power_family_normalized_integral_tendsto_zero
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (k : ι → ℕ) (K c : ι → ℝ)
    {Ccut : ℝ} (hCcut : 0 ≤ Ccut)
    (d site : ℕ → ℝ) (D : ℕ → ℝ → ℝ) (Eta : ι → ℕ → ℝ → ℝ)
    (hd : ∀n, 0 < d n) (hsite : ∀n, 0 ≤ site n)
    (hIlim : Tendsto
      (fun n => (∫u in 0..Ccut*d n,D n u)/(d n)^2) atTop (𝓝 0))
    (hsitelim : Tendsto (fun n => site n/d n) atTop (𝓝 0))
    (hD : ∀n, IntervalIntegrable (D n) volume 0 (Ccut*d n))
    (hDpos : ∀n,∀u∈Icc (0:ℝ) (Ccut*d n),0≤D n u)
    (hK : ∀j∈s,0≤K j)
    (hEta : ∀j∈s,∀n, IntervalIntegrable (Eta j n) volume 0 (Ccut*d n))
    (hEtapos : ∀j∈s,∀n,∀u∈Icc (0:ℝ) (Ccut*d n),0≤Eta j n u)
    (hpow : ∀j∈s,∀n,∀u∈Icc (0:ℝ) (Ccut*d n),
      (Eta j n u)^(k j+1) ≤ K j*(D n u+site n)/d n) :
    Tendsto (fun n =>
      (∫u in 0..Ccut*d n, ∑j∈s,c j*Eta j n u)/d n)
      atTop (𝓝 0) := by
  have hsingle (j : ι) (hj : j∈s) :
      Tendsto (fun n => (∫u in 0..Ccut*d n,Eta j n u)/d n)
        atTop (𝓝 0) :=
    power_factor_normalized_integral_tendsto_zero (k j) hCcut (hK j hj)
      d site D (Eta j) hd hsite hIlim hsitelim hD (hEta j hj)
      hDpos (hEtapos j hj) (hpow j hj)
  have hsum : Tendsto
      (fun n => ∑j∈s,c j*((∫u in 0..Ccut*d n,Eta j n u)/d n))
      atTop (𝓝 (∑j∈s,c j*(0:ℝ))) :=
    tendsto_finsetSum s (fun j hj => (hsingle j hj).const_mul (c j))
  have hEq (n : ℕ) :
      (∫u in 0..Ccut*d n, ∑j∈s,c j*Eta j n u)/d n =
        ∑j∈s,c j*((∫u in 0..Ccut*d n,Eta j n u)/d n) := by
    have hterm (j : ι) (hj : j∈s) :
        IntervalIntegrable (fun u => c j*Eta j n u) volume 0 (Ccut*d n) :=
      (hEta j hj n).const_mul (c j)
    rw [intervalIntegral.integral_finsetSum (fun j hj => hterm j hj)]
    simp_rw [intervalIntegral.integral_const_mul]
    simp only [div_eq_mul_inv,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have H : Tendsto
      (fun n => ∑j∈s,c j*((∫u in 0..Ccut*d n,Eta j n u)/d n))
      atTop (𝓝 0) := by
    simpa only [mul_zero,Finset.sum_const_zero] using hsum
  exact H.congr' (Eventually.of_forall (fun n => (hEq n).symm))

theorem finite_power_family_local_residual_integral_tendsto_zero
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
    (hpoint : ∀n,∀u∈Icc (0:ℝ) (Ccut*d n),
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
  exact local_thermal_factor_residual_integral_tendsto_zero hCcut
    d a D EtaSum R hd hdlim halim hIlim hJlim hD hEtaSum hR
    (by simpa only [EtaSum] using hpoint)

theorem finite_power_family_separate_coefficients_residual_integral_tendsto_zero
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
    (hpoint : ∀n,∀u∈Icc (0:ℝ) (Ccut*d n),
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
  have hpoint' (n : ℕ) (u : ℝ) (hu : u∈Icc (0:ℝ) (Ccut*d n)) :
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
  exact finite_power_family_local_residual_integral_tendsto_zero
    s k K cc hCcut d aa site D R Eta hd hsite hdlim halim' hIlim
    hsitelim hD hR hDpos hK hEta hEtapos hpow hpoint'

end OAI.SKFluctuations.Cavity
