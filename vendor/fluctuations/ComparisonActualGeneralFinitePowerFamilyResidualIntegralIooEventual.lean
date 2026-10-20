module

public import ComparisonActualGeneralFinitePowerFamilyResidualIntegralIoo

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory
open scoped Topology BigOperators
set_option autoImplicit false

theorem finite_power_family_separate_coefficients_eventual_Ioo_integral_tendsto_zero
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
    (hK : ∀j∈s,0≤K j)
    (hD : ∀ᶠn in atTop,IntervalIntegrable (D n) volume 0 (Ccut*d n))
    (hR : ∀ᶠn in atTop,
      IntervalIntegrable (fun u => |R n u|) volume 0 (Ccut*d n))
    (hDpos : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) (Ccut*d n),0≤D n u)
    (hEta : ∀ᶠn in atTop,∀j∈s,
      IntervalIntegrable (Eta j n) volume 0 (Ccut*d n))
    (hEtapos : ∀ᶠn in atTop,∀j∈s,∀u∈Icc (0:ℝ) (Ccut*d n),0≤Eta j n u)
    (hpow : ∀ᶠn in atTop,∀j∈s,∀u∈Icc (0:ℝ) (Ccut*d n),
      (Eta j n u)^(k j+1) ≤ K j*(D n u+site n)/d n)
    (hpoint : ∀ᶠn in atTop,∀u∈Ioo (0:ℝ) (Ccut*d n),
      |R n u| ≤ C*((d n)^4+(d n)^2*D n u+
        d n*(∫v in 0..Ccut*d n,D n v))+
        (d n)^3*(a n+∑j∈s,c j*Eta j n u)) :
    Tendsto (fun n => (∫u in 0..Ccut*d n, |R n u|)/(d n)^4)
      atTop (𝓝 0) := by
  let Good : ℕ → Prop := fun n =>
    IntervalIntegrable (D n) volume 0 (Ccut*d n) ∧
    IntervalIntegrable (fun u => |R n u|) volume 0 (Ccut*d n) ∧
    (∀u∈Icc (0:ℝ) (Ccut*d n),0≤D n u) ∧
    (∀j∈s,IntervalIntegrable (Eta j n) volume 0 (Ccut*d n)) ∧
    (∀j∈s,∀u∈Icc (0:ℝ) (Ccut*d n),0≤Eta j n u) ∧
    (∀j∈s,∀u∈Icc (0:ℝ) (Ccut*d n),
      (Eta j n u)^(k j+1) ≤ K j*(D n u+site n)/d n) ∧
    (∀u∈Ioo (0:ℝ) (Ccut*d n),
      |R n u| ≤ C*((d n)^4+(d n)^2*D n u+
        d n*(∫v in 0..Ccut*d n,D n v))+
        (d n)^3*(a n+∑j∈s,c j*Eta j n u))
  have hgood : ∀ᶠn in atTop,Good n := by
    filter_upwards [hD,hR,hDpos,hEta,hEtapos,hpow,hpoint]
      with n hnD hnR hnDpos hnEta hnEtapos hnpow hnpoint
    exact ⟨hnD,hnR,hnDpos,hnEta,hnEtapos,hnpow,hnpoint⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hgood
  let idx : ℕ → ℕ := fun n => max n N
  have hidxge (n : ℕ) : N ≤ idx n := le_max_right n N
  have hnext (n : ℕ) : Good (idx n) := hN (idx n) (hidxge n)
  have hidx : Tendsto idx atTop atTop := by
    apply tendsto_id.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    exact (max_eq_left hn).symm
  let dd : ℕ → ℝ := fun n => d (idx n)
  let aa : ℕ → ℝ := fun n => a (idx n)
  let ss : ℕ → ℝ := fun n => site (idx n)
  let DD : ℕ → ℝ → ℝ := fun n => D (idx n)
  let RR : ℕ → ℝ → ℝ := fun n => R (idx n)
  let EE : ι → ℕ → ℝ → ℝ := fun j n => Eta j (idx n)
  have hD' (n : ℕ) : IntervalIntegrable (DD n) volume 0 (Ccut*dd n) :=
    (hnext n).1
  have hR' (n : ℕ) : IntervalIntegrable (fun u => |RR n u|) volume 0 (Ccut*dd n) :=
    (hnext n).2.1
  have hDpos' (n : ℕ) (u : ℝ) (hu : u∈Icc (0:ℝ) (Ccut*dd n)) :
      0≤DD n u := (hnext n).2.2.1 u hu
  have hEta' (j : ι) (hj : j∈s) (n : ℕ) :
      IntervalIntegrable (EE j n) volume 0 (Ccut*dd n) :=
    (hnext n).2.2.2.1 j hj
  have hEtapos' (j : ι) (hj : j∈s) (n : ℕ) (u : ℝ)
      (hu : u∈Icc (0:ℝ) (Ccut*dd n)) :
      0≤EE j n u := (hnext n).2.2.2.2.1 j hj u hu
  have hpow' (j : ι) (hj : j∈s) (n : ℕ) (u : ℝ)
      (hu : u∈Icc (0:ℝ) (Ccut*dd n)) :
      (EE j n u)^(k j+1) ≤ K j*(DD n u+ss n)/dd n :=
    (hnext n).2.2.2.2.2.1 j hj u hu
  have hpoint' (n : ℕ) (u : ℝ) (hu : u∈Ioo (0:ℝ) (Ccut*dd n)) :
      |RR n u| ≤ C*((dd n)^4+(dd n)^2*DD n u+
        dd n*(∫v in 0..Ccut*dd n,DD n v))+
        (dd n)^3*(aa n+∑j∈s,c j*EE j n u) :=
    (hnext n).2.2.2.2.2.2 u hu
  have hIlim' : Tendsto
      (fun n => (∫u in 0..Ccut*dd n,DD n u)/(dd n)^2)
      atTop (𝓝 0) := by
    simpa only [dd,DD,Function.comp_def] using hIlim.comp hidx
  have H : Tendsto
      (fun n => (∫u in 0..Ccut*dd n, |RR n u|)/(dd n)^4)
      atTop (𝓝 0) :=
    finite_power_family_separate_coefficients_residual_integral_Ioo_tendsto_zero
      s k K c hCcut hC dd aa ss DD RR EE (fun n => hd (idx n))
      (fun n => hsite (idx n))
      (by simpa only [dd,Function.comp_def] using hdlim.comp hidx)
      (by simpa only [aa,Function.comp_def] using halim.comp hidx)
      hIlim'
      (by simpa only [ss,dd,Function.comp_def] using hsitelim.comp hidx)
      hD' hR' hDpos' hK hEta' hEtapos' hpow' hpoint'
  apply H.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  simp only [dd,RR,idx,max_eq_left hn]

end OAI.SKFluctuations.Cavity
