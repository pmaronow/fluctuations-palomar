module

public import ComparisonActualHighWallCriticalMassEq22FiniteReaderPointwise
public import ComparisonActualGeneralFinitePowerFamilyResidualIntegralIooEventual
public import ComparisonActualHighWallCriticalSampledTaylorDensityDimAlong
public import ComparisonActualHighWallCriticalScalarCalibration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal BigOperators
set_option autoImplicit false

theorem actual_high_wall_critical_mass_Eq22_of_fractional_pointwise_price
    {m delta cl cu Az C0 Ct D Bclock Ccut Cbudget : ℝ}
    (hCcut : 0 < Ccut) (hCbudget : 0 < Cbudget)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighWallOverlapMinimum
      (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n => (M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto
      (fun n => (M n).data.s/(M n).data.d) atTop (𝓝 0))
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p : ι → ℕ) (hp : ∀j∈s,0<p j)
    (c : ι → ℝ)
    (a : ℕ → ℝ) (halim : Tendsto a atTop (𝓝 0))
    (hpoint : ∀ᶠn in atTop,
      ∀u∈Ioo (0:ℝ) (Ccut*(M n).data.d),
        let d := (M n).data.d
        let site := 1/((dim n+1:ℕ):ℝ)
        let Dmass := (M n).originalMassThermalRadius
        let J := ∫v in 0..Ccut*d,Dmass v
        |(M n).originalMassScalarResidual u| ≤
          Cbudget*(d^4+d^2*Dmass u+d*J)+
          d^3*(Cbudget*(a n+site/d)+
            ∑j∈s,(Cbudget*c j)*
              ((Dmass u+site)/d)^((p j:ℝ)⁻¹))) :
    Tendsto (fun n =>
      (∫u in 0..Ccut*(M n).data.d,
        |(M n).originalMassScalarResidual u|)/(M n).data.d^4)
      atTop (𝓝 0) := by
  let d : ℕ → ℝ := fun n => (M n).data.d
  let site : ℕ → ℝ := fun n => 1/((dim n+1:ℕ):ℝ)
  let Dmass : ℕ → ℝ → ℝ := fun n => (M n).originalMassThermalRadius
  let R : ℕ → ℝ → ℝ := fun n => (M n).originalMassScalarResidual
  let Eta : ι → ℕ → ℝ → ℝ := fun j n u =>
    ((Dmass n u+site n)/d n)^((p j:ℝ)⁻¹)
  let base : ℕ → ℝ := fun n => Cbudget*(a n+site n/d n)
  let weight : ι → ℝ := fun j => Cbudget*c j
  let k : ι → ℕ := fun j => p j-1
  have hd : ∀n,0<d n := fun n => (M n).data.hd
  have hsite (n : ℕ) : (0:ℝ) ≤ site n := by
    dsimp only [site]
    positivity
  have hIlim : Tendsto
      (fun n => (∫u in 0..Ccut*d n,Dmass n u)/(d n)^2)
      atTop (𝓝 0) := by
    simpa only [d,Dmass,ActualHighWallOverlapMinimum.originalMassThermalRadius]
      using ActualHighWallOverlapMinimum.actual_high_wall_critical_thermal_radius_tendsto_zero_along
        hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hD dim hdim M hfixed hdlim hsRatio
  have hsiteSq := actual_high_wall_original_sampled_site_over_square_dim_tendsto_zero
    hm hC0 dim hdim M hfixed
  have hsite' : Tendsto (fun n => site n/d n) atTop (𝓝 0) := by
    have H := (hdlim.mul hsiteSq).const_mul (1/3:ℝ)
    have H' : Tendsto
        (fun n => (1/3:ℝ)*(d n*(3/(((dim n+1:ℕ):ℝ)*(d n)^2))))
        atTop (𝓝 0) := by
      simpa only [d,mul_zero] using H
    apply H'.congr'
    filter_upwards [] with n
    dsimp only [d,site]
    have hd0 : (M n).data.d≠0 := (M n).data.hd.ne'
    have hN0 : (((dim n+1:ℕ):ℝ))≠0 := by positivity
    field_simp [hd0,hN0]
  have hbase : Tendsto base atTop (𝓝 0) := by
    have H := (halim.add hsite').const_mul Cbudget
    simpa only [base,mul_zero,add_zero] using H
  have Hcut : ∀ᶠn in atTop,Ccut*d n≤1 := by
    filter_upwards [hdlim.eventually
      (eventually_le_nhds (show (0:ℝ)<1/Ccut by positivity))] with n hn
    calc
      Ccut*d n≤Ccut*(1/Ccut) := mul_le_mul_of_nonneg_left hn hCcut.le
      _ = 1 := by field_simp
  have hDint : ∀ᶠn in atTop,
      IntervalIntegrable (Dmass n) volume 0 (Ccut*d n) := by
    filter_upwards [Hcut] with n hncut
    exact (native_intervalIntegrable_sqrt_of_intervalIntegrable
      (M n).full_original_thermal_intervalIntegrable).mono_set (by
        rw [uIcc_of_le (mul_nonneg hCcut.le (hd n).le),uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl hncut)
  have hRint : ∀ᶠn in atTop,
      IntervalIntegrable (fun u => |R n u|) volume 0 (Ccut*d n) := by
    filter_upwards [Hcut] with n hncut
    have hq : Ccut*d n∈Icc (0:ℝ) 1 :=
      ⟨mul_nonneg hCcut.le (hd n).le,hncut⟩
    simpa only [d,R,ActualHighWallOverlapMinimum.originalMassScalarResidual]
      using ((M n).original_scalar_gap_intervalIntegrable hq).abs
  have hDpos : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) (Ccut*d n),
      0≤Dmass n u := by
    filter_upwards [] with n u hu
    exact Real.sqrt_nonneg _
  let FG : ι → ℕ → Prop := fun j n =>
    IntervalIntegrable (Eta j n) volume 0 (Ccut*d n) ∧
    ∀u∈Icc (0:ℝ) (Ccut*d n),
      0≤Eta j n u ∧ (Eta j n u)^(p j)=(Dmass n u+site n)/d n
  have hFGone (j : ι) (hj : j∈s) : ∀ᶠn in atTop,FG j n := by
    have H := actual_high_wall_original_mass_fractional_factor_eventually
      hCcut dim M hdlim (p j) (hp j hj)
    simpa only [FG,d,site,Dmass,Eta,
      ActualHighWallOverlapMinimum.originalMassThermalRadius] using H
  have hFGall (t : Finset ι) : ∀ᶠn in atTop,∀j∈t, j∈s → FG j n := by
    induction t using Finset.induction_on with
    | empty =>
        exact Eventually.of_forall (fun n j hj => False.elim (Finset.notMem_empty j hj))
    | @insert j t hj ih =>
        by_cases hjs : j∈s
        · filter_upwards [hFGone j hjs,ih] with n hnj hnt
          intro i hi his
          rcases Finset.mem_insert.mp hi with hji|hit
          · subst i; exact hnj
          · exact hnt i hit his
        · filter_upwards [ih] with n hnt
          intro i hi his
          rcases Finset.mem_insert.mp hi with hji|hit
          · subst i; exact False.elim (hjs his)
          · exact hnt i hit his
  have hFG : ∀ᶠn in atTop,∀j∈s,FG j n := by
    filter_upwards [hFGall s] with n hn j hj
    exact hn j hj hj
  have hEtaInt : ∀ᶠn in atTop,∀j∈s,
      IntervalIntegrable (Eta j n) volume 0 (Ccut*d n) := by
    filter_upwards [hFG] with n hn j hj
    exact (hn j hj).1
  have hEtaPos : ∀ᶠn in atTop,∀j∈s,∀u∈Icc (0:ℝ) (Ccut*d n),
      0≤Eta j n u := by
    filter_upwards [hFG] with n hn j hj u hu
    exact ((hn j hj).2 u hu).1
  have hEtaPow : ∀ᶠn in atTop,∀j∈s,∀u∈Icc (0:ℝ) (Ccut*d n),
      (Eta j n u)^(k j+1) ≤
        (1:ℝ)*(Dmass n u+site n)/d n := by
    filter_upwards [hFG] with n hn j hj u hu
    have horder : k j+1=p j := by
      dsimp only [k]
      exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr (hp j hj))
    simpa only [horder,one_mul] using ((hn j hj).2 u hu).2.le
  have hpoint' : ∀ᶠn in atTop,∀u∈Ioo (0:ℝ) (Ccut*d n),
      |R n u|≤Cbudget*((d n)^4+(d n)^2*Dmass n u+
        d n*(∫v in 0..Ccut*d n,Dmass n v))+
        (d n)^3*(base n+∑j∈s,weight j*Eta j n u) := by
    simpa only [d,site,Dmass,R,Eta,base,weight,
      ActualHighWallOverlapMinimum.originalMassThermalRadius,
      ActualHighWallOverlapMinimum.originalMassScalarResidual]
      using hpoint
  have H := finite_power_family_separate_coefficients_eventual_Ioo_integral_tendsto_zero
    s k (fun _ => (1:ℝ)) weight hCcut.le hCbudget d base site Dmass R Eta
    hd hsite (by simpa only [d] using hdlim) hbase hIlim hsite'
    (fun _ _ => zero_le_one) hDint hRint hDpos
    hEtaInt hEtaPos hEtaPow hpoint'
  simpa only [d,R] using H

end OAI.SKFluctuations.LaplaceWindowFormalization
