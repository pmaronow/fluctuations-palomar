module

public import ComparisonActualHighWallCriticalThermalRadiusAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory
open scoped Topology NNReal
set_option autoImplicit false

theorem original_mass_fractional_factor_integrable_and_power
    {q d site : ℝ} (hq : 0 ≤ q) (hd : 0 < d) (hsite : 0 ≤ site)
    (D : ℝ → ℝ)
    (hD : IntervalIntegrable D volume 0 q)
    (hDpos : ∀u∈Icc (0:ℝ) q,0≤D u)
    (p : ℕ) (hp : 0 < p) :
    IntervalIntegrable
      (fun u => ((D u+site)/d)^((p:ℝ)⁻¹)) volume 0 q ∧
    ∀u∈Icc (0:ℝ) q,
      0≤((D u+site)/d)^((p:ℝ)⁻¹) ∧
      (((D u+site)/d)^((p:ℝ)⁻¹))^p=(D u+site)/d := by
  let f : ℝ → ℝ := fun u => (D u+site)/d
  let mu : Measure ℝ := volume.restrict (Ioc (0:ℝ) q)
  let : IsFiniteMeasure mu := by
    dsimp only [mu]
    infer_instance
  have hpReal : (1:ℝ)≤p := by exact_mod_cast hp
  have hpPos : (0:ℝ)<p := by exact_mod_cast hp
  have hpExp : (0:ℝ)<(p:ℝ)⁻¹ := inv_pos.mpr hpPos
  have hpExpLe : (p:ℝ)⁻¹≤1 := by
    rw [inv_eq_one_div,div_le_iff₀ hpPos]
    linarith only [hpReal]
  have hfI : IntervalIntegrable f volume 0 q :=
    (hD.add intervalIntegrable_const).div_const d
  have hf : Integrable f mu := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hq).mp hfI
  have hf0 : 0≤ᵐ[mu] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact div_nonneg
      (add_nonneg (hDpos u ⟨hu.1.le,hu.2⟩) hsite) hd.le
  have Hnorm : Integrable (fun u => ‖f u‖^((p:ℝ)⁻¹)) mu :=
    integrable_norm_rpow_of_le hf.aestronglyMeasurable hpExp.le
      zero_le_one hpExpLe (by simpa only [Real.rpow_one] using hf.norm)
  have hEta : IntervalIntegrable (fun u => f u^((p:ℝ)⁻¹)) volume 0 q := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hq).mpr
    change Integrable (fun u => f u^((p:ℝ)⁻¹)) mu
    apply Hnorm.congr
    filter_upwards [hf0] with u hu
    simp only [Real.norm_eq_abs,abs_of_nonneg hu]
  refine ⟨hEta,?_⟩
  intro u hu
  have hfnonneg : 0≤f u := div_nonneg
    (add_nonneg (hDpos u hu) hsite) hd.le
  exact ⟨Real.rpow_nonneg hfnonneg _,
    Real.rpow_inv_natCast_pow hfnonneg hp.ne'⟩

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal
set_option autoImplicit false

theorem actual_high_wall_original_mass_fractional_factor_eventually
    {m delta cl cu Az C0 Ct D Bclock Ccut : ℝ} (hCcut : 0 < Ccut)
    (dim : ℕ → ℕ)
    (M : (n : ℕ) → ActualHighWallOverlapMinimum
      (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hdlim : Tendsto (fun n => (M n).data.d) atTop (𝓝 0))
    (p : ℕ) (hp : 0 < p) :
    ∀ᶠn in atTop,
      let d := (M n).data.d
      let q := Ccut*d
      let Dmass := fun u => Real.sqrt
        (orderedPathB (dim n+1) (M n).bf (M n).hf u-
          (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)
      let site := 1/((dim n+1:ℕ):ℝ)
      IntervalIntegrable
        (fun u => ((Dmass u+site)/d)^((p:ℝ)⁻¹)) volume 0 q ∧
      ∀u∈Icc (0:ℝ) q,
        0≤((Dmass u+site)/d)^((p:ℝ)⁻¹) ∧
        (((Dmass u+site)/d)^((p:ℝ)⁻¹))^p=(Dmass u+site)/d := by
  have Hcut : ∀ᶠn in atTop,Ccut*(M n).data.d≤1 := by
    filter_upwards [hdlim.eventually
      (eventually_le_nhds (show (0:ℝ)<1/Ccut by positivity))] with n hn
    calc
      Ccut*(M n).data.d≤Ccut*(1/Ccut) :=
        mul_le_mul_of_nonneg_left hn hCcut.le
      _ = 1 := by field_simp
  filter_upwards [Hcut] with n hncut
  dsimp only
  let q := Ccut*(M n).data.d
  let Dmass : ℝ → ℝ := fun u => Real.sqrt
    (orderedPathB (dim n+1) (M n).bf (M n).hf u-
      (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)
  have hq0 : 0≤q := mul_nonneg hCcut.le (M n).data.hd.le
  have hD : IntervalIntegrable Dmass volume 0 q := by
    exact (native_intervalIntegrable_sqrt_of_intervalIntegrable
      (M n).full_original_thermal_intervalIntegrable).mono_set (by
        rw [uIcc_of_le hq0,uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl hncut)
  have hDpos : ∀u∈Icc (0:ℝ) q,0≤Dmass u := by
    intro u hu
    exact Real.sqrt_nonneg _
  have hsite : 0≤1/((dim n+1:ℕ):ℝ) := by positivity
  exact original_mass_fractional_factor_integrable_and_power hq0
    (M n).data.hd hsite Dmass hD hDpos p hp

end OAI.SKFluctuations.LaplaceWindowFormalization
