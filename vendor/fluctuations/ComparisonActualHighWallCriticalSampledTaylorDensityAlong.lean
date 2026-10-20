module

public import ComparisonNativeActualUniformBandL1Density
public import ComparisonActualHighWallCriticalThermalRadiusAlong
public import ComparisonActualHighWallHighMassNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 14000000

theorem actual_high_wall_original_sampled_initial_radius_le_thermal
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Ccut : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hCcut : 0 ≤ Ccut) (hcut1 : Ccut*M.data.d ≤ 1)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) :
    ∀ᶠjGrid : ℕ in atTop,
      let as:=finiteCutMasses us jGrid
      ∀U : ℕ,U ≤ as.length → partitionPoint 0 as U ≤ Ccut*M.data.d →
        ClockTree.edgeBudget 0 as
          (fun j=>if j<U then nativeOriginalCutLowErrorRadius n M.bf M.hf as j+
            1/(n+1:ℕ) else 0) ≤
          (∫u in 0..Ccut*M.data.d,
            Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
              (orderedPathS (n+1) M.bf M.hf u)^2))+3/(n+1:ℕ) := by
  filter_upwards [original_band_l1_density_on_all_final_nets n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)] with jGrid hj
  dsimp only at hj ⊢
  intro U hU hmass
  let as:=finiteCutMasses us jGrid
  let Q:=fun u=>Real.sqrt (orderedPathB (n+1) M.bf M.hf u-
    (orderedPathS (n+1) M.bf M.hf u)^2)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have Hband:=hj us hus 0 U (Nat.zero_le _) hU
  have hzero : partitionPoint 0 as 0=0:=by cases as <;> rfl
  simp only [Nat.not_lt_zero,ite_false] at Hband
  rw [hzero] at Hband
  have hQ : IntervalIntegrable Q volume 0 (Ccut*M.data.d) :=
    (native_intervalIntegrable_sqrt_of_intervalIntegrable
      (physicalOrderedThermal_intervalIntegrable n M.bf M.hf
        (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha))).mono_set (by
        rw [uIcc_of_le (mul_nonneg hCcut M.data.hd.le),uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl hcut1)
  have Hmono : (∫u in 0..partitionPoint 0 as U,Q u) ≤
      (∫u in 0..Ccut*M.data.d,Q u) :=
    intervalIntegral.integral_mono_interval le_rfl (partitionPoint_mem as ho U).1
      hmass (ae_of_all _ (fun _=>Real.sqrt_nonneg _)) hQ
  exact Hband.trans (add_le_add Hmono le_rfl)

theorem actual_high_wall_original_sampled_site_over_square_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d) :
    Tendsto (fun n=>3/(((n+1:ℕ):ℝ)*(M n).data.d^2)) atTop (𝓝 0) := by
  have Hpow : Tendsto (fun n=>3*C0^6*((n+1:ℕ):ℝ)^(-6*m)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,neg_mul] using
      (((tendsto_rpow_neg_atTop (by positivity : 0 < 6*m)).comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))).const_mul (3*C0^6))
  apply squeeze_zero' (Eventually.of_forall (fun n=>by positivity)) ?_ Hpow
  filter_upwards [] with n
  have hd1 : (M n).data.d ≤ 1:=(M n).data.hd1
  have hd4 : (M n).data.d^4 ≤ 1:=pow_le_one₀ (M n).data.hd.le hd1
  have hd6 : (M n).data.d^6 ≤ (M n).data.d^2 := by
    have HH:=mul_le_mul_of_nonneg_left hd4 (sq_nonneg (M n).data.d)
    nlinarith only [HH]
  have Hcritical:=(M n).high_mass_inverse_power hC0 6
  rw [hfixed n] at Hcritical
  norm_num only [Nat.cast_ofNat,div_self (by norm_num : (6:ℝ) ≠ 0),
    Real.rpow_one] at Hcritical
  have Hle : 1/((M n).data.N*(M n).data.d^2) ≤
      1/((M n).data.N*(M n).data.d^6) :=
    div_le_div_of_nonneg_left zero_le_one
      (by have :=(M n).data.hd; have :=(M n).data.hN; positivity)
      (mul_le_mul_of_nonneg_left hd6 (M n).data.hN.le)
  have Hmul:=mul_le_mul_of_nonneg_left (Hle.trans Hcritical)
    (by norm_num : (0:ℝ) ≤ 3)
  convert Hmul using 1 <;> ring

theorem actual_high_wall_critical_sampled_initial_radius_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock Ccut : ℝ}
    (hCcut : 0 < Ccut)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0)) :
    ∃eps : ℕ→ℝ,Tendsto eps atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∀us : List PositiveMass,(∀u∈us,u.val ≤ 1)→
        ∀ᶠjGrid : ℕ in atTop,
          let as:=finiteCutMasses us jGrid
          ∀U : ℕ,U ≤ as.length → partitionPoint 0 as U ≤ Ccut*(M n).data.d →
            ClockTree.edgeBudget 0 as
              (fun j=>if j<U then nativeOriginalCutLowErrorRadius n (M n).bf (M n).hf as j+
                1/(n+1:ℕ) else 0) ≤ eps n*(M n).data.d^2 := by
  let J:=fun n=>∫u in 0..Ccut*(M n).data.d,
    Real.sqrt (orderedPathB (n+1) (M n).bf (M n).hf u-
      (orderedPathS (n+1) (M n).bf (M n).hf u)^2)
  let eps:=fun n=>J n/(M n).data.d^2+
    3/(((n+1:ℕ):ℝ)*(M n).data.d^2)
  have Hthermal:=ActualHighWallOverlapMinimum.actual_high_wall_critical_thermal_radius_tendsto_zero_along
    hCcut hm hdelta hroom hcl hcu hAz hC0 hCt hD id tendsto_id M hfixed hdlim hsRatio
  have Hsite:=actual_high_wall_original_sampled_site_over_square_tendsto_zero hm hC0 M hfixed
  have Heps : Tendsto eps atTop (𝓝 0) := by
    have HH:=Hthermal.add Hsite
    simpa only [eps,J,id_eq,zero_add] using HH
  have Hcut : ∀ᶠn in atTop,Ccut*(M n).data.d≤1 := by
    filter_upwards [hdlim.eventually (eventually_le_nhds
      (show (0:ℝ) < 1/Ccut by positivity))] with n hn
    calc
      Ccut*(M n).data.d ≤ Ccut*(1/Ccut) := mul_le_mul_of_nonneg_left hn hCcut.le
      _ = 1 := by field_simp
  refine ⟨eps,Heps,?_⟩
  filter_upwards [Hcut] with n hncut
  intro us hus
  have Hgrid:=actual_high_wall_original_sampled_initial_radius_le_thermal
    (M n) hCcut.le hncut us hus
  filter_upwards [Hgrid] with jGrid hj
  dsimp only at hj ⊢
  intro U hU hmass
  have H:=hj U hU hmass
  have hd:=(M n).data.hd
  have HEq : eps n*(M n).data.d^2=J n+3/(n+1:ℕ) := by
    dsimp only [eps,J]
    field_simp
  rw [HEq]
  exact H

end OAI.SKFluctuations.LaplaceWindowFormalization
