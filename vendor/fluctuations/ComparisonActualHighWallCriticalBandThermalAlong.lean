module

public import ComparisonActualHighWallCriticalBandThermal
public import ComparisonActualHighWallCriticalInitialThermalAlong
public import ComparisonRadiusSizeRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
namespace ActualHighWallOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eventually_actual_high_wall_critical_cut_feasible :
    ∀ᶠn : ℕ in atTop,
      ∀a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        2*a.data.N^(-(10:ℝ)) < comparisonSmallMass a.data.N a.data.E := by
  have Hsmall := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=2*(1+D^2)) (d:=(1:ℝ)/2) (q:=-(9:ℝ)) (r:=0)
      (by norm_num) (by norm_num))
  filter_upwards [Hsmall] with n hn
  intro a
  have hN : 1 ≤ a.data.N := by dsimp [ActualHighWallData.N]; exact_mod_cast Nat.succ_pos n
  have Hinv := a.actual_mass_inverse_small_le hN
  have Hprod : (2*a.data.N^(-(10:ℝ)))/comparisonSmallMass a.data.N a.data.E ≤
      (2*(1+D^2))*a.data.N^(-(9:ℝ)) := by
    calc
      _ = (2*a.data.N^(-(10:ℝ)))*(1/comparisonSmallMass a.data.N a.data.E) := by ring
      _ ≤ (2*a.data.N^(-(10:ℝ)))*(a.data.N*(1+D^2)) :=
        mul_le_mul_of_nonneg_left Hinv (by positivity)
      _ = (2*(1+D^2))*a.data.N^(-(9:ℝ)) := by
        have He : a.data.N^(-(10:ℝ))*a.data.N=a.data.N^(-(9:ℝ)) := by
          calc
            _ = a.data.N^(-(10:ℝ))*a.data.N^(1:ℝ) := by rw [Real.rpow_one]
            _ = a.data.N^(-(10:ℝ)+1) := (Real.rpow_add a.data.hN _ _).symm
            _ = _ := by norm_num
        calc
          _ = (2*(1+D^2))*(a.data.N^(-(10:ℝ))*a.data.N) := by ring
          _ = _ := by rw [He]
  have Hhalf : (2*(1+D^2))*a.data.N^(-(9:ℝ)) ≤ (1:ℝ)/2 := by
    simpa only [ActualHighWallData.N,Real.rpow_zero,mul_one] using hn
  exact (div_lt_one a.data.hU).mp ((Hprod.trans Hhalf).trans_lt (by norm_num))

theorem critical_band_count_saved_tendsto_zero_along
    (hm : 0 < m) (hdelta : 0 < delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock) :
    Tendsto (fun n=>(M n).data.N^(-actualMassSavingExponent m delta)*
      ((Nat.ceil (Real.log (1/comparisonSmallMass (M n).data.N (M n).data.E)/Real.log 2):ℝ)+1))
      atTop (𝓝 0) := by
  let eta:=actualMassSavingExponent m delta
  have heta : 0 < eta := actualMassSavingExponent_pos hm hdelta
  have HN : Tendsto (fun n=>((dim n+1:ℕ):ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim
  have Hlog : Tendsto (fun n=>Real.log (M n).data.N*(M n).data.N^(-eta)) atTop (𝓝 0) := by
    have H := (comparison_radius_log_power_tendsto heta).comp
      ((tendsto_add_atTop_nat 1).comp hdim)
    convert H using 1
    ext n
    simp only [Function.comp_apply,ActualHighWallData.N,div_eq_mul_inv]
    rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ (dim n+1:ℕ))]
  have Hbound := (Hlog.const_mul (actualHighWallMassCountConstant D))
  have Hbound0 : Tendsto (fun n=>actualHighWallMassCountConstant D*
      (Real.log (M n).data.N*(M n).data.N^(-eta))) atTop (𝓝 0) := by
    simpa only [mul_zero] using Hbound
  apply squeeze_zero' _ _ Hbound0
  · filter_upwards [] with n
    positivity
  · filter_upwards [(Real.tendsto_log_atTop.comp HN).eventually (eventually_ge_atTop 1)]
      with n hn
    have hN : 1 ≤ (M n).data.N := by
      dsimp [ActualHighWallData.N]; exact_mod_cast Nat.succ_pos (dim n)
    have Hcount := (M n).actual_mass_log_count_le hN
      (by simpa only [Function.comp_apply,ActualHighWallData.N] using hn)
    have HH:=mul_le_mul_of_nonneg_left Hcount
      (Real.rpow_nonneg (M n).data.hN.le (-eta))
    convert HH using 1; ring

theorem actual_high_wall_critical_band_thermal_tendsto_zero_along
    {c C : ℝ} (hc : 0 < c) (hC : c < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0)) :
    Tendsto (fun n=>(∫u in Ioo (c*(M n).data.d) (C*(M n).data.d),
      orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)/(M n).data.d^3)
      atTop (𝓝 0) := by
  obtain ⟨K,hK,Hfinite⟩:=eventually_actual_high_wall_critical_band_thermal_rate
    (Bclock:=Bclock) hc hC hm hdelta hroom hcl hcu hAz hC0 hCt hD
  have Hbase:=critical_mass_cover_base_ratio_tendsto_zero_along hm hC0 dim hdim M
    (fun n=>(hfixed n).le) hsRatio
  have HU : Tendsto (fun n=>comparisonSmallMass (M n).data.N (M n).data.E/(M n).data.d)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>div_nonneg (M n).data.hU.le (M n).data.hd.le) _ Hbase
    intro n
    exact div_le_div_of_nonneg_right
      (show comparisonSmallMass (M n).data.N (M n).data.E≤(M n).criticalMassCoverBase
        from le_max_left _ _) (M n).data.hd.le
  have Hfloor := actual_wall_floor_mass_ratio_tendsto_zero_along
    (D:=D) hC0 (by linarith : 0 < 3*m+delta) dim hdim M
      (fun n=>(M n).data.d) (fun n=>(hfixed n).le)
  have Hprefix := actual_critical_initial_thermal_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M (fun n=>(hfixed n).le) hsRatio
  have Hq:=critical_band_count_saved_tendsto_zero_along hm hdelta dim hdim M
  have Hrhs : Tendsto (fun n=>10*C*((M n).data.N^(-actualMassSavingExponent m delta)*
      ((Nat.ceil (Real.log (1/comparisonSmallMass (M n).data.N (M n).data.E)/Real.log 2):ℝ)+1))+
    ((∫u in 0..min (8*(M n).criticalMassCoverBase) 1,
      orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)/(M n).data.d^3)+
    K*(1+C)^2*((M n).data.N^(-delta)*comparisonSmallMass (M n).data.N (M n).data.E/
      (M n).data.d)) atTop (𝓝 0) := by
    have HH := ((Hq.const_mul (10*C)).add Hprefix).add
      (Hfloor.const_mul (K*(1+C)^2))
    simpa only [mul_zero,zero_add] using HH
  have Hcut := hdim.eventually (eventually_actual_high_wall_critical_cut_feasible
    (m:=m) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (C0:=C0) (Ct:=Ct)
    (D:=D) (Bclock:=Bclock))
  have HN : Tendsto (fun n=>((dim n+1:ℕ):ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim
  have Hlog: ∀ᶠn in atTop,1≤Real.log (M n).data.N := by
    simpa only [Function.comp_apply,ActualHighWallData.N] using
      (Real.tendsto_log_atTop.comp HN).eventually (eventually_ge_atTop 1)
  have Hdhi: ∀ᶠn in atTop,C*(M n).data.d≤1 := by
    have HCp : 0 < C := hc.trans hC
    filter_upwards [hdlim.eventually (eventually_le_nhds (show 0 < 1/C by positivity))]
      with n hn
    calc
      C*(M n).data.d ≤ C*(1/C) := mul_le_mul_of_nonneg_left hn HCp.le
      _ = 1 := by field_simp
  have HUc: ∀ᶠn in atTop,comparisonSmallMass (M n).data.N (M n).data.E≤c*(M n).data.d := by
    filter_upwards [HU.eventually (eventually_le_nhds hc)] with n hn
    exact (div_le_iff₀ (M n).data.hd).mp hn
  have Hsc: ∀ᶠn in atTop,32*(M n).data.s<c*(M n).data.d := by
    filter_upwards [hsRatio.eventually (eventually_lt_nhds (show 0 < c/32 by positivity))]
      with n hn
    have Hd:=(M n).data.hd
    have HH: (M n).data.s/(M n).data.d<c/32:=hn
    apply (div_lt_iff₀ Hd).mp at HH
    nlinarith
  apply squeeze_zero' _ _ Hrhs
  · filter_upwards [Hdhi] with n hn
    apply div_nonneg _ (pow_nonneg (M n).data.hd.le 3)
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact (M n).full_thermal_nonneg_on_unit
      ⟨(mul_nonneg hc.le (M n).data.hd.le).trans hu.1.le,hu.2.le.trans hn⟩
  · filter_upwards [hdim.eventually Hfinite,Hcut,Hlog,Hdhi,HUc,Hsc]
      with n hnF hnCut hnLog hnHi hnU hnS
    have HH:=hnF (M n) (hfixed n) hnU hnS (hnCut (M n)) hnLog hnHi
    have Hd:=(M n).data.hd
    have Hdiv:=div_le_div_of_nonneg_right HH (pow_nonneg Hd.le 3)
    convert Hdiv using 1; field_simp

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
