module

public import ComparisonActualHighWallCriticalInitialThermal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 10000000
namespace ActualHighWallOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem critical_mass_cover_base_ratio_tendsto_zero_along
    (hm : 0 < m) (hC0 : 0 < C0) (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxsd : ∀n,(M n).xs≤(M n).data.d)
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0)) :
    Tendsto (fun n=>(M n).criticalMassCoverBase/(M n).data.d) atTop (𝓝 0) := by
  have Hpow := ((tendsto_rpow_neg_atTop (by linarith : 0< 3*m)).comp
    ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim)).const_mul (C0^3)
  have HU : Tendsto (fun n=>comparisonSmallMass (M n).data.N (M n).data.E/(M n).data.d)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>div_nonneg (M n).data.hU.le (M n).data.hd.le) _
      (by simpa only [mul_zero] using Hpow)
    intro n
    simpa only [Function.comp_apply,ActualHighWallData.N,neg_mul] using
      (div_le_div_of_nonneg_left (M n).data.hU.le (M n).hxs (hxsd n)).trans
        ((M n).canonical_mass_small_ratio_high_wall hC0)
  have Hsum := HU.add (hsRatio.const_mul 8)
  apply squeeze_zero (fun n=>div_nonneg (criticalMassCoverBase_pos (a:=M n)).le (M n).data.hd.le) _
    (by simpa only [mul_zero,zero_add] using Hsum)
  intro n
  have Hmax : (M n).criticalMassCoverBase≤ comparisonSmallMass (M n).data.N (M n).data.E+8*(M n).data.s := by
    exact max_le (by linarith [(M n).data.hs.1]) (by linarith [(M n).data.hU])
  have H := div_le_div_of_nonneg_right Hmax (M n).data.hd.le
  simpa only [add_div,mul_div_assoc] using H

theorem actual_critical_initial_thermal_tendsto_zero_along
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta< 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hxsd : ∀n,(M n).xs≤(M n).data.d)
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0)) :
    Tendsto (fun n=>(∫u in 0..min (8*(M n).criticalMassCoverBase) 1,
      orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)/(M n).data.d^3) atTop (𝓝 0) := by
  obtain ⟨K,hK,Hphysical⟩:=eventually_actual_high_wall_critical_initial_thermal (D:=D) Bclock
    hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hbase := critical_mass_cover_base_ratio_tendsto_zero_along hm hC0 dim hdim M hxsd hsRatio
  have Hlimit := (((Hbase.const_mul 8).const_add 1).pow 2).mul Hbase |>.const_mul (8*K)
  have Hlimit0 : Tendsto (fun n=>8*K*(1+8*((M n).criticalMassCoverBase/(M n).data.d))^2*
      ((M n).criticalMassCoverBase/(M n).data.d)) atTop (𝓝 0) := by
    simpa only [mul_zero,add_zero,zero_add,one_pow,mul_assoc] using Hlimit
  apply squeeze_zero' _ _ Hlimit0
  · filter_upwards [] with n
    have hv : 0≤ min (8*(M n).criticalMassCoverBase) 1 :=
      le_min (mul_nonneg (by norm_num : (0:ℝ)≤8) (criticalMassCoverBase_pos (a:=M n)).le) zero_le_one
    apply div_nonneg _ (pow_nonneg (M n).data.hd.le 3)
    apply intervalIntegral.integral_nonneg hv
    intro u hu
    exact (M n).full_thermal_nonneg_on_unit ⟨hu.1,hu.2.trans (min_le_right _ _)⟩
  · filter_upwards [hdim.eventually Hphysical] with n hn
    have H := hn (M n)
    have hbase0 := (criticalMassCoverBase_pos (a:=M n)).le
    have HS := pow_le_pow_left₀ (add_nonneg (M n).hxs.le (by positivity : 0≤ 8*(M n).criticalMassCoverBase))
      (show (M n).xs+8*(M n).criticalMassCoverBase ≤ (M n).data.d+8*(M n).criticalMassCoverBase by linarith only [hxsd n]) 2
    have Hupper := H.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left HS (by positivity : 0≤ 8*K)) hbase0)
    have Hd := (M n).data.hd
    have HH := div_le_div_of_nonneg_right Hupper (pow_nonneg Hd.le 3)
    convert HH using 1; field_simp

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
