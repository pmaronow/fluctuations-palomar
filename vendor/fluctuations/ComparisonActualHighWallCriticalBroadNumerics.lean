module

public import ComparisonActualHighWallCriticalBroadDiameterNumerics
public import ComparisonActualHighWallCriticalBroadRate

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 22000000
set_option linter.unusedVariables false
namespace ActualHighWallOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem criticalBroadTraceConstant_nonneg
    {Az cl c C0 Ct D : ℝ} (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hc : 0<c) (hC0 : 0≤C0) (hCt : 0 ≤ Ct) :
    0≤criticalBroadTraceConstant Az cl c C0 Ct D := by
  have Hlog:=Real.log_nonneg (by nlinarith [sq_nonneg D] : (1:ℝ)≤1+D^2)
  have HK : 0≤highMassEndpointConstant (Az:=Az) (cl:=cl) 16 c:=
    (one_div_pos.mpr hc).le.trans (le_max_left _ _)
  unfold criticalBroadTraceConstant
  exact mul_nonneg (mul_nonneg criticalBroadOriginLossFactor_pos.le HK) (by positivity)

theorem eventually_actual_high_wall_critical_broad_budget_polynomial_le
    (ell : ℕ) (hell : 2<ell) (Q : ℝ) (hQ : 1≤Q)
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hCt : 0 ≤ Ct) (hC0 : 0 < C0) {c C : ℝ} (hc : 0<c) (hC : 0≤C) :
    ∀ᶠn : ℕ in atTop,
      ∀a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.xs=a.data.d → ∀v width : ℝ,0<v → v≤1 → c*a.data.d≤v → v≤C*a.data.d →
        v≤width → width≤4*v → width≤1 →
          a.criticalBroadMassBudget ell Q (10*Real.log a.data.N) (a.data.N^(-(10:ℝ))) v width/
            (a.data.d^2*v) ≤ a.data.N^(-actualMassSavingExponent m delta) := by
  let Ctrace:=criticalBroadTraceConstant Az cl c C0 Ct D
  let Cd:=criticalBroadDiameterConstant C0 D
  let Cr:=criticalBroadReverseConstant ell Q C C0 D
  let Ccut:=C0^4/c
  have HCtrace : 0 ≤ Ctrace:=criticalBroadTraceConstant_nonneg hcl hAz hc hC0.le hCt
  have HCd : 0≤Cd:=criticalBroadDiameterConstant_nonneg (D:=D) hC0.le
  have HCr : 0≤Cr:=criticalBroadReverseConstant_nonneg ell Q hC hC0.le
  have HCcut : 0≤Ccut:=by dsimp [Ccut];positivity
  have Hrate:=eventually_critical_broad_finite_saved_rate_le hm hdelta HCtrace HCd HCr HCcut
  have HU:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^3) (d:=c) (q:=-3*m) (r:=0) hc (by linarith))
  have HL:=(tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1:ℝ))
  filter_upwards [Hrate,HU,HL] with n hnRate hnU hnLog
  intro a hfixed v width hv hv1 hvlo hvhi hwlo hwhi hw1
  have hN : 1≤a.data.N:=by dsimp [ActualHighWallData.N];exact_mod_cast Nat.succ_pos n
  have hlog : 1≤Real.log a.data.N:=hnLog
  have hUratio : comparisonSmallMass a.data.N a.data.E/a.xs≤c:=
    (a.high_mass_small_ratio hC0).trans (by simpa only [ActualHighWallData.N,Real.rpow_zero,mul_one] using hnU)
  have hUv : comparisonSmallMass a.data.N a.data.E≤v:=
    ((div_le_iff₀ a.hxs).mp hUratio).trans (by simpa only [hfixed] using hvlo)
  let loss:=(32:ℝ)^2+a.criticalBroadTraceLoss 4 v (min (4*v) 1)+1
  have hV0 : 0 ≤ min (4*v) 1:=le_min (by positivity) zero_le_one
  have hMV : 0<a.data.M (min (4*v) 1):=
    (comparisonCap_first_term a.data.hN a.data.hU a.data.hL a.data.hE a.data.hd.le hV0).1
  have hrlog : 0≤Real.log ((1+comparisonSmallMass a.data.N a.data.E)/comparisonSmallMass a.data.N a.data.E):=
    Real.log_nonneg ((one_le_div a.data.hU).mpr (by linarith))
  have hloss : 0≤loss:=by
    dsimp [loss,criticalBroadTraceLoss]
    positivity [hMV.le, hrlog, a.data.hrbounds.1, a.data.hU, hv]
  have hP : 0<a.criticalBroadMassPower v:=a.highMassPower_pos 16 v
  have hDiam:=a.criticalBroad_diameter_nonneg (by linarith : 0≤Real.log a.data.N)
  have hRev:=a.criticalBroad_reverse_nonneg ell Q hv.le (by linarith : 0≤Real.log a.data.N)
  have Htrace:=a.criticalBroad_trace_noise_bound hm hcl hAz hCt hC0 hc hN hlog hfixed hv hv1 hvlo hUv
  have Htrace' : loss/(a.criticalBroadMassPower v*v^2*a.data.d^2)/Real.log a.data.N≤
      Ctrace*a.data.N^(-3*m) := by
    have HE : loss*(a.data.d^2/(a.criticalBroadMassPower v*v^2*a.xs^4))=
        loss/(a.criticalBroadMassPower v*v^2*a.data.d^2) := by rw [hfixed];field_simp
    dsimp only [loss] at HE
    rw [HE] at Htrace
    exact Htrace
  have HD:=a.criticalBroad_diameter_rate hdelta.le hC0 hN hlog
  rw [hfixed] at HD
  have HR:=a.criticalBroad_reverse_rate ell hell Q hm hdelta hC0 hN hlog hC hv.le
    (by simpa only [hfixed] using hvhi)
  rw [hfixed] at HR
  have Hweight:=a.high_mass_normalization_weight_le hm hC0 hN hc a.data.hd1 hv hvlo
  rw [hfixed] at Hweight
  have Hweight' : 1/(a.data.d^2*v)≤Ccut*a.data.N^4 := by
    convert Hweight using 1
    field_simp [a.data.hd.ne', hv.ne']
  have Hcut : a.data.N^(-(10:ℝ))/(a.data.d^2*v)≤Ccut*a.data.N^(-(6:ℝ)) := by
    have HH:=mul_le_mul_of_nonneg_left Hweight' (Real.rpow_nonneg a.data.hN.le (-(10:ℝ)))
    have HE : a.data.N^(-(10:ℝ))*(Ccut*a.data.N^4)=Ccut*a.data.N^(-(6:ℝ)) := by
      rw [show a.data.N^(-(10:ℝ))*(Ccut*a.data.N^4)=Ccut*(a.data.N^(-(10:ℝ))*a.data.N^4) by ring,
        ←Real.rpow_natCast a.data.N 4,←Real.rpow_add a.data.hN]
      norm_num
    simpa only [mul_one_div,HE] using HH
  exact hnRate a.data.d (a.criticalBroadMassPower v) v width a.criticalBroadMassDiameter
    (a.criticalBroadMassReverse ell Q v) loss a.data.hd hP hv hwlo hwhi hw1 hDiam hRev hloss Htrace' HD HR Hcut

theorem exists_actual_high_wall_critical_broad_budget_order
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hCt : 0 ≤ Ct) (hC0 : 0 < C0) {c C : ℝ} (hc : 0<c) (hC : 0≤C) :
    ∃ell : ℕ,2<ell ∧ ∀Q : ℝ,1≤Q → ∀ᶠn : ℕ in atTop,
      ∀a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.xs=a.data.d → ∀v width : ℝ,0<v → v≤1 → c*a.data.d≤v → v≤C*a.data.d →
        v≤width → width≤4*v → width≤1 →
          a.criticalBroadMassBudget ell Q (10*Real.log a.data.N) (a.data.N^(-(10:ℝ))) v width/
            (a.data.d^2*v) ≤ a.data.N^(-actualMassSavingExponent m delta) := by
  refine ⟨3,by norm_num,?_⟩
  intro Q hQ
  exact eventually_actual_high_wall_critical_broad_budget_polynomial_le 3 (by norm_num) Q hQ
    hm hdelta hcl hAz hCt hC0 hc hC

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
