module

public import ComparisonActualHighWallMesoscopicBroadTraceSharp
public import ComparisonActualHighWallCriticalBroadNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 22000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ActualHighWallOverlapMinimum
variable {n : ℕ}
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem mesoscopic_broad_normalization_weight_le
    (a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hm : 0 < m) (hC0 : 0 < C0) (hN : 1 ≤ a.data.N)
    {c v : ℝ} (hc : 0 < c) (hxs1 : a.xs ≤ 1) (hv : 0 < v) (hvlo : c*a.xs ≤ v) :
    1/(a.xs^2*v)≤(C0^4/c)*a.data.N^4 := by
  have Hx : a.xs^4≤a.xs^3 := by
    have H:=mul_le_mul_of_nonneg_left hxs1 (show 0≤a.xs^3 by positivity [a.hxs])
    nlinarith only [H]
  have H1:=mul_le_mul_of_nonneg_left Hx hc.le
  have H2:=mul_le_mul_of_nonneg_left hvlo (sq_nonneg a.xs)
  have Hden : c*a.xs^4≤a.xs^2*v := by nlinarith only [H1,H2]
  have Hgeom : 1/(a.xs^2*v)≤(1/c)*(1/a.xs^4) := by
    have Hdirect : 1/(a.xs^2*v)≤1/(c*a.xs^4) :=
      (div_le_div_iff₀ (show 0<a.xs^2*v by positivity [a.hxs])
        (show 0<c*a.xs^4 by positivity [a.hxs])).mpr (by nlinarith only [Hden])
    convert Hdirect using 1 <;> field_simp
  have Hinv:=a.high_mass_inverse_four_coarse hm hC0 hN
  have H:=Hgeom.trans (mul_le_mul_of_nonneg_left Hinv (show 0≤1/c by positivity))
  convert H using 1 <;> ring

theorem eventually_actual_high_wall_mesoscopic_broad_budget_polynomial_le
    (ell : ℕ) (hell : 2 < ell) (Q : ℝ) (hQ : 1 ≤ Q)
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hCt : 0 ≤ Ct) (hC0 : 0 < C0) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C) :
    ∀ᶠn : ℕ in atTop,
      ∀a : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        a.data.d≤a.xs → a.xs≤1 → ∀v width : ℝ,0<v → v≤1 → c*a.xs≤v → v≤C*a.xs →
        v≤width → width≤4*v → width≤1 →
          a.criticalBroadMassBudget ell Q (10*Real.log a.data.N) (a.data.N^(-(10:ℝ))) v width/
            (a.xs^2*v) ≤ a.data.N^(-actualMassSavingExponent m delta) := by
  let Ctrace:=criticalBroadTraceConstant Az cl c C0 Ct D
  let Cd:=criticalBroadDiameterConstant C0 D
  let Cr:=criticalBroadReverseConstant ell Q C C0 D
  let Ccut:=C0^4/c
  have HCtrace : 0≤Ctrace:=criticalBroadTraceConstant_nonneg hcl hAz hc hC0.le hCt
  have HCd : 0≤Cd:=criticalBroadDiameterConstant_nonneg (D:=D) hC0.le
  have HCr : 0≤Cr:=criticalBroadReverseConstant_nonneg ell Q hC hC0.le
  have HCcut : 0≤Ccut:=by dsimp [Ccut];positivity
  have Hrate:=eventually_critical_broad_finite_saved_rate_le hm hdelta HCtrace HCd HCr HCcut
  have HU:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^3) (d:=c) (q:=-3*m) (r:=0) hc (by linarith))
  have HL:=(tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1:ℝ))
  filter_upwards [Hrate,HU,HL] with n hnRate hnU hnLog
  intro a hdx hxs1 v width hv hv1 hvlo hvhi hwlo hwhi hw1
  have hN : 1≤a.data.N:=by dsimp [ActualHighWallData.N];exact_mod_cast Nat.succ_pos n
  have hlog : 1≤Real.log a.data.N:=hnLog
  have hUratio : comparisonSmallMass a.data.N a.data.E/a.xs≤c:=
    (a.high_mass_small_ratio hC0).trans (by simpa only [ActualHighWallData.N,Real.rpow_zero,mul_one] using hnU)
  have hUv : comparisonSmallMass a.data.N a.data.E≤v:=
    ((div_le_iff₀ a.hxs).mp hUratio).trans hvlo
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
  have Htrace:=a.mesoscopicBroad_trace_noise_bound_sharp hm hcl hAz hCt hC0 hc hN hlog
    hdx hv hv1 hvlo hUv
  have Htrace' : loss/(a.criticalBroadMassPower v*v^2*a.xs^2)/Real.log a.data.N≤
      Ctrace*a.data.N^(-3*m) := by simpa only [loss,Ctrace] using Htrace
  have HD:=a.criticalBroad_diameter_rate hdelta.le hC0 hN hlog
  have HR:=a.criticalBroad_reverse_rate ell hell Q hm hdelta hC0 hN hlog hC hv.le hvhi
  have Hweight:=a.mesoscopic_broad_normalization_weight_le hm hC0 hN hc hxs1 hv hvlo
  have Hcut : a.data.N^(-(10:ℝ))/(a.xs^2*v)≤Ccut*a.data.N^(-(6:ℝ)) := by
    have HH:=mul_le_mul_of_nonneg_left Hweight (Real.rpow_nonneg a.data.hN.le (-(10:ℝ)))
    have HE : a.data.N^(-(10:ℝ))*(Ccut*a.data.N^4)=Ccut*a.data.N^(-(6:ℝ)) := by
      rw [show a.data.N^(-(10:ℝ))*(Ccut*a.data.N^4)=Ccut*(a.data.N^(-(10:ℝ))*a.data.N^4) by ring,
        ←Real.rpow_natCast a.data.N 4,←Real.rpow_add a.data.hN]
      norm_num
    dsimp only [Ccut] at HE ⊢
    simpa only [mul_one_div,HE] using HH
  exact hnRate a.xs (a.criticalBroadMassPower v) v width a.criticalBroadMassDiameter
    (a.criticalBroadMassReverse ell Q v) loss a.hxs hP hv hwlo hwhi hw1 hDiam hRev hloss Htrace' HD HR Hcut

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
