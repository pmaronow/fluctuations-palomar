module

public import ComparisonActualHighWallCriticalFullThermalAlong
public import ComparisonNativeMassDefectIntervalCauchy

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
namespace ActualHighWallOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_high_wall_critical_thermal_radius_tendsto_zero_along
    {C : ℝ} (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).data.d) atTop (𝓝 0)) :
    Tendsto (fun n=>(∫u in 0..C*(M n).data.d,
      Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))/(M n).data.d^2)
      atTop (𝓝 0) := by
  have Hthermal:=actual_high_wall_critical_full_thermal_tendsto_zero_along
    hC hm hdelta hroom hcl hcu hAz hC0 hCt hD dim hdim M hfixed hdlim hsRatio
  have Hsqrt : Tendsto (fun n=>Real.sqrt (C*((∫u in 0..C*(M n).data.d,
      orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)/(M n).data.d^3)))
      atTop (𝓝 0) := by
    have HH:=Real.continuous_sqrt.continuousAt.tendsto.comp (Hthermal.const_mul C)
    simpa [Function.comp_def] using HH
  have Hdhi : ∀ᶠ n in atTop,C*(M n).data.d≤1 := by
    filter_upwards [hdlim.eventually (eventually_le_nhds (show 0 < 1/C by positivity))]
      with n hn
    calc
      C*(M n).data.d ≤ C*(1/C) := mul_le_mul_of_nonneg_left hn hC.le
      _ = 1 := by field_simp
  apply squeeze_zero' _ _ Hsqrt
  · filter_upwards [] with n
    exact div_nonneg (intervalIntegral.integral_nonneg (mul_nonneg hC.le (M n).data.hd.le)
      (fun _ _=>Real.sqrt_nonneg _)) (pow_nonneg (M n).data.hd.le 2)
  · filter_upwards [Hdhi] with n hnHi
    let a:=M n
    let d:=a.data.d
    let f:=fun u=>orderedPathB (dim n+1) a.bf a.hf u-
      (orderedPathS (dim n+1) a.bf a.hf u)^2
    let T:=∫u in 0..C*d,f u
    let J:=∫u in 0..C*d,Real.sqrt (f u)
    have hd : 0 < d:=a.data.hd
    have hCd : 0≤C*d:=mul_nonneg hC.le hd.le
    have hfi : IntervalIntegrable f volume 0 (C*d) :=
      a.full_original_thermal_intervalIntegrable.mono_set (by
        rw [uIcc_of_le hCd,uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl hnHi)
    have hf0 : ∀u∈Icc (0:ℝ) (C*d),0≤f u := by
      intro u hu
      exact a.full_thermal_nonneg_on_unit ⟨hu.1,hu.2.trans hnHi⟩
    have HT0 : 0≤T := intervalIntegral.integral_nonneg hCd
      (fun u hu=>hf0 u ⟨hu.1,hu.2⟩)
    have HJ0 : 0≤J := intervalIntegral.integral_nonneg hCd
      (fun u _=>Real.sqrt_nonneg (f u))
    have Hcauchy:=interval_integral_sqrt_sq_le_length hCd hfi hf0
    have Hsq : (J/d^2)^2≤C*(T/d^3) := by
      calc
        (J/d^2)^2=J^2/d^4 := by field_simp
        _ ≤ ((C*d-0)*T)/d^4 := div_le_div_of_nonneg_right Hcauchy (pow_nonneg hd.le 4)
        _ = C*(T/d^3) := by field_simp; ring
    have Hbound : J/d^2≤Real.sqrt (C*(T/d^3)) := by
      exact Real.le_sqrt_of_sq_le Hsq
    simpa only [a,d,f,T,J] using Hbound

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
