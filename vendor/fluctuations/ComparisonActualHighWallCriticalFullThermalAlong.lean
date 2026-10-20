module

public import ComparisonActualHighWallCriticalBandThermalAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
namespace ActualHighWallOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem actual_high_wall_critical_full_thermal_tendsto_zero_along
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
      orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)/(M n).data.d^3)
      atTop (𝓝 0) := by
  obtain ⟨K,hK,Hlow⟩:=eventually_actual_high_wall_critical_low_mass_thermal
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hdhi : ∀ᶠ n in atTop,C*(M n).data.d≤1 := by
    filter_upwards [hdlim.eventually (eventually_le_nhds (show 0 < 1/C by positivity))]
      with n hn
    calc
      C*(M n).data.d ≤ C*(1/C) := mul_le_mul_of_nonneg_left hn hC.le
      _ = 1 := by field_simp
  apply tendsto_order.2
  constructor
  · intro b hb
    filter_upwards [Hdhi] with n hn
    have Hnon : 0 ≤ (∫u in 0..C*(M n).data.d,
      orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2) := by
      apply intervalIntegral.integral_nonneg (mul_nonneg hC.le (M n).data.hd.le)
      intro u hu
      exact (M n).full_thermal_nonneg_on_unit ⟨hu.1,hu.2.trans hn⟩
    exact hb.trans_le (div_nonneg Hnon (pow_nonneg (M n).data.hd.le 3))
  · intro ε hε
    let c:=min (C/2) (min 1 (ε/(16*K)))
    have hc : 0 < c := lt_min (div_pos hC (by norm_num))
      (lt_min (by norm_num) (div_pos hε (mul_pos (by norm_num) hK)))
    have hcC : c < C := (min_le_left _ _).trans_lt (by linarith)
    have hc1 : c ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    have hcε : c ≤ ε/(16*K) := (min_le_right _ _).trans (min_le_right _ _)
    have Hband:=actual_high_wall_critical_band_thermal_tendsto_zero_along
      hc hcC hm hdelta hroom hcl hcu hAz hC0 hCt hD dim hdim M hfixed hdlim hsRatio
    filter_upwards [hdim.eventually Hlow,Hdhi,
      Hband.eventually (eventually_lt_nhds (show 0 < ε/2 by positivity))]
      with n hnLow hnHi hnBand
    let a:=M n
    let d:=a.data.d
    let f:=fun u=>orderedPathB (dim n+1) a.bf a.hf u-
      (orderedPathS (dim n+1) a.bf a.hf u)^2
    have hd : 0 < d := a.data.hd
    have hc0 : 0 ≤ c*d := mul_nonneg hc.le hd.le
    have hcCd : c*d≤C*d := mul_le_mul_of_nonneg_right hcC.le hd.le
    have hC0 : 0 ≤ C*d := hc0.trans hcCd
    have Hlo : (∫u in 0..c*d,f u)≤K*(d+c*d)^2*(c*d) := by
      simpa only [f,a,d,hfixed n] using hnLow a (c*d) ⟨hc0,hcCd.trans hnHi⟩
    have HloNorm : (∫u in 0..c*d,f u)/d^3 ≤ K*(1+c)^2*c := by
      have H := div_le_div_of_nonneg_right Hlo (pow_nonneg hd.le 3)
      convert H using 1; field_simp
    have HloSmall : K*(1+c)^2*c ≤ ε/4 := by
      have Hsq : (1+c)^2≤4 := by nlinarith [sq_nonneg (1-c)]
      have Hx := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left Hsq hK.le) hc.le
      have Hy := mul_le_mul_of_nonneg_left hcε (show 0≤4*K by positivity)
      calc
        K*(1+c)^2*c ≤ K*4*c := Hx
        _ = 4*K*c := by ring
        _ ≤ 4*K*(ε/(16*K)) := Hy
        _ = ε/4 := by field_simp; ring
    have H01 : IntervalIntegrable f volume 0 (c*d) :=
      a.full_original_thermal_intervalIntegrable.mono_set (by
        rw [uIcc_of_le hc0,uIcc_of_le zero_le_one]
        exact Icc_subset_Icc le_rfl (hcCd.trans hnHi))
    have H12 : IntervalIntegrable f volume (c*d) (C*d) :=
      a.full_original_thermal_intervalIntegrable.mono_set (by
        rw [uIcc_of_le hcCd,uIcc_of_le zero_le_one]
        exact Icc_subset_Icc hc0 (hnHi))
    have Hsplit:=intervalIntegral.integral_add_adjacent_intervals H01 H12
    have HbandEq : (∫u in c*d..C*d,f u)=(∫u in Ioo (c*d) (C*d),f u) := by
      rw [intervalIntegral.integral_of_le hcCd,integral_Ioc_eq_integral_Ioo]
    rw [HbandEq] at Hsplit
    have Hnorm : (∫u in 0..C*d,f u)/d^3 =
        (∫u in 0..c*d,f u)/d^3+(∫u in Ioo (c*d) (C*d),f u)/d^3 := by
      rw [←Hsplit,add_div]
    dsimp only [a,d,f] at Hnorm HloNorm hnBand
    rw [Hnorm]
    calc
      _ ≤ ε/4+(∫u in Ioo (c*(M n).data.d) (C*(M n).data.d),
          orderedPathB (dim n+1) (M n).bf (M n).hf u-
            (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)/(M n).data.d^3 :=
        add_le_add_left (HloNorm.trans HloSmall) _
      _ < ε := by linarith only [hnBand,hε]

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
