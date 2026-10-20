module

public import ComparisonActualHighWallInitialMassMismatch
public import ComparisonActualHighWallInitialChargesAlong
public import ComparisonActualHighWallInitialMismatchAmplitude
public import ComparisonActualHighWallOriginsAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 20000000

namespace ActualHighWallOverlapMinimum

theorem actual_high_wall_critical_centering_l2_of_thermal_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (C : ℝ) (hC : 1 ≤ C)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (hthermal : Tendsto (fun n=>
      (∫u in 0..C*(M n).xs,
        orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)/(M n).xs^3)
      atTop (𝓝 0)) :
    Tendsto (fun n=>
      (∫u in 0..C*(M n).xs,
        (orderedPathS (dim n+1) (M n).bf (M n).hf u-
          (M n).data.wallRadius (M n).alpha u)^2)/(M n).xs^3)
      atTop (𝓝 0) := by
  have hroom' : 0<3*m+delta := by linarith
  have hrmin := rmin_over_larger_scale_tendsto_zero hdelta dim hdim M
    (fun n=>(M n).xs) (fun n=>(hfixed n).ge)
  have htravel := actual_wall_cap_travel_ratio_tendsto_zero_along hC0 hroom'
    dim hdim M (fun n=>(M n).xs) (fun _=>le_rfl)
  have hfloor := actual_wall_floor_mass_ratio_tendsto_zero_along hC0 hroom'
    dim hdim M (fun n=>(M n).xs) (fun _=>le_rfl)
  obtain ⟨K,hK,Hamp⟩ := eventually_actual_high_wall_initial_mismatch_amplitude
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  have hCpos : 0<C := zero_lt_one.trans_le hC
  have Hv := (hxlim.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ)<1 by simp))
  have Hratio : Tendsto (fun n=>
      16*C*((M n).data.rmin/(M n).xs+(M n).cavityCapTravel/(M n).xs)^2+
      2*((∫u in 0..C*(M n).xs,
        orderedPathB (dim n+1) (M n).bf (M n).hf u-
          (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)/(M n).xs^3)+
      K*(1+C)^2*((M n).data.s/(M n).xs+
        ((M n).data.N^(-delta)*comparisonSmallMass (M n).data.N (M n).data.E)/(M n).xs))
      atTop (𝓝 0) := by
    have H1 := ((hrmin.add htravel).pow 2).const_mul (16*C)
    have H2 := hthermal.const_mul 2
    have H3 := (hsRatio.add hfloor).const_mul (K*(1+C)^2)
    have H := (H1.add H2).add H3
    simpa only [zero_add,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,add_zero] using H
  apply squeeze_zero' _ _ Hratio
  · filter_upwards [Hv] with n hnV
    have hv : C*(M n).xs∈Icc (0:ℝ) 1 := ⟨(mul_pos hCpos (M n).hxs).le,hnV⟩
    exact div_nonneg (intervalIntegral.integral_nonneg hv.1
      (fun u _=>sq_nonneg _)) (pow_nonneg (M n).hxs.le 3)
  · filter_upwards [hdim.eventually Hamp,Hv] with n hnAmp hnV
    let v := C*(M n).xs
    have hv : v∈Icc (0:ℝ) 1 := ⟨(mul_pos hCpos (M n).hxs).le,hnV⟩
    have hs : (M n).data.s≤v :=
      (M n).hsxs.trans (by nlinarith only [hC,(M n).hxs])
    let p : (M n).Potential := Classical.choice (M n).exists_potential
    have hamp : ∀u∈Ioc (0:ℝ) v,
        (orderedPathS (dim n+1) (M n).bf (M n).hf u-
          (M n).data.wallRadius (M n).alpha u)^2 ≤
          K*((M n).xs+v)^2 := by
      intro u hu
      exact hnAmp (M n) u ⟨hu.1,hu.2.trans hv.2⟩ |>.trans
        (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by linarith [(M n).hxs,hu.1] : 0≤(M n).xs+u)
            (add_le_add_right hu.2 (M n).xs) 2) hK.le)
    have Hfinite := p.full_initial_mass_squared_mismatch_le hv hs
      (mul_nonneg hK.le (sq_nonneg _)) hamp
    have Hdiv := div_le_div_of_nonneg_right Hfinite (pow_nonneg (M n).hxs.le 3)
    convert Hdiv using 1
    · dsimp only [v]
      field_simp [(M n).hxs.ne']

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
