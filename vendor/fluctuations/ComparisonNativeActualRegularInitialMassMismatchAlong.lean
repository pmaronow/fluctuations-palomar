module

public import ComparisonNativeActualInitialMassMismatch
public import ComparisonNativeActualInitialMassError
public import ComparisonNativeActualRegularInitialMassConcentrationAlong
public import ComparisonNativeActualRegularMassGeometry
public import ComparisonNativeActualInitialMassChargesAlong
public import ComparisonNativeActualOriginalMassMismatch

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 8000000
namespace NativeOverlapMinimum

theorem regular_minimum_initial_mass_squared_mismatch_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,
      NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*W n,
      (orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)^2)/(W n)^3)
      atTop (𝓝 0) := by
  obtain ⟨B,hB,Hmean⟩:=eventually_actual_minimum_mass_mean_upper (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let K:=(B+Az+1/cl)*(1+C)
  have hK : 0 < K := by dsimp only [K];positivity
  have hroom' : 0 < 3*m+delta := by linarith only [hm,hdelta]
  have Htravel:=actual_cap_travel_ratio_tendsto_zero_along hC0 hroom' dim hdim M W hxs
  have Hfloor:=actual_floor_mass_ratio_tendsto_zero_along hC0 hroom' dim hdim M W hxs
  have Hthermal:=regular_minimum_initial_mass_thermal_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hxs hWlim hclock C hC
  have Htotal:=((Htravel.pow 2).const_mul (16*C)).add
    ((Hthermal.const_mul 2).add (Hfloor.const_mul (K^2)))
  simp only [zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,add_zero] at Htotal
  have HW:=(hWlim.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ) < 1 by simp))
  have HP:=hdim.eventually (eventually_exists_actual_common_geometry_regular
    (m:=m) (cl:=cl) (cu:=cu) (Az:=Az) (C0:=C0) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hdelta)
  have HmeanAlong:=hdim.eventually Hmean
  apply squeeze_zero' _ _ Htotal
  · filter_upwards [] with n
    have hw:=(M n).hxs.trans_le (hxs n)
    exact div_nonneg (intervalIntegral.integral_nonneg (by positivity)
      (fun u _=>sq_nonneg _)) (pow_pos hw 3).le
  · filter_upwards [HmeanAlong,HW,HP,hclock] with n hnmean hnW hnP hnClock
    have hw:=(M n).hxs.trans_le (hxs n)
    obtain ⟨p,_⟩:=hnP (M n) hnClock
    have hamp : ∀u∈Ioc (0:ℝ) (C*W n),
        (orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)^2 ≤ K^2*(W n)^2 := by
      intro u hu
      have hui : u∈Icc (0:ℝ) 1 := ⟨hu.1.le,hu.2.trans hnW⟩
      have HS:=hnmean (M n) u ⟨hu.1,hu.2.trans hnW⟩
      have HR:=(M n).inverse_radius_le_source_mass hcl hAz hui
      have Hsmall : (M n).xs+u ≤ (1+C)*W n := by nlinarith only [hxs n,hu.2]
      have Hmul:=mul_le_mul_of_nonneg_left Hsmall
        (show 0 ≤ B+Az+1/cl by positivity)
      have HS0:=(M n).mass_mean_nonneg hui
      have HR0:=(comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk
        (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha u).1
      have Habs : |orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u| ≤ K*W n := by
        apply abs_le.mpr
        dsimp only [K]
        constructor  <;> nlinarith only [HS,HR,HS0,HR0,Hmul]
      have Hsq:=pow_le_pow_left₀ (abs_nonneg _) Habs 2
      simpa only [sq_abs,mul_pow] using Hsq
    have Hint:=p.initial_mass_squared_mismatch_le ⟨by positivity,hnW⟩
      (show 0 ≤ K^2*(W n)^2 by positivity) hamp
    have HD:=div_le_div_of_nonneg_right Hint (pow_pos hw 3).le
    apply HD.trans_eq
    field_simp; ring

theorem regular_minimum_initial_mass_absolute_mismatch_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,
      NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*W n,
      |orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u|)/(W n)^2)
      atTop (𝓝 0) := by
  have Hsquare:=regular_minimum_initial_mass_squared_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hxs hWlim hclock C hC
  have Hlimit:=(Hsquare.const_mul C).sqrt
  simp only [mul_zero,Real.sqrt_zero] at Hlimit
  have HW:=(hWlim.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ) < 1 by simp))
  apply squeeze_zero' _ _ Hlimit
  · filter_upwards [] with n
    have hw:=(M n).hxs.trans_le (hxs n)
    exact div_nonneg (intervalIntegral.integral_nonneg (by positivity)
      (fun u _=>abs_nonneg _)) (sq_nonneg _)
  · filter_upwards [HW] with n hnW
    have hw:=(M n).hxs.trans_le (hxs n)
    have hi:=((M n).mass_squared_mismatch_intervalIntegrable).mono_set (by
      rw [uIcc_of_le (by positivity : 0 ≤ C*W n),uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hnW)
    have Hsq:=interval_integral_sqrt_sq_le (by positivity : 0 ≤ C*W n) hi
      (fun u _=>sq_nonneg _)
    simp only [Real.sqrt_sq_eq_abs] at Hsq
    apply Real.le_sqrt_of_sq_le
    rw [div_pow]
    apply (div_le_iff₀ (pow_pos (pow_pos hw 2) 2)).mpr
    convert Hsq using 1; field_simp [hw.ne']

theorem regular_original_retained_squared_mismatch_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W v : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,
      NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (C : ℝ) (hC : 0 < C) (hv : ∀n,v n∈Icc (0:ℝ) 1)
    (hvc : ∀n,v n ≤ C*W n) :
    Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ) ≤ v n},
      (orderedPathS (dim n+1) (M n).bf (M n).hf w-(M n).R w)^2
        ∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(W n)^3) atTop (𝓝 0) := by
  have Hfull:=regular_minimum_initial_mass_squared_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hxs hWlim hclock C hC
  have HW:=(hWlim.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ) < 1 by simp))
  apply squeeze_zero' _ _ Hfull
  · filter_upwards [] with n
    have hw:=(M n).hxs.trans_le (hxs n)
    exact div_nonneg (integral_nonneg (fun _=>sq_nonneg _)) (pow_pos hw 3).le
  · filter_upwards [HW] with n hnW
    have hw:=(M n).hxs.trans_le (hxs n)
    rw [comparison_original_retained_integral_eq_interval (hv n)
      (fun u=>(orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)^2)]
    apply div_le_div_of_nonneg_right _ (pow_pos hw 3).le
    have hi:=((M n).mass_squared_mismatch_intervalIntegrable).mono_set (by
      rw [uIcc_of_le (by positivity : 0 ≤ C*W n),uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl hnW)
    exact intervalIntegral.integral_mono_interval le_rfl (hv n).1 (hvc n)
      (ae_of_all _ (fun _=>sq_nonneg _)) hi

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
