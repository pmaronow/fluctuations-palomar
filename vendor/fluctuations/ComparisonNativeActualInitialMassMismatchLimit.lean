module

public import ComparisonNativeActualInitialMassMismatch
public import ComparisonNativeActualInitialMassError

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 8000000
namespace NativeOverlapMinimum

theorem actual_minimum_initial_mass_squared_mismatch_ratio_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock T H : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n : ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=H)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*W n,
      (orderedPathS (n+1) (M n).bf (M n).hf u-(M n).R u)^2)/(W n)^3)
      atTop (𝓝 0) := by
  obtain ⟨B,hB,Hmean⟩:=eventually_actual_minimum_mass_mean_upper (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let K:=(B+Az+1/cl)*(1+C)
  have hK : 0 < K := by dsimp only [K];positivity
  have hroom' : 0 < 3*m+delta := by linarith only [hm,hdelta]
  have Htravel:=actual_cap_travel_ratio_tendsto_zero hC0 hroom' M W hxs
  have Hfloor:=actual_floor_mass_ratio_tendsto_zero hC0 hroom' M W hxs
  have Hthermal:=actual_minimum_initial_mass_thermal_ratio_tendsto_zero
    hm hdelta hroom hcl hcu hAz hC0 hCt M W hxs hWlim hb hh C hC
  have Htotal:=((Htravel.pow 2).const_mul (16*C)).add
    ((Hthermal.const_mul 2).add (Hfloor.const_mul (K^2)))
  simp only [zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,add_zero] at Htotal
  have HW:=(hWlim.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ) < 1 by simp))
  have HP:=eventually_exists_actual_common_geometry_constant
    (m:=m) (cl:=cl) (cu:=cu) (Az:=Az) (C0:=C0) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hdelta
  apply squeeze_zero' _ _ Htotal
  · filter_upwards [] with n
    have hw:=(M n).hxs.trans_le (hxs n)
    exact div_nonneg (intervalIntegral.integral_nonneg (by positivity)
      (fun u _=>sq_nonneg _)) (pow_pos hw 3).le
  · filter_upwards [Hmean,HW,HP] with n hnmean hnW hnP
    have hw:=(M n).hxs.trans_le (hxs n)
    obtain ⟨p,_⟩:=hnP (M n) T H (hb n) (hh n)
    have hamp : ∀u∈Ioc (0:ℝ) (C*W n),
        (orderedPathS (n+1) (M n).bf (M n).hf u-(M n).R u)^2 ≤ K^2*(W n)^2 := by
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
      have Habs : |orderedPathS (n+1) (M n).bf (M n).hf u-(M n).R u| ≤ K*W n := by
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

theorem actual_minimum_initial_mass_absolute_mismatch_ratio_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock T H : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n : ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=H)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*W n,
      |orderedPathS (n+1) (M n).bf (M n).hf u-(M n).R u|)/(W n)^2)
      atTop (𝓝 0) := by
  have Hsquare:=actual_minimum_initial_mass_squared_mismatch_ratio_tendsto_zero
    hm hdelta hroom hcl hcu hAz hC0 hCt M W hxs hWlim hb hh C hC
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

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
