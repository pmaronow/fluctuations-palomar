module

public import ComparisonActualHighOnlyInitialMismatchAmplitude
public import ComparisonActualHighOnlyRegularInitialMassConcentrationAlong
public import ComparisonNativeActualInitialMassError
public import ComparisonActualHighOnlyInitialCharges
public import ComparisonNativeActualRegularMassGeometry
public import ComparisonNativeActualInitialMassChargesAlong
public import ComparisonNativeActualOriginalMassMismatch

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace ActualHighOnlyOverlapMinimum

private theorem initial_mass_squared_limit_from_thermal
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,
      NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (hsRatio : Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0))
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (C : ℝ) (hC : 0 < C)
    (Hthermal : Tendsto (fun n=>(∫u in 0..C*W n,
      orderedPathB (dim n+1) (M n).bf (M n).hf u-
        (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)/(W n)^3) atTop (𝓝 0)) :
    Tendsto (fun n=>(∫u in 0..C*W n,
      (orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)^2)/(W n)^3)
      atTop (𝓝 0) := by
  obtain ⟨K,hK,HAmp⟩:=eventually_actual_high_only_initial_mismatch_amplitude (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let A:=K*(1+C)^2
  have hA : 0≤A:=mul_nonneg hK.le (sq_nonneg _)
  have hroom' : 0<3*m+delta:=by linarith
  have Htravel:=actual_cap_travel_ratio_tendsto_zero_along hC0 hroom' dim hdim M W hxs
  have Hfloor:=actual_floor_mass_ratio_tendsto_zero_along hC0 hroom' dim hdim M W hxs
  have Htotal:=((Htravel.pow 2).const_mul (16*C)).add
    ((Hthermal.const_mul 2).add (((hsRatio.const_mul 2).add Hfloor).const_mul A))
  simp only [zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,add_zero] at Htotal
  have HW:=(hWlim.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ)<1 by simp))
  have HS:=hsRatio.eventually (eventually_le_nhds hC)
  have HmeanAlong:=hdim.eventually HAmp
  apply squeeze_zero' _ _ Htotal
  · filter_upwards [] with n
    have hw:=(M n).hxs.trans_le (hxs n)
    exact div_nonneg (intervalIntegral.integral_nonneg (by positivity)
      (fun u _=>sq_nonneg _)) (pow_pos hw 3).le
  · filter_upwards [HmeanAlong,HW,HS,Hcutoff] with n hnamp hnW hnS hnCut
    have hw:=(M n).hxs.trans_le (hxs n)
    obtain ⟨p⟩:=(M n).exists_potential_high_only hnCut.1
    have hamp : ∀u∈Ioc (0:ℝ) (C*W n),
        (orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)^2 ≤ A*(W n)^2 := by
      intro u hu
      have HB:=hnamp (M n) hnCut.1 hnCut.2 u ⟨hu.1,hu.2.trans hnW⟩
      have Hsmall : (M n).xs+u ≤ (1+C)*W n:=by nlinarith only [hxs n,hu.2]
      have Hsq:=pow_le_pow_left₀ (add_nonneg (M n).hxs.le hu.1.le) Hsmall 2
      have Hmul:=mul_le_mul_of_nonneg_left Hsq hK.le
      apply HB.trans
      simpa only [A,mul_pow,mul_assoc] using Hmul
    have hsV : (M n).data.s ≤ C*W n:=by
      exact (div_le_iff₀ hw).mp hnS
    have Hint:=p.initial_mass_squared_mismatch_le ⟨by positivity,hnW⟩ hsV
      (show 0≤A*(W n)^2 by positivity) hamp
    have HD:=div_le_div_of_nonneg_right Hint (pow_pos hw 3).le
    apply HD.trans_eq
    field_simp
    ring

private theorem initial_mass_absolute_limit_from_square
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,
      NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (hsRatio : Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0))
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (C : ℝ) (hC : 0 < C)
    (Hsquare : Tendsto (fun n=>(∫u in 0..C*W n,
      (orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)^2)/(W n)^3)
      atTop (𝓝 0)) :
    Tendsto (fun n=>(∫u in 0..C*W n,
      |orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u|)/(W n)^2)
      atTop (𝓝 0) := by
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

private theorem original_retained_squared_limit_from_initial
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W v : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,
      NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (C : ℝ) (hC : 0 < C) (hv : ∀n,v n∈Icc (0:ℝ) 1)
    (hvc : ∀n,v n ≤ C*W n)
    (hsRatio : Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0))
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (Hfull : Tendsto (fun n=>(∫u in 0..C*W n,
      (orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)^2)/(W n)^3)
      atTop (𝓝 0)) :
    Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ) ≤ v n},
      (orderedPathS (dim n+1) (M n).bf (M n).hf w-(M n).R w)^2
        ∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(W n)^3) atTop (𝓝 0) := by
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

theorem regular_minimum_initial_mass_squared_mismatch_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,
      NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (hsRatio : Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0))
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*W n,
      (orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u)^2)/(W n)^3)
      atTop (𝓝 0) := by
  have Hthermal:=regular_minimum_initial_mass_thermal_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hxs hWlim hclock hsRatio Hcutoff C hC
  exact initial_mass_squared_limit_from_thermal hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hxs hWlim hclock hsRatio Hcutoff C hC Hthermal

theorem regular_minimum_initial_mass_absolute_mismatch_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,
      NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (hsRatio : Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0))
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (C : ℝ) (hC : 0 < C) :
    Tendsto (fun n=>(∫u in 0..C*W n,
      |orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u|)/(W n)^2)
      atTop (𝓝 0) := by
  have Hsquare:=regular_minimum_initial_mass_squared_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hxs hWlim hclock hsRatio Hcutoff C hC
  exact initial_mass_absolute_limit_from_square hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W hxs hWlim hclock hsRatio Hcutoff C hC Hsquare

theorem regular_original_retained_squared_mismatch_ratio_tendsto_zero_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W v : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,
      NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (C : ℝ) (hC : 0 < C) (hv : ∀n,v n∈Icc (0:ℝ) 1)
    (hvc : ∀n,v n ≤ C*W n)
    (hsRatio : Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0))
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs) :
    Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ) ≤ v n},
      (orderedPathS (dim n+1) (M n).bf (M n).hf w-(M n).R w)^2
        ∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(W n)^3) atTop (𝓝 0) := by
  have Hfull:=regular_minimum_initial_mass_squared_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hxs hWlim hclock hsRatio Hcutoff C hC
  exact original_retained_squared_limit_from_initial hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M W v hxs hWlim hclock C hC hv hvc hsRatio Hcutoff Hfull

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
