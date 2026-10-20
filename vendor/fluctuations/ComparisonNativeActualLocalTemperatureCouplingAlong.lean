module

public import ComparisonNativeActualRegularInitialMassMismatchAlong
public import ComparisonNativeActualLocalTemperatureClockCoupling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 7000000
namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T t : ℝ}

theorem regular_initial_local_temperature_scalar_radius_coupling_along
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,
      NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (hT : 0 < T) (ht : 0 < t)
    (htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (C Cb Ch : ℝ) (hC : 0 < C) (hCb : 0 ≤ Cb) (hCh : 0 ≤ Ch)
    (hEq4 : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) (C*W n),
      |(M n).b u-t| ≤ Cb*(W n)^2 ∧ |(M n).h u| ≤ Ch*(W n)^3) :
    Tendsto (fun n=>(∫u in 0..C*W n,
      |actualScalarClockQuantile t (dim n+1) (M n).bf (M n).hf u-(M n).R u|)/(W n)^2)
      atTop (𝓝 0) := by
  obtain ⟨B,hB,Hmean⟩:=eventually_actual_minimum_mass_mean_upper (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cs:=B*(1+C)
  have hCs : 0 < Cs := by dsimp [Cs];positivity
  let E:=(Cb*Cs+Ch)/t
  let F:=1+T/t
  have hE : 0 ≤ E := by dsimp [E];positivity
  have Hmis:=regular_minimum_initial_mass_absolute_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W hxs hWlim hclock C hC
  have Herror:=(hWlim.pow 2).const_mul (E*C)
  simp only [zero_pow (by norm_num : (2:ℕ)≠0),mul_zero] at Herror
  have Htotal:=(Hmis.const_mul F).add Herror
  simp only [mul_zero,add_zero] at Htotal
  have HmeanAlong:=hdim.eventually Hmean
  have HW:=(hWlim.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ) < 1 by simp))
  apply squeeze_zero' _ _ Htotal
  · filter_upwards [] with n
    have hw:=(M n).hxs.trans_le (hxs n)
    exact div_nonneg (intervalIntegral.integral_nonneg (by positivity) (fun _ _=>abs_nonneg _))
      (sq_nonneg _)
  · filter_upwards [HmeanAlong,HW,hEq4,htotal] with n hn hnW hnEq hnTotal
    have hw:=(M n).hxs.trans_le (hxs n)
    have hS : ∀u∈Icc (0:ℝ) (C*W n),orderedPathS (dim n+1) (M n).bf (M n).hf u ≤ Cs*W n := by
      intro u hu
      by_cases hu0 : u=0
      · subst u
        simp only [orderedPathS,orderedPathPair_zero]
        positivity
      · have HS:=hn (M n) u ⟨lt_of_le_of_ne hu.1 (Ne.symm hu0),hu.2.trans hnW⟩
        have H:=mul_le_mul_of_nonneg_left (show (M n).xs+u ≤ (1+C)*W n by nlinarith [hxs n,hu.2]) hB.le
        exact HS.trans (by dsimp [Cs];nlinarith only [H])
    have Hint:=(M n).inherited_local_temperature_scalar_radius_integral_le_of_eq4 hT ht hnTotal
      ⟨by positivity,hnW⟩ hCb (fun u hu=>(hnEq u hu).1) (fun u hu=>(hnEq u hu).2) hS
    have H:=div_le_div_of_nonneg_right Hint (sq_nonneg (W n))
    exact H.trans_eq (by dsimp only [E,F];field_simp [hw.ne'])

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
