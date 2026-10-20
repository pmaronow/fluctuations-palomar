module

public import ComparisonSignedCavityActualStarMassRateSelection
public import ComparisonNativeActualMinimumMassSlabPolynomial

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 10000000

namespace NativeOverlapMinimum

theorem actual_minimum_complete_mass_slab_thermal_ratio_tendsto_zero
    {m delta cl cu Az C0 Ct D Bclock T H : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (a : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(a n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hb : ∀n u,(a n).b u=T) (hh : ∀n u,(a n).h u=H)
    (c C : ℝ) (hc : 0 < c) (hcC : c ≤ C) :
    Tendsto (fun n =>
      (∫u in Ioo (c*W n) (C*W n),orderedPathB (n+1) (a n).bf (a n).hf u-
        (orderedPathS (n+1) (a n).bf (a n).hf u)^2)/(W n)^3) atTop (𝓝 0) := by
  have Hbound := eventually_actual_minimum_complete_mass_slab_polynomial (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt c C hc hcC
  have HW1 := hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  have HWC := (hWlim.const_mul C).eventually
    (eventually_le_nhds (by norm_num : C*(0:ℝ) < 1))
  have hrate : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/2)))
      atTop (𝓝 0) := by
    exact (tendsto_rpow_neg_atTop (half_pos (actualMassSavingExponent_pos hm hdelta))).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  apply squeeze_zero'
    (by
      filter_upwards [HWC] with n hn
      have hW : 0 < W n := (a n).hxs.trans_le (hxs n)
      apply div_nonneg _ (pow_pos hW 3).le
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      have hui : u∈Icc (0:ℝ) 1 := ⟨(mul_pos hc hW).le.trans hu.1.le,hu.2.le.trans hn⟩
      have hr := comparisonSweepQuantile_bounds (a n).context.hc (a n).context.hk
        (a n).context.hkc (a n).context.hm (a n).context.hM (a n).alpha u
      have HD := (a n).cavityRadiusPointDefect_nonneg hr
      simpa only [Pi.zero_apply,cavityRadiusPointDefect,comparisonSweepQuantile_mass_spec
        (a n).context.hc (a n).context.hk (a n).context.hkc (a n).context.hm
        (a n).context.hM (a n).alpha hui] using HD)
    (by
      filter_upwards [Hbound,HW1,HWC] with n hn hn1 hnC
      have hW : 0 < W n := (a n).hxs.trans_le (hxs n)
      have Hle := hn (a n) T H (hb n) (hh n) (W n) (hxs n) hn1 hnC
      have hends : c*W n ≤ C*W n := mul_le_mul_of_nonneg_right hcC hW.le
      rw [intervalIntegral.integral_of_le hends, integral_Ioc_eq_integral_Ioo] at Hle
      exact Hle)
    hrate

theorem eventually_actual_bare_calibrated_star
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hT : 0 < T)
    (M : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hscale : ∀n,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs ≤ (W n)^2)
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=0) :
    ∀ᶠn : ℕ in atTop,
      ∃p : (M n).Potential,
      ∃u∈Ioo (starMassBandConstant cu Az*W n) (2*starMassBandConstant cu Az*W n),
        p.H ((M n).R u) ≤ 0 ∧
        (3*(starMassBandConstant cu Az/cu)/4)*W n ≤
          orderedPathS (n+1) (M n).bf (M n).hf u ∧
        orderedPathS (n+1) (M n).bf (M n).hf u ≤
          (2*starMassBandConstant cu Az/cl+(starMassBandConstant cu Az/cu)/4)*W n ∧
        (3*T*(starMassBandConstant cu Az/cu)/8)*W n ≤
          actualMixedClock (n+1) (M n).bf (M n).hf u ∧
        |actualMixedClock (n+1) (M n).bf (M n).hf u-
          T*orderedPathS (n+1) (M n).bf (M n).hf u| ≤
          ((starMassBandConstant cu Az/cu+1)/4)*(W n)^3 := by
  let A := starMassBandConstant cu Az
  let c := A/cu
  have hA : 0 < A := star_mass_band_constant_pos hcu hAz
  have hc : 0 < c := div_pos hA hcu
  have hpositive : 0 < 3*m+delta := by linarith
  have Hthermal := actual_minimum_complete_mass_slab_thermal_ratio_tendsto_zero
    hm hdelta hroom hcl hcu hAz hC0 hCt M W hxs hWlim hb hh A (2*A) hA (by linarith)
  have Htravel := eventually_actual_minimum_cap_travel_small
    (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) (epsilon:=c/32)
    hC0 hpositive (by positivity)
  have Hfloor := eventually_actual_minimum_floor_mass_small
    (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) (epsilon:=A/2)
    hC0 hpositive (by positivity)
  have HW1 := hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  have HWband := (hWlim.const_mul (2*A)).eventually
    (eventually_le_nhds (by norm_num : (2*A)*(0:ℝ) < 1))
  have HWclock := ((hWlim.pow 2).const_mul (1+1/c)).eventually
    (eventually_le_nhds (show (1+1/c)*(0:ℝ)^2 < T/2 by simpa using half_pos hT))
  have Hsmallthermal := Hthermal.eventually
    (eventually_lt_nhds (show (0:ℝ) < c^2*A/128 by positivity))
  have Hpotential := eventually_exists_actual_common_geometry_constant
    (m:=m) (cl:=cl) (cu:=cu) (Az:=Az) (C0:=C0) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hdelta
  filter_upwards [Htravel,Hfloor,HW1,HWband,HWclock,Hsmallthermal,Hpotential]
    with n hntravel hnfloor hnW1 hnWband hnWclock hnthermal hnpotential
  obtain ⟨p,_⟩ := hnpotential (M n) T 0 (hb n) (hh n)
  have hW : 0 < W n := (M n).hxs.trans_le (hxs n)
  have htravel : (M n).cavityCapTravel ≤ c*W n/32 := by
    exact (hntravel (M n)).1.trans (by
      have HH := mul_le_mul_of_nonneg_left (hxs n) (show 0 ≤ c/32 by positivity)
      simpa only [div_mul_eq_mul_div] using HH)
  have hfloor : (M n).context.N^(-delta)*(M n).context.U ≤ (A/2)*W n :=
    hnfloor (M n) (W n) (hxs n)
  have hthermalbound : (∫u in Ioo (A*W n) (2*A*W n),
      orderedPathB (n+1) (M n).bf (M n).hf u-
        (orderedPathS (n+1) (M n).bf (M n).hf u)^2) <
      ((c*W n)^2/64)*(A*W n-(M n).context.N^(-delta)*(M n).context.U) := by
    have HI := (div_lt_iff₀ (pow_pos hW 3)).mp hnthermal
    have Hbudget : c^2*A/128*(W n)^3 ≤
        ((c*W n)^2/64)*(A*W n-(M n).context.N^(-delta)*(M n).context.U) := by
      calc
        _ = ((c*W n)^2/64)*((A/2)*W n) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact HI.trans_le Hbudget
  exact ⟨p,p.exists_bare_star_on_regular_mass_slab hcl hcu hAz hW hnW1 (hxs n)
    hnWband htravel (hscale n) hnWclock (hb n) (hh n) hthermalbound⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
