module

public import ComparisonSignedCavityActualStarMassRateSelection
public import ComparisonSignedCavityActualStarCompleteProducer

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 10000000

namespace NativeOverlapMinimum

theorem eventually_actual_bare_polynomial_calibrated_star
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
        orderedPathB (n+1) (M n).bf (M n).hf u-
          (orderedPathS (n+1) (M n).bf (M n).hf u)^2 ≤
            (M n).context.N^(-(actualMassSavingExponent m delta/4))*(W n)^2 ∧
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
  let η := actualMassSavingExponent m delta
  have hη : 0 < η := actualMassSavingExponent_pos hm hdelta
  have Hslab := eventually_actual_minimum_complete_mass_slab_polynomial (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt A (2*A) hA (by linarith)
  have Hcoef := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=A/4) (q:=-(η/4)) (r:=0)
      (by positivity) (by linarith))
  have Hsize := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=c^2/64) (q:=-(η/4)) (r:=0)
      (by positivity) (by linarith))
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
  have Hpotential := eventually_exists_actual_common_geometry_constant
    (m:=m) (cl:=cl) (cu:=cu) (Az:=Az) (C0:=C0) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hdelta
  filter_upwards [Htravel,Hfloor,HW1,HWband,HWclock,Hslab,Hcoef,Hsize,Hpotential]
    with n hntravel hnfloor hnW1 hnWband hnWclock hnslab hncoef hnsize hnpotential
  obtain ⟨p,_⟩ := hnpotential (M n) T 0 (hb n) (hh n)
  have hW : 0 < W n := (M n).hxs.trans_le (hxs n)
  have htravel : (M n).cavityCapTravel ≤ c*W n/32 := by
    exact (hntravel (M n)).1.trans (by
      have HH := mul_le_mul_of_nonneg_left (hxs n) (show 0 ≤ c/32 by positivity)
      simpa only [div_mul_eq_mul_div] using HH)
  have hfloor : (M n).context.N^(-delta)*(M n).context.U ≤ (A/2)*W n :=
    hnfloor (M n) (W n) (hxs n)
  let t := (M n).context.N^(-(η/4))*(W n)^2
  have ht : 0 < t := by dsimp [t];positivity
  have hcoef : (M n).context.N^(-(η/4)) ≤ A/4 := by
    simpa only [NativeOverlapContext.N,Real.rpow_zero,mul_one,one_mul] using hncoef
  have hsize : (M n).context.N^(-(η/4)) ≤ c^2/64 := by
    simpa only [NativeOverlapContext.N,Real.rpow_zero,mul_one,one_mul] using hnsize
  have htpow : (M n).context.N^(-(η/2)) = ((M n).context.N^(-(η/4)))^2 := by
    rw [pow_two,←Real.rpow_add (M n).context.hN]
    congr 1
    ring
  have Hslab' := hnslab (M n) T 0 (hb n) (hh n) (W n) (hxs n) hnW1 hnWband
  have hends : A*W n ≤ (2*A)*W n := by nlinarith [mul_pos hA hW]
  rw [intervalIntegral.integral_of_le hends,integral_Ioc_eq_integral_Ioo] at Hslab'
  have HI := (div_le_iff₀ (pow_pos hW 3)).mp Hslab'
  have hthermalbound : (∫u in Ioo (A*W n) (2*A*W n),
      orderedPathB (n+1) (M n).bf (M n).hf u-
        (orderedPathS (n+1) (M n).bf (M n).hf u)^2) <
      t*((2*A*W n-A*W n)-(M n).context.N^(-delta)*(M n).context.U) := by
    calc
      _ ≤ (M n).context.N^(-(η/2))*(W n)^3 := HI
      _ = t*((M n).context.N^(-(η/4))*W n) := by rw [htpow];dsimp [t];ring
      _ ≤ t*((A/4)*W n) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoef hW.le) ht.le
      _ < t*((A/2)*W n) := mul_lt_mul_of_pos_left (by nlinarith [mul_pos hA hW]) ht
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) ht.le
  have hband : ∀u∈Ioo (A*W n) (2*A*W n), c*W n ≤ (M n).R u ∧
      (M n).R u ≤ (2*A/cl)*W n := by
    intro u hu
    exact (M n).actual_star_mass_band_radius_bounds hcl hcu hAz hW (hxs n) hnWband hu
  obtain ⟨u,hu,hH,hdefect,hmismatch⟩ := p.exists_thermal_good_star_off_floor
    (mul_pos hA hW).le (by nlinarith [mul_pos hA hW] : A*W n < 2*A*W n)
    hnWband ht.le (fun u hu => by linarith [(hband u hu).1,mul_pos hc hW]) hthermalbound
  have htbound : t ≤ (c*W n)^2/64 := by
    calc
      t ≤ (c^2/64)*(W n)^2 := mul_le_mul_of_nonneg_right hsize (sq_nonneg (W n))
      _ = _ := by ring
  have htravel0 := (M n).cavityCapTravel_nonneg
  have htravel2 := pow_le_pow_left₀ htravel0 htravel 2
  have hsq : (orderedPathS (n+1) (M n).bf (M n).hf u-(M n).R u)^2 ≤ (c*W n/4)^2 := by
    nlinarith only [hmismatch,htravel2,htbound,sq_nonneg (c*W n)]
  have habs : |orderedPathS (n+1) (M n).bf (M n).hf u-(M n).R u| ≤ c*W n/4 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ c*W n/4)).mp
    simpa only [sq_abs] using hsq
  have hmeanlo : (3*c/4)*W n ≤ orderedPathS (n+1) (M n).bf (M n).hf u := by
    nlinarith only [(abs_le.mp habs).1,(abs_le.mp habs).2,(hband u hu).1]
  have hmeanhi : orderedPathS (n+1) (M n).bf (M n).hf u ≤ (2*A/cl+c/4)*W n := by
    nlinarith only [(abs_le.mp habs).1,(abs_le.mp habs).2,(hband u hu).2]
  have hui : u∈Icc (0:ℝ) 1 := ⟨(mul_pos hA hW).le.trans hu.1.le,hu.2.le.trans hnWband⟩
  obtain ⟨hK,hcomp⟩ := (M n).bare_selected_mass_clock_calibration hui hc hW hnW1 (hxs n)
    (hband u hu).1 (hscale n) hnWclock (hb n u) (hh n u) hmeanlo habs
  exact ⟨p,u,hu,hH,hdefect,hmeanlo,hmeanhi,hK,hcomp⟩

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
