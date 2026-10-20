module

public import ComparisonSignedCavityActualStarMassBand
public import ComparisonNativeActualMassBudgetScale

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 6000000

namespace NativeOverlapMinimum

theorem eventually_actual_minimum_floor_mass_small
    {m delta cl cu Az C0 Ct D Bclock epsilon : ℝ}
    (hC0 : 0 < C0) (hroom : 0 < 3*m+delta) (hepsilon : 0 < epsilon) :
    ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀W : ℝ,M.xs ≤ W → M.context.N^(-delta)*M.context.U ≤ epsilon*W := by
  have H := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^3) (d:=epsilon) (q:=-(3*m+delta)) (r:=0)
      hepsilon (by linarith))
  filter_upwards [H] with n hn
  intro M W hxs
  have hW : 0 < W := M.hxs.trans_le hxs
  have hratio : M.context.U/W ≤ C0^3*M.context.N^(-3*m) :=
    (div_le_div_of_nonneg_left M.context.hU.le M.hxs hxs).trans
      (M.canonical_mass_small_ratio hC0)
  have Hmul := mul_le_mul_of_nonneg_left hratio
    (Real.rpow_nonneg M.context.hN.le (-delta))
  have He : M.context.N^(-delta)*(C0^3*M.context.N^(-3*m)) =
      C0^3*M.context.N^(-(3*m+delta)) := by
    rw [←mul_assoc, mul_comm (M.context.N^(-delta)) (C0^3), mul_assoc,
      ←Real.rpow_add M.context.hN]
    congr 2
    ring
  rw [He] at Hmul
  have Hcoeff : C0^3*M.context.N^(-(3*m+delta)) ≤ epsilon := by
    simpa only [NativeOverlapContext.N, Real.rpow_zero, mul_one] using hn
  have Hratio' : (M.context.N^(-delta)*M.context.U)/W ≤ epsilon := by
    simpa only [mul_div_assoc] using Hmul.trans Hcoeff
  exact (div_le_iff₀ hW).mp Hratio'

theorem eventually_actual_bare_star_on_regular_mass_slab
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hroom : 0 < 3*m+delta) (hT : 0 < T)
    (M : (n : ℕ) → NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (p : (n : ℕ) → (M n).Potential) (W : ℕ → ℝ)
    (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hscale : ∀n,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs ≤ (W n)^2)
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=0)
    (hthermal : Tendsto (fun n =>
      (∫u in Ioo (starMassBandConstant cu Az*W n) (2*starMassBandConstant cu Az*W n),
        orderedPathB (n+1) (M n).bf (M n).hf u-
          (orderedPathS (n+1) (M n).bf (M n).hf u)^2)/(W n)^3) atTop (𝓝 0)) :
    ∀ᶠn : ℕ in atTop,
      ∃u∈Ioo (starMassBandConstant cu Az*W n) (2*starMassBandConstant cu Az*W n),
        (p n).H ((M n).R u) ≤ 0 ∧
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
  have Htravel := eventually_actual_minimum_cap_travel_small
    (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) (epsilon:=c/32)
    hC0 hroom (by positivity)
  have Hfloor := eventually_actual_minimum_floor_mass_small
    (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) (epsilon:=A/2)
    hC0 hroom (by positivity)
  have HW1 := hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  have HWband := (hWlim.const_mul (2*A)).eventually
    (eventually_le_nhds (by norm_num : (2*A)*(0:ℝ) < 1))
  have HWclock := ((hWlim.pow 2).const_mul (1+1/c)).eventually
    (eventually_le_nhds (show (1+1/c)*(0:ℝ)^2 < T/2 by simpa using half_pos hT))
  have Hthermal := hthermal.eventually
    (eventually_lt_nhds (show (0:ℝ) < c^2*A/128 by positivity))
  filter_upwards [Htravel,Hfloor,HW1,HWband,HWclock,Hthermal]
    with n hntravel hnfloor hnW1 hnWband hnWclock hnthermal
  have hW : 0 < W n := (M n).hxs.trans_le (hxs n)
  have htravel : (M n).cavityCapTravel ≤ c*W n/32 := by
    exact (hntravel (M n)).1.trans (by
      have H := mul_le_mul_of_nonneg_left (hxs n) (show 0 ≤ c/32 by positivity)
      simpa only [div_mul_eq_mul_div] using H)
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
  exact (p n).exists_bare_star_on_regular_mass_slab hcl hcu hAz hW hnW1 (hxs n)
    hnWband htravel (hscale n) hnWclock (hb n) (hh n) hthermalbound

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
