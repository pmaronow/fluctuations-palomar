module

public import ComparisonSignedCavityActualSlowWindowGeometry
public import ComparisonSignedCavityActualRegularSharpCentralSelection
public import ComparisonSignedCavityActualRegularCalibratedBand
public import ComparisonSignedCavityActualNearBareTightClock

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy NativeStarBuffer
set_option maxHeartbeats 9000000

namespace NativeOverlapMinimum

theorem eventually_actual_regular_positive_band_sharp_slow_window
    {m delta cl cu Az C0 Ct D Bclock T L c1 Ctest : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCtest : 0 ≤ Ctest) (hT : 0 < T) (hL : 0 < L) (hc1 : 0 < c1)
    (hc1thermal : c1 < actualMassSavingExponent m delta/8) (hc1floor : c1 < 3*m+delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ctest*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (hnearbare : ∀c C eps : ℝ,0 < c → 0 ≤ C → 0 < eps → ∀ᶠn in atTop,
      ∀u∈Icc (c*W n) (min (C*W n) 1),
      |(M n).b u-T| ≤ eps*(W n)^2 ∧ |(M n).h u| ≤ eps*(W n)^3) :
    ∃Cs : ℝ,0 < Cs ∧ ∀ᶠn : ℕ in atTop,
      let a := calibratedBandStart cu Az
      let b := a+4*L
      let c := starMassBandConstant cu Az/cu
      let S := orderedPathS (dim n+1) (M n).bf (M n).hf
      ∃N : ℕ,∃quarter : ℝ,∃i : ℕ,∃p : (M n).Potential,∃u : PositiveMass,
        i < N ∧ 0 < N ∧ 0 < quarter ∧
        (M n).context.N^(-c1)*W n ≤ quarter ∧ 4*(N:ℝ)*quarter=4*L*W n ∧
        (∀j ≤ 4*N,massNode (a*W n) quarter j ∈ Icc (a*W n) (b*W n)) ∧
        u.val ∈ Ioo (massNode (a*W n) quarter (4*i+1)+quarter/2)
          (massNode (a*W n) quarter (4*i+3)-quarter/2) ∧
        p.H ((M n).R u.val) ≤ 0 ∧
        orderedPathB (dim n+1) (M n).bf (M n).hf u.val-(S u.val)^2 ≤
          (M n).context.N^(-(actualMassSavingExponent m delta/4))*(W n)^2 ∧
        (3*c/4)*W n ≤ S u.val ∧ S u.val ≤ Cs*W n ∧
        (a/cu)*W n ≤ (M n).R u.val ∧ (M n).R u.val ≤ (b/cl)*W n ∧
        (M n).xs ≤ (M n).R u.val ∧ (M n).z ≤ (M n).R u.val/2 ∧
        (3*T*c/8)*W n ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf u.val ∧
        |actualMixedClock (dim n+1) (M n).bf (M n).hf u.val-T*S u.val| ≤
          ((c+1)/4)*(W n)^3 ∧
        (∀v∈Icc (massNode (a*W n) quarter (4*i)) (massNode (a*W n) quarter (4*(i+1))),
          |S v-S u.val| ≤ (M n).context.N^(-c1/2)*W n) ∧
        orderedPathB (dim n+1) (M n).bf (M n).hf u.val-(S u.val)^2 ≤
          (M n).context.N^(-(actualMassSavingExponent m delta/4))*((M n).xs^4/(W n)^2) := by
  have hxs n : (M n).xs ≤ W n := by
    rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hscale n : laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs ≤ (W n)^2 := by
    rw [hcanonical]
    have Hg : 0 ≤ laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs :=
      (laplaceComparisonStrength_pos _ (M n).hlam _).le
    have H:=pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_max_right (M n).xs
      (Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs))) 2
    simpa only [Real.sq_sqrt Hg,canonicalDirectTestBandScale] using H
  let A := starMassBandConstant cu Az
  let a := calibratedBandStart cu Az
  let b := a+4*L
  let c := A/cu
  let η := actualMassSavingExponent m delta
  have hA : 0 < A := star_mass_band_constant_pos hcu hAz
  have ha : 0 < a := calibrated_band_start_pos hcu hAz
  have hc : 0 < c := div_pos hA hcu
  have hab : a ≤ b := by dsimp only [b];linarith
  have hAa : A ≤ a := by dsimp only [a,calibratedBandStart,A];linarith
  have hη : 0 < η := actualMassSavingExponent_pos hm hdelta
  obtain ⟨Cs,hCs,Hband⟩ := eventually_actual_regular_calibrated_mass_band
    hm hdelta hroom hcl hcu hAz hC0 hCt hL dim hdim M W hxs hWlim hclock
  have Hblock := (tendsto_add_atTop_nat 1).eventually
    (eventually_exists_native_continuum_star (A:=L) (B:=Cs) hL hc1)
  have houter : 2*cu*(Az+1) ≤ a := by
    dsimp only [a,calibratedBandStart,starMassBandConstant]
    nlinarith
  have Hcentral := eventually_actual_regular_sharp_central_mass_selection (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCtest a b c1 hAa hab houter hc1 hc1thermal hc1floor
  have Hpotential := eventually_exists_actual_common_geometry_regular
    (m:=m) (cl:=cl) (cu:=cu) (Az:=Az) (C0:=C0) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hdelta
  have Htravel := eventually_actual_minimum_cap_travel_small
    (m:=m) (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    (epsilon:=c/64) hC0 (by linarith) (by positivity)
  have Hsize := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=c^2/256) (q:=-(η/4)) (r:=0)
      (by positivity) (by linarith))
  have HW1 := hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  have HWband := (hWlim.const_mul (2*b)).eventually
    (eventually_le_nhds (show 2*b*(0:ℝ) < 1 by simp))
  let eps:=(c+1)/(8*(Cs+1))
  have heps : 0 < eps:=by dsimp [eps];positivity
  have Hnear:=hnearbare a b eps ha (ha.le.trans hab) heps
  have HWclock := ((hWlim.pow 2).const_mul (eps+1+1/c)).eventually
    (eventually_le_nhds (show (eps+1+1/c)*(0:ℝ)^2 < T/2 by simpa using half_pos hT))
  refine ⟨Cs,hCs,?_⟩
  filter_upwards [Hband,hdim.eventually Hblock,hdim.eventually Hcentral,hdim.eventually Hpotential,
    hdim.eventually Htravel,hdim.eventually Hsize,HW1,HWclock,HWband,hclock,Hnear]
    with n hnBand hnBlock hnCentral hnPotential hnTravel hnSize hnW1 hnClock hn2small hnclock hnnear
  dsimp only at hnBand ⊢
  have hW : 0 < W n := (M n).hxs.trans_le (hxs n)
  have hsmall : b*W n ≤ 1 := hnBand.2.1
  have hend : a*W n+4*L*W n ≤ 1 := by nlinarith only [hsmall]
  have hvariation : orderedPathS (dim n+1) (M n).bf (M n).hf (a*W n+4*L*W n)-
      orderedPathS (dim n+1) (M n).bf (M n).hf (a*W n) ≤ Cs*W n := by
    have H := hnBand.2.2.2
    have he : a*W n+4*L*W n=b*W n := by dsimp only [b];ring
    rw [he]
    exact H
  obtain ⟨N,quarter,i,hi,hN,hq,hqlower,htotal,hosc⟩ := hnBlock
    (orderedPathS (dim n+1) (M n).bf (M n).hf) (a*W n) (W n) hnBand.1
      (mul_pos ha hW).le hW hend hvariation
  have hnodes : ∀j ≤ 4*N,massNode (a*W n) quarter j ∈ Icc (a*W n) (b*W n) := by
    intro j hj
    exact calibrated_mass_node_mem hq.le hj htotal
  let s := massNode (a*W n) quarter (4*i+1)+quarter/2
  let t := massNode (a*W n) quarter (4*i+3)-quarter/2
  have hlength : t-s=quarter := calibrated_mass_middle_length _ _ _
  have hst : s < t := by linarith only [hlength,hq]
  have hs : a*W n ≤ s := by
    have H := (hnodes (4*i+1) (by omega)).1
    dsimp only [s]
    linarith only [H,hq]
  have ht : t ≤ b*W n := by
    have H := (hnodes (4*i+3) (by omega)).2
    dsimp only [t]
    linarith only [H,hq]
  have hwidth : (M n).context.N^(-c1)*W n ≤ t-s := by
    rw [hlength]
    exact hqlower
  obtain ⟨p,_⟩ := hnPotential (M n) hnclock
  obtain ⟨v,hv,hH,hsharp,hmismatchsharp⟩ := hnCentral (M n) hnclock
    (W n) (hcanonical n) (hcompare n) hnW1 hn2small p s t hs ht hst hwidth
  have hnormalization : (M n).xs^4/(W n)^2 ≤ (W n)^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hW)).mpr
    have H := pow_le_pow_left₀ (M n).hxs.le (hxs n) 4
    nlinarith only [H]
  have hthreshold := mul_le_mul_of_nonneg_left hnormalization
    (Real.rpow_nonneg (M n).context.hN.le (-(η/4)))
  have hthermal := hsharp.trans hthreshold
  have hmismatch : (orderedPathS (dim n+1) (M n).bf (M n).hf v-(M n).R v)^2 ≤
      16*(M n).cavityCapTravel^2+2*((M n).context.N^(-(η/4))*(W n)^2) := by
    linarith only [hmismatchsharp,hthreshold]
  have hvblock := calibrated_mass_central_subset hq.le (calibrated_mass_middle_subset hq.le hv)
  have hvband := calibrated_mass_block_subset hq.le hi htotal hvblock
  have hvunit : v ∈ Icc (0:ℝ) 1 := ⟨(mul_pos ha hW).le.trans hvband.1,hvband.2.trans hsmall⟩
  have hvpos : 0 < v := (mul_pos ha hW).trans_le hvband.1
  let u : PositiveMass := ⟨v,hvpos⟩
  have Hbandv := hnBand.2.2.1 v hvband
  have htravel : (M n).cavityCapTravel ≤ c*W n/64 := by
    exact (hnTravel (M n)).1.trans (by
      simpa only [div_mul_eq_mul_div] using
        mul_le_mul_of_nonneg_left (hxs n) (show 0 ≤ c/64 by positivity))
  have hsize : (M n).context.N^(-(η/4)) ≤ c^2/256 := by
    simpa only [NativeOverlapContext.N,Real.rpow_zero,mul_one,one_mul] using hnSize
  have htbound : (M n).context.N^(-(η/4))*(W n)^2 ≤ (c*W n)^2/256 := by
    have H := mul_le_mul_of_nonneg_right hsize (sq_nonneg (W n))
    nlinarith only [H]
  have htravel2 := pow_le_pow_left₀ (M n).cavityCapTravel_nonneg htravel 2
  have hsq : (orderedPathS (dim n+1) (M n).bf (M n).hf v-(M n).R v)^2 ≤ (c*W n/8)^2 := by
    nlinarith only [hmismatch,htravel2,htbound,sq_nonneg (c*W n)]
  have habs : |orderedPathS (dim n+1) (M n).bf (M n).hf v-(M n).R v| ≤ c*W n/8 := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ c*W n/8)).mp
    simpa only [sq_abs] using hsq
  have hrad : c*W n ≤ (M n).R v :=
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hAa hcu.le) hW.le).trans Hbandv.2.2.1
  have Hnearv:=hnnear v ⟨hvband.1,le_min hvband.2 hvunit.2⟩
  have hbudget : eps*Cs+eps ≤ (c+1)/8 := by
    dsimp only [eps]
    have hCs1 : Cs+1 ≠ 0:=ne_of_gt (by positivity)
    apply le_of_eq
    field_simp
  obtain ⟨hclockstar,hcomp⟩ := (M n).near_bare_selected_mass_tight_clock_calibration
    hvunit hc hW hnW1 (hxs n) heps.le hrad (hscale n) hnClock
    Hnearv.1 Hnearv.2 Hbandv.1 Hbandv.2.1 habs hbudget
  refine ⟨N,quarter,i,p,u,hi,hN,hq,hqlower,htotal,hnodes,hv,hH,hthermal,
    Hbandv.1,Hbandv.2.1,Hbandv.2.2.1,Hbandv.2.2.2.1,Hbandv.2.2.2.2.1,Hbandv.2.2.2.2.2,
    hclockstar,hcomp,?_,hsharp⟩
  intro w hw
  exact hosc w hw v hvblock

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
