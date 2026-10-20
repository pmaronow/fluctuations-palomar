module

public import ComparisonSignedCavityActualInheritedCanonicalProjectionGeometry
public import ComparisonActualHighOnlyStarScalarGeometry
public import ComparisonActualHighOnlyRetainedStarProjectionGeometry

@[expose] public section
set_option linter.unusedVariables false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeStarBuffer NativeOverlapMinimum
set_option maxHeartbeats 12000000

namespace ActualHighOnlyOverlapMinimum
theorem canonical_scale_strength_upper_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) :
    laplaceComparisonStrength M.context.d M.lam M.xs  ≤ 
      (max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs)))^2 := by
  have hg := (laplaceComparisonStrength_pos M.context.d M.hlam M.xs).le
  have H := pow_le_pow_left₀ (Real.sqrt_nonneg _)
    (le_max_right M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))) 2
  simpa only [Real.sq_sqrt hg] using H

theorem eventually_actual_inherited_canonical_slow_window_projection_geometry_along_high_only
    {m delta cl cu Az C0 Ct D Bclock L Ccal : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0)
    (hL : 0 < L) (hCcal : 1  ≤  Ccal)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ)
    (hcanonical : ∀n,W n=max (M n).xs
      (Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)))
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hcutoff : ∀ᶠn in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (hcompare : ∀n,(M n).xs^2  ≤  Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃Kv Cprof Lcount H0 : ℝ,1  ≤  Kv ∧ 0 < Cprof ∧ 0 < Lcount ∧ 0 < H0 ∧
      ∀ᶠn : ℕ in atTop,
      W n  ≤  Ccal*(M n).context.d ∧
      (1/Ccal^3)*(W n)^2  ≤  laplaceComparisonStrength (M n).context.d (M n).lam (W n) ∧
      (M n).xs  ≤  Kv*W n ∧ Kv*W n  ≤  1 ∧
      ∀T Cs : ℝ,∀w : ActualSlowWindowChoice,IsActualCalibratedSlowWindow_high_only (M n) (W n) T L Cs w →
      ∀future : PositiveMass,
        future.val=massNode (calibratedBandStart cu Az*W n) w.quarter (4*w.index+3) →
      ∀us : List PositiveMass,(∀u∈us,u.val  ≤  1) → w.star∈us → future∈us →
      ∀ᶠj : ℕ in atTop,
        let as := finiteCutMasses us j
        let q := completedPathClock (dim n+1) (M n).bf (M n).hf
        let steps := sampleClockSteps q 0 as
        Nonempty (OriginalStarProjectionGeometry steps
          (physicalRetainedIndex steps w.star.val).val (physicalRetainedIndex steps future.val).val
          (M n).xs (H0/(Kv*W n)) (Kv*W n)
          ((M n).context.N^(-(3*actualSlowWindowExponent m delta)))
          (M n).context.d (M n).lam (M n).context.E delta Cprof Lcount H0 Bclock) := by
  let ce := 1/Ccal^3
  have hCcalpos : 0 < Ccal := zero_lt_one.trans_le hCcal
  have hce : 0 < ce := by dsimp only [ce];positivity
  have hxs n : (M n).xs  ≤  W n := by rw [hcanonical];exact le_max_left _ _
  have hW n : 0 < W n := (M n).hxs.trans_le (hxs n)
  have hscale n : laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs  ≤  (W n)^2 := by
    rw [hcanonical]
    exact (M n).canonical_scale_strength_upper_high_only
  obtain ⟨Kv,Ks,Cprof,Lcount,hKv,hKs,hCp,hLc,Hscalar⟩ :=
    eventually_actual_slow_window_projection_scalars_along_high_only
      hm hdelta hroom hcl hcu hAz hC0 hL (show 0 < ce/24 by positivity)
      dim hdim M W hxs hWlim Hcutoff hscale
  let a := calibratedBandStart cu Az
  let F := 9+2*cu
  let H0 := actualStarProjectionAnchorConstant a Kv Ks cl cu F
  have ha : 0 < a := calibrated_band_start_pos hcu hAz
  have hKvpos : 0 < Kv := zero_lt_one.trans_le hKv
  have hKspos : 0 < Ks := hKvpos.trans_le hKs
  have hH0 : 0 < H0 := (actual_star_projection_anchor_bounds (F:=F)
    ha hKvpos hKspos hcl hcu.le (hW 0)).1
  have Hlog : ∀ᶠn : ℕ in atTop,1  ≤  Real.log ((dim n+1:ℕ):ℝ) :=
    ((tendsto_add_atTop_nat 1).comp hdim).eventually
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
  have Hdepth := ((tendsto_add_atTop_nat 1).comp hdim).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  have Hvunit := (hWlim.const_mul Kv).eventually
    (eventually_le_nhds (show Kv*(0:ℝ) < 1 by simp))
  refine ⟨Kv,Cprof,Lcount,H0,hKv,hCp,hLc,hH0,?_⟩
  filter_upwards [Hscalar,Hlog,Hdepth,Hvunit] with n hnScalar hnLog hnDepth hnVunit
  have Hcanonical := actual_direct_test_calibration_strength (M n).context.hd (M n).hlam
    (M n).hld (M n).hxs hCcal (hcompare n)
  rw [←hcanonical n] at Hcanonical
  have hxv : (M n).xs  ≤  Kv*W n := (hxs n).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hKv (hW n).le)
  refine ⟨Hcanonical.2.1,Hcanonical.2.2,hxv,hnVunit,?_⟩
  intro T Cs w hw future hfuture us hus hstar hfutureus
  obtain ⟨hanchor,_,hfork,hgap,hRv,hRs,hWv,hWs,hz,hfour,_,htcap,hcaproom,hcaplower,_,
    _,hshort,J,hJ,hreach,hJone,hcount⟩ := hnScalar T Cs w hw
  have hN : (1:ℝ)  ≤  ((dim n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos (dim n)
  have hnd : 1/((dim n+1:ℕ):ℝ)  ≤  (M n).context.d := by
    have H := hnDepth (M n).context.E (M n).context.d (M n).context.hE (M n).context.hd (M n).hlower
    have H' : comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d  ≤ 
        (M n).context.d := by
      unfold comparisonLowerScale
      exact (div_le_iff₀ (M n).context.hd).mpr (by simpa only [pow_two] using (M n).hupper)
    exact H.trans H'
  have Hanchor := actual_star_projection_anchor_bounds (F:=F) ha hKvpos hKspos hcl hcu.le (hW n)
  have hHlater : F/((cl/8)^2*(Ks*W n))  ≤  H0/(Kv*W n) := Hanchor.2.2.1
  have hHfirst : (1+4*cu)*(Ks*W n)  ≤  (H0/(Kv*W n))*(a*W n)^2 := Hanchor.2.2.2
  have hFmass : 1+2*cu  ≤  F := by dsimp only [F];linarith
  have hFradius : 1+1/((1:ℝ)/8)  ≤  F := by dsimp only [F];norm_num;linarith
  have hshort' : laplaceComparisonStrength (M n).context.d (M n).lam (Kv*W n)*
      ((M n).context.N^(-(3*actualSlowWindowExponent m delta)))*(Kv*W n)/
        (3*(M n).context.M (Cprof*(Kv*W n))*Real.log ((dim n+1:ℕ):ℝ))  ≤ 
      ce*(W n)^3/(24*Real.log ((dim n+1:ℕ):ℝ)) := by
    convert hshort using 1; ring
  have hhighStar : (M n).data.s ≤ w.star.val := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hxStar,_⟩ := hw
    exact ((M n).radius_high_mass ((M n).hxs.trans_le hxStar)).le
  apply eventually_retained_actual_minimum_inherited_star_projection_geometry_high_only (M n) hcl hcu.le
    hN hnLog hnd (hW n) hWs hfour hce Hcanonical.2.2 hz (by norm_num : (0:ℝ) < 1/8)
    hFmass hFradius ((hxs n).trans hWs) (mul_pos hKvpos (hW n)) hnVunit
    (Real.rpow_pos_of_pos (M n).context.hN _) hCp.le hcaproom (hcl.trans_le hcaplower)
    hshort' hHlater hHfirst le_rfl hJ hreach hJone hcount
    w.star future hhighStar (by rw [hfuture];exact hfork.le)
    (by rw [hfuture];linarith only [hRs]) (by rw [hfuture];exact hRv)
    (mul_pos ha (hW n)) hanchor (by rw [hfuture];exact htcap)
    (by rw [hfuture];exact hgap) us hus hstar hfutureus

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
