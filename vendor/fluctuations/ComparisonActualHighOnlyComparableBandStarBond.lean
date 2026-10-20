module

public import ComparisonNativeActualComparableBandStarBond
public import ComparisonActualHighOnlyStarContext
public import ComparisonActualHighOnlySharpClockCalibration

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeOverlapMinimum ActualHighOnlyOverlapMinimum
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
namespace ActualHighOnlyOverlapMinimum
theorem actual_compensated_bond_near_temperature
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u c W T Cb : ℝ} (hc : 0 < c) (hW : 0 < W) (hW1 : W ≤ 1)
    (hxs : M.xs ≤ W) (hT : 0 ≤ T) (hCb : 0 ≤ Cb)
    (hr : c*W ≤ M.R u)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs ≤ W^2)
    (hb : |M.b u-T| ≤ Cb*W^2) :
    |(M.bf u:ℝ)-T| ≤ (Cb+1+1/c)*W^2 := by
  have hR:=M.shiftedNativeModel.R_bounds u
  have hg:=M.strength_le_scale_of_radius_lower hc hW hW1 hxs ⟨hr,hR.2⟩ hscale
  have he0 := M.coefficient_nonneg u
  have he : M.coefficient u≤laplaceComparisonStrength M.context.d M.lam (M.R u) := by
    unfold coefficient ActualHighOnlyComparisonData.coefficient omittedStrengthCoefficient
    split_ifs
    · exact le_rfl
    · exact (laplaceComparisonStrength_pos M.context.d M.hlam _).le
  have hg0:=(laplaceComparisonStrength_pos M.context.d M.hlam (M.R u)).le
  have hcinv : 0 ≤ 1/c:=by positivity
  have hC : 0 ≤ (Cb+1+1/c)*W^2:=by positivity
  change |max (M.b u-M.coefficient u) 0-T| ≤ _
  apply abs_le.mpr
  constructor
  · have H:=le_max_left (M.b u-M.coefficient u) 0
    nlinarith [(abs_le.mp hb).1]
  · have H : max (M.b u-M.coefficient u) 0 ≤
        T+(Cb+1+1/c)*W^2 := by
      apply max_le
      · nlinarith [(abs_le.mp hb).2,mul_nonneg hcinv (sq_nonneg W)]
      · positivity
    linarith

end ActualHighOnlyOverlapMinimum
theorem actual_minimum_susceptibility_coefficient_change_bound_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp T W Cb : ℝ} (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (star U : ℕ)
    (hs : star < U) (hU : U ≤ as.length)
    (hb : |(M.bf (partitionPoint 0 as star):ℝ)-T| ≤ Cb*W^2) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2| ≤ |T*chi^2-1|+Cb*W^2 := by
  dsimp only
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hK0:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone
    M.inherited_hf_monotone as ho
  have hterm : K as.length ≤ Temp:=
    (native_continuum_mixed_clock_terminal_le n M.bf M.hf M.inherited_bf_monotone
      M.inherited_hf_monotone as ho).trans (M.inherited_total_clock_le htotal 1 (by norm_num))
  have HH:=scalar_boundary_hessian_uniform_bounds ho (relocatedClock U 0 K)
    (relocatedClock_monotone U (by norm_num : (0:ℝ)∈Icc 0 1) hKm hK0)
    (by simp [relocatedClock,show 0 < U by omega])
    (B:=Temp) (by simpa [relocatedClock,not_lt.mpr hU] using hterm)
  exact susceptibility_coefficient_change_bound
    ((Real.exp_pos (-4*Temp)).le.trans HH.1) HH.2 hb

theorem actual_selected_bad_history_star_bond_near_temperature_along_comparable_context_high_only
    {m delta cl cu Az C0 Ct D Bclock T L Cs c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) T L Cs (w n)) :
    let Cb:=2+1/(calibratedBandStart cu Az/cu)
    0 < Cb ∧ ∀ᶠn in atTop,|((M n).bf (w n).star.val:ℝ)-T| ≤ Cb*(W n)^2 := by
  have hTemp : 0 < T := G.hT
  dsimp only
  let a:=calibratedBandStart cu Az
  let b:=a+4*L
  let c:=a/cu
  have ha : 0 < a:=calibrated_band_start_pos hcu hAz
  have hc : 0 < c:=div_pos ha hcu
  have hb0 : 0 ≤ b:=by dsimp only [b];positivity
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hay : ∀ᶠn in atTop,comparisonLowerScale (M n).context.N (M n).context.E (M n).context.d ≤ W n:=
    Eventually.of_forall (fun n=>(M n).hscale.trans (hxs n))
  have Hnear:=G.comparable W hWlim hay a b 1 ha hb0 zero_lt_one
  have HWband:=((hWlim.const_mul b).eventually (eventually_le_nhds (by simp : b*(0:ℝ)<1)))
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨by positivity,?_⟩
  filter_upwards [Hnear,HW,hw,HWband] with n hnnear hnW hnw hnBand
  have hWn : 0 < W n:=(M n).hxs.trans_le (hxs n)
  obtain ⟨p,hindex,_,hquarter,_,_,hnodes,hstar,_,_,_,_,hRlo,_⟩:=hnw.1
  have hnode:=hnodes (4*(w n).index+3) (by omega)
  have hu : (w n).star.val∈Icc (a*W n) (min (b*W n) 1):=by
    constructor
    · have Hnode:=hnodes (4*(w n).index+1) (by omega)
      have H:=hstar.1
      linarith [Hnode.1]
    · apply le_min
      · change (w n).star.val ≤ (a+4*L)*W n
        have H:=hstar.2
        have Hn:=hnode.2
        change NativeStarBuffer.massNode (a*W n) (w n).quarter (4*(w n).index+3) ≤ (a+4*L)*W n at Hn
        linarith
      · have H:=hstar.2
        have Hn:=hnode.2
        have Hbound : (w n).star.val ≤ b*W n := by linarith
        exact Hbound.trans hnBand
  have hscale : laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs ≤ (W n)^2:=by
    rw [hcanonical]
    have Hg : 0 ≤ laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs:=
      (laplaceComparisonStrength_pos _ (M n).hlam _).le
    have H:=le_max_right (M n).xs (Real.sqrt (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs))
    have HS:=Real.sq_sqrt Hg
    change _ ≤ max _ _ ^ 2
    nlinarith [Real.sqrt_nonneg (laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)]
  simpa only [one_mul,show (1:ℝ)+1=2 by norm_num] using
    (M n).actual_compensated_bond_near_temperature hc hWn hnW (hxs n) hTemp.le
      (show (0:ℝ) ≤ 1 by norm_num) hRlo hscale (hnnear _ hu).1

theorem actual_selected_bad_history_susceptibility_coefficient_along_comparable_context_high_only
    {m delta cl cu Az C0 Ct D Bclock T L Cs c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow_high_only (M n) (W n) T L Cs (w n)) :
    ∃Cb : ℝ,0 < Cb ∧ ∀ᶠn in atTop,∀(as : List PositiveMass)
      (_ho : MassOrdered 0 as), (w n).star∈as →
      ∀U : ℕ,retainedMassPrefixIndex (w n).star.val as < U → U ≤ as.length →
        let star:=retainedMassPrefixIndex (w n).star.val as
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2| ≤
          |T*chi^2-1|+Cb*(W n)^2 := by
  have hTemp : 0 < T := G.hT
  obtain ⟨hCb,Hbond⟩:=actual_selected_bad_history_star_bond_near_temperature_along_comparable_context_high_only
    hm hdelta hcl hcu hAz hC0 hL hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G W hcanonical hWlim w hw
  refine ⟨_,hCb,?_⟩
  have Htotal:=G.total_root
  filter_upwards [Hbond,Htotal] with n hnBond hnTotal
  intro as ho hstar U hs hU
  apply actual_minimum_susceptibility_coefficient_change_bound_high_only (M n) hnTotal.1 as ho _ U hs hU
  simpa only [nativeRetainedCut_partitionPoint as ho (w n).star hstar] using hnBond

end OAI.SKFluctuations.LaplaceWindowFormalization
