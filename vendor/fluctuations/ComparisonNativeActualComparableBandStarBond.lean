module

public import ComparisonNativeActualComparableBandSharpWindow
public import ComparisonSignedCavityActualHistorySusceptibilityCoefficient

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
theorem actual_selected_bad_history_star_bond_near_temperature_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Cs c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) :
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

theorem actual_selected_bad_history_susceptibility_coefficient_along_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T L Cs c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : NativeActualComparableBandContext M T)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) :
    ∃Cb : ℝ,0 < Cb ∧ ∀ᶠn in atTop,∀(as : List PositiveMass)
      (_ho : MassOrdered 0 as), (w n).star∈as →
      ∀U : ℕ,retainedMassPrefixIndex (w n).star.val as < U → U ≤ as.length →
        let star:=retainedMassPrefixIndex (w n).star.val as
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2| ≤
          |T*chi^2-1|+Cb*(W n)^2 := by
  have hTemp : 0 < T := G.hT
  obtain ⟨hCb,Hbond⟩:=actual_selected_bad_history_star_bond_near_temperature_along_comparable_context
    hm hdelta hcl hcu hAz hC0 hL hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim M G W hcanonical hWlim w hw
  refine ⟨_,hCb,?_⟩
  have Htotal:=G.total_root
  filter_upwards [Hbond,Htotal] with n hnBond hnTotal
  intro as ho hstar U hs hU
  apply actual_minimum_susceptibility_coefficient_change_bound (M n) hnTotal.1 as ho _ U hs hU
  simpa only [nativeRetainedCut_partitionPoint as ho (w n).star hstar] using hnBond

end OAI.SKFluctuations.LaplaceWindowFormalization
