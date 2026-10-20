module

public import ComparisonNativeActualHistoryNearBareClocks
public import ComparisonNativeActualHistoryScalarEndpointLimits
public import ComparisonSignedCavityActualFourResidualDecomposition

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 20000000

namespace NativeOverlapMinimum

theorem actual_compensated_bond_near_temperature
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u c W T Cb : ℝ} (hc : 0 < c) (hW : 0 < W) (hW1 : W ≤ 1)
    (hxs : M.xs ≤ W) (hT : 0 ≤ T) (hCb : 0 ≤ Cb)
    (hr : c*W ≤ M.R u)
    (hscale : laplaceComparisonStrength M.context.d M.lam M.xs ≤ W^2)
    (hb : |M.b u-T| ≤ Cb*W^2) :
    |(M.bf u:ℝ)-T| ≤ (Cb+1+1/c)*W^2 := by
  have hR:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u
  have hg:=M.strength_le_scale_of_radius_lower hc hW hW1 hxs ⟨hr,hR.2⟩ hscale
  have hg0:=(laplaceComparisonStrength_pos M.context.d M.hlam (M.R u)).le
  have hcinv : 0 ≤ 1/c:=by positivity
  have hC : 0 ≤ (Cb+1+1/c)*W^2:=by positivity
  change |max (M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)) 0-T| ≤ _
  apply abs_le.mpr
  constructor
  · have H:=le_max_left (M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)) 0
    nlinarith [(abs_le.mp hb).1]
  · have H : max (M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)) 0 ≤
        T+(Cb+1+1/c)*W^2 := by
      apply max_le
      · nlinarith [(abs_le.mp hb).2,mul_nonneg hcinv (sq_nonneg W)]
      · positivity
    linarith

end NativeOverlapMinimum

theorem susceptibility_coefficient_change_bound
    {b T chi W Cb : ℝ} (hchi0 : 0 ≤ chi) (hchi1 : chi ≤ 1)
    (hb : |b-T| ≤ Cb*W^2) :
    |1-b*chi^2| ≤ |T*chi^2-1|+Cb*W^2 := by
  have hC : 0 ≤ Cb*W^2:=(abs_nonneg _).trans hb
  have hchi2 : chi^2 ≤ 1:=by nlinarith
  have HE : 1-b*chi^2=-(T*chi^2-1)+(T-b)*chi^2:=by ring
  rw [HE]
  apply (abs_add_le _ _).trans
  rw [abs_neg,abs_mul,abs_of_nonneg (sq_nonneg chi),abs_sub_comm T b]
  apply add_le_add le_rfl
  exact (mul_le_mul hb hchi2 (sq_nonneg chi) hC).trans_eq (mul_one _)

theorem actual_minimum_susceptibility_coefficient_change_bound
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
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

theorem actual_selected_bad_history_star_bond_near_temperature_along
    {m delta cl cu Az C0 Ct D Bclock T L Cs c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hshell : 0 < shell) (hTemp : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cs (w n)) :
    let Cb:=2+1/(calibratedBandStart cu Az/cu)
    0 < Cb ∧ ∀ᶠn in atTop,|((M n).bf (w n).star.val:ℝ)-(T-epsilon)| ≤ Cb*(W n)^2 := by
  dsimp only
  let a:=calibratedBandStart cu Az
  let b:=a+4*L
  let c:=a/cu
  have ha : 0 < a:=calibrated_band_start_pos hcu hAz
  have hc : 0 < c:=div_pos ha hcu
  have hb0 : 0 ≤ b:=by dsimp only [b];positivity
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have Hnear:=actual_selected_bad_shell_history_near_bare_clocks hm hdelta hcl hAz hC0 hc0 hc01
    hmargin hcapmargin hgapmargin hdim epsilon shell hshell hb hh Hhistory W
    (Eventually.of_forall hxs) hWlim b 1 hb0 zero_lt_one
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨by positivity,?_⟩
  filter_upwards [Hnear,HW,hw] with n hnnear hnW hnw
  have hWn : 0 < W n:=(M n).hxs.trans_le (hxs n)
  obtain ⟨p,hindex,_,hquarter,_,_,hnodes,hstar,_,_,_,_,hRlo,_⟩:=hnw.1
  have hnode:=hnodes (4*(w n).index+3) (by omega)
  have hu : (w n).star.val∈Icc (0:ℝ) (b*W n):=by
    refine ⟨(w n).star.property.le,?_⟩
    change (w n).star.val ≤ (a+4*L)*W n
    have H:=hstar.2
    have Hn:=hnode.2
    change NativeStarBuffer.massNode (a*W n) (w n).quarter (4*(w n).index+3) ≤ (a+4*L)*W n at Hn
    linarith
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

theorem actual_selected_bad_history_susceptibility_coefficient_along
    {m delta cl cu Az C0 Ct D Bclock T L Cs c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hL : 0 < L) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hshell : 0 < shell) (hTemp : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0)) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cs (w n)) :
    ∃Cb : ℝ,0 < Cb ∧ ∀ᶠn in atTop,∀(as : List PositiveMass)
      (_ho : MassOrdered 0 as), (w n).star∈as →
      ∀U : ℕ,retainedMassPrefixIndex (w n).star.val as < U → U ≤ as.length →
        let star:=retainedMassPrefixIndex (w n).star.val as
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |1-((M n).bf (partitionPoint 0 as star):ℝ)*chi^2| ≤
          |(T-epsilon)*chi^2-1|+Cb*(W n)^2 := by
  obtain ⟨hCb,Hbond⟩:=actual_selected_bad_history_star_bond_near_temperature_along
    hm hdelta hcl hcu hAz hC0 hL hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim root M epsilon shell hshell hTemp hb hh Hhistory W hcanonical hWlim w hw
  refine ⟨_,hCb,?_⟩
  have Htotal:=actual_selected_bad_history_total_clock_and_root dim root M
    epsilon shell hepsilon hb hh Hhistory
  filter_upwards [Hbond,Htotal] with n hnBond hnTotal
  intro as ho hstar U hs hU
  apply actual_minimum_susceptibility_coefficient_change_bound (M n) hnTotal.1 as ho _ U hs hU
  simpa only [nativeRetainedCut_partitionPoint as ho (w n).star hstar] using hnBond

end OAI.SKFluctuations.LaplaceWindowFormalization
