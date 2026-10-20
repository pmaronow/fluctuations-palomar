module

public import ComparisonSignedCavityActualHistoryCoveredTargetInitialInputsAlong
public import ComparisonSignedCavityActualInitialFullSourceModulusAlong
public import ComparisonSignedCavityActualInitialFullResidualRetainedAdapter
public import ComparisonSignedCavityActualSourceCutOuterScaleMonotonicity
public import ComparisonNativeActualCoveredScalarGapIntegralAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_original_scalar_gap_pointwise_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (Atarget : ℝ) (hAtarget : 0 < Atarget)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hshell : 0 < shell) (hTemp : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ rate : ℕ→ℝ,
      (∀n,0 ≤ rate n) ∧ Tendsto rate atTop (𝓝 0) ∧
      ∀ᶠn in atTop,
        ∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
        ∀u : ℝ, 0 < u → u ≤ Atarget*(M n).xs →
          |orderedPathS (dim n+1) (M n).bf (M n).hf u-
            scalarCovarianceResponse (hTemp.trans_le (sub_le_self T hepsilon))
              ((M n).inheritedScalarMassProfile
                (hTemp.trans_le (sub_le_self T hepsilon)) htotal)
              (actualMixedClock (dim n+1) (M n).bf (M n).hf u)| ≤
          C*(M n).xs^2*(Real.sqrt (orderedPathB (dim n+1) (M n).bf (M n).hf u-
            (orderedPathS (dim n+1) (M n).bf (M n).hf u)^2)+1/(dim n+1:ℕ))+
              rate n*(M n).xs^3 := by
  let cInner:=Atarget+1+2*cu*(Az+1)
  let Cinner:=2*cInner
  let Rmacro:ℝ:=1/4
  have hcbase : 0 ≤ 2*cu*(Az+1):=by positivity
  have hcInner : 0 < cInner:=by dsimp only [cInner];linarith
  have hcouter : 2*cu*(Az+1) ≤ cInner:=by dsimp only [cInner];linarith
  have hinner : 0 < Cinner:=by dsimp only [Cinner];positivity
  have hTargetInner : Atarget < 2*cInner:=by dsimp only [cInner];linarith
  have hmacro : 0 < Rmacro:=by norm_num [Rmacro]
  have hRhalf : Rmacro ≤ 1/2:=by norm_num [Rmacro]
  have hT : 0 < T:=hTemp.trans_le (sub_le_self T hepsilon)
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hW n : 0 < W n:=(M n).hxs.trans_le (hxs n)
  obtain ⟨hsaving,cK,hcK,Cf,hCf,Hsource,Cwindow,hCwindow,w,hw,Hcoverage,
    Hsquare,Hmixed,_Hsharp,_Hconstant,_Hpair,Happrox,Ku,Kv,cFirst,cKcut,hKu,_hKv,
    hFirst,hFirstLower,hcKcut,high,outer,_Hvalues,Hstrong,threshold,hthreshold,Hbootstrap⟩:=
    exists_actual_selected_bad_history_covered_target_initial_inputs_along
      Atarget hAtarget.le Rmacro Cinner hmacro hRhalf hinner
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
  let Aouter:=max (Ku+1) Atarget
  have hAouter : 1 ≤ Aouter:=(by linarith : (1:ℝ) ≤ Ku+1).trans (le_max_left _ _)
  have hAo : 0 < Aouter:=zero_lt_one.trans_le hAouter
  have Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (Kv*W n) cFirst cKcut Aouter Rmacro Cinner := by
    filter_upwards [Hstrong] with n hn
    exact hn.mono_outer_scale (hW n).le (le_max_left _ _)
  obtain ⟨thresholdI,_hthresholdI,savingI,hsavingI,HapproxI⟩:=Happrox Cinner hinner.le
  let depth:=max threshold thresholdI
  obtain ⟨Cj,hCj,HJ0⟩:=Hbootstrap depth (le_max_left _ _)
  have HJ : ActualSusceptibilityCoefficientOnStrongCutsAlong Cj M W w high outer := by
    filter_upwards [HJ0] with n hn
    intro Lnet us hus hret hmesh hstar hhigh houter hnodes
    filter_upwards [hn Lnet us hus hret hmesh hstar hhigh houter hnodes] with jGrid hj
    obtain ⟨_hs,_hU,_hcal,Hbond⟩:=hj
    exact Hbond
  obtain ⟨Cr,hCr,er,her,herlim,Hfull⟩:=actual_selected_bad_history_initial_full_source_modulus_along
    depth hmacro hRhalf hinner hAouter hcKcut hFirst hFirstLower
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hmargin hcapmargin
    hdim root M epsilon shell hepsilon hT.le hb hh Hhistory W (fun n=>Kv*W n)
    hcanonical hWlim hcompare (actualSlowWindowExponent m delta/256) hsaving hCj.le
    w high outer hw Hsquare HJ Hmixed Hcuts
  have HfullTarget:=Hfull.to_retained_targets (show Atarget ≤ Aouter from le_max_right _ _)
  obtain ⟨Ctgt,et,hCtgt,het,hetlim,Htarget⟩:=
    actual_selected_bad_history_continuum_target_residual_modulus_of_initial_approx
      Cinner Aouter hT hinner.le hAo hm hdelta hroom hcl hcu hAz hC0 hCt
      (sq_nonneg Ccal) hcInner hcouter hc0 hmargin hcapmargin hsavingI depth dim hdim root M
      epsilon shell hepsilon hb hh Hhistory W (fun n=>(M n).xs) hcanonical hWlim
      (fun _=>le_rfl) (Eventually.of_forall hxs) (Eventually.of_forall hcompare) w
      (HapproxI depth (le_max_right _ _))
  obtain ⟨rate,hrate,hratelim,Hgap⟩:=actual_original_target_gap_from_full_residual_along
    hT depth Cinner hcInner le_rfl hTargetInner le_rfl M W (fun n=>Kv*W n) w high outer
    Hcuts Hsource et er hetlim herlim Htarget HfullTarget
  have hGapConstant : 0 ≤ Ctgt+2*T*Cr:=add_nonneg hCtgt.le
    (mul_nonneg (mul_nonneg (by norm_num) hT.le) hCr)
  refine ⟨Ctgt+2*T*Cr,hGapConstant,rate,hrate,hratelim,?_⟩
  filter_upwards [Hcoverage,Hgap] with n hncover hngap
  obtain ⟨htotal,hngap⟩:=hngap
  refine ⟨htotal,?_⟩
  intro u hu huA
  exact hngap ⟨u,hu⟩ huA (huA.trans_lt hncover)

end OAI.SKFluctuations.LaplaceWindowFormalization
