module

public import ComparisonSignedCavityActualOriginalTargetGapFromFullResidual
public import ComparisonNativeActualHistoryScalarGapIntegralAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false

def ActualOriginalScalarGapIntegralOnBandAlong
    {m delta cl cu Az C0 Ct D Bclock Temp : ℝ} {dim : ℕ→ℕ}
    (hTemp : 0 < Temp) (A : ℝ) (eta : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock) : Prop :=
  ∀ᶠn in atTop,∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp,
    (∫u in 0..A*(M n).xs,
      |orderedPathS (dim n+1) (M n).bf (M n).hf u-
        scalarCovarianceResponse hTemp ((M n).inheritedScalarMassProfile hTemp htotal)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf u)|) ≤ eta n*(M n).xs^4

theorem actual_selected_bad_history_covered_scalar_gap_integral_along
    {m delta cl cu Az C0 Ct D Bclock Temp c0 Ccompare A C cFirst cK Acut Rmacro Cx : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCompare : 0 ≤ Ccompare) (hTemp : 0 < Temp) (hA : 0 < A) (hC : 0 ≤ C)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccompare*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (W radius : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualStrongSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK Acut Rmacro Cx)
    (Hcoverage : ∀ᶠn in atTop,A*(M n).xs ≤ (w n).star.val)
    (rate : ℕ→ℝ) (hrate : ∀n,0 ≤ rate n) (hratelim : Tendsto rate atTop (𝓝 0))
    (Hgap : ActualOriginalTargetScalarGapModulusAlong hTemp A C rate M w) :
    ∃eta : ℕ→ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ActualOriginalScalarGapIntegralOnBandAlong hTemp A eta M := by
  obtain ⟨eta,heta,hetalim,Hintegral⟩:=
    actual_selected_bad_history_original_scalar_gap_integral_envelope_along
      hm hdelta hroom hcl hcu hAz hC0 hCt hCompare dim hdim root M epsilon shell hb hh
      Hhistory hsmall hWlim A C hA hC rate hrate hratelim
  refine ⟨eta,heta,hetalim,?_⟩
  filter_upwards [Hcuts,Hcoverage,Hgap] with n hnCuts hnCoverage hnGap
  obtain ⟨htotal,hnGap⟩:=hnGap
  refine ⟨htotal,?_⟩
  have hstar1 : (w n).star.val ≤ 1:=
    (hnCuts.star_lt.trans hnCuts.high_lt).le.trans hnCuts.outer_le_one
  have H:=Hintegral n Temp hTemp htotal (w n).star.val
    ⟨(w n).star.property.le,hstar1⟩ (by
      intro u hu huA hustar
      exact hnGap ⟨u,hu⟩ huA hustar)
  simpa only [min_eq_left hnCoverage] using H

end OAI.SKFluctuations.Cavity
