module

public import ComparisonNativeActualHistoryBoundedScalarClosureAlong
public import ComparisonNativeActualVirtualGapExistenceAlong
public import ComparisonNativeActualLocalScalarLimitRadiusReadout
public import ComparisonAECompactIntervalExhaustion

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 22000000

theorem actual_selected_bad_history_bounded_gap_scalar_closure_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
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
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (d : ActualInheritedLocalScalarLimitData (hTemp.trans_le (sub_le_self T hepsilon))
      (T-epsilon) M htotal)
    (L A : ℝ) (s : NonnegativeMassProfile)
    (Hstrength : ∀t : ℝ,Tendsto (fun n=>
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).xs*t)/(M n).xs^2)
        atTop (𝓝 (L*laplaceComparisonShape (A*t))))
    (Hspin : ∀t : ℝ,Tendsto (fun n=>
      orderedPathS (dim n+1) (M n).bf (M n).hf
        ((M n).alpha.val.val ((M n).xs*t))/(M n).xs) atTop (𝓝 (s.mass t)))
    (hasupport : a∈comparisonIncrementSupport d.V.mass)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass) :
    let g := comparisonLocalScalarLimitResponse (hTemp.trans_le (sub_le_self T hepsilon))
      (T-epsilon) d.beta d.U d.sigma
    ∀ᵐt∂volume.restrict (Ioo a b),
      g (s.mass t)=(L*laplaceComparisonShape (A*t))/(T-epsilon)*(s.mass t-t) := by
  intro g
  have hmass : 0 < d.V.mass ((a+b)/2) :=
    comparison_increment_support_positive_cdf_after d.V.monotone d.radius_negative_axis_zero
      hasupport (by linarith)
  let c := d.V.mass ((a+b)/2)/2
  let C := d.V.mass ((a+b)/2)+1
  have hc : 0 < c := half_pos hmass
  have hC : 0 < C := by dsimp only [C]; linarith
  apply comparison_ae_on_open_interval_of_compact_interiors
  intro left hleft right hright hlr
  have Hmass := actual_compact_gap_mass_band_along dim M d.V.mass d.V.monotone
    d.radius_inverse_cdf_limit hab hgap hmass hleft hright
  exact actual_selected_bad_history_bounded_radius_scalar_closure_along
    c C left right hc hC (ha.trans hleft.1.le) hlr
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim
    hcompare htotal Hmass d L A s (fun t _=>Hstrength t) (fun t _=>Hspin t)

end OAI.SKFluctuations.LaplaceWindowFormalization
