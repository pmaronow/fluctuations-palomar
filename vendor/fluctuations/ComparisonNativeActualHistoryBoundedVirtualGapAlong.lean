module

public import ComparisonNativeActualHistoryBoundedVirtualPrimitiveAlong
public import ComparisonNativeActualHistoryGapSpinRangeAlong
public import ComparisonNativeActualHistoryBoundedGapScalarClosureAlong
public import ComparisonBoundedVirtualGradientBehavior

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 22000000

theorem actual_selected_bad_history_bounded_virtual_gap_data_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
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
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2 ≤ K)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (d : ActualInheritedLocalScalarLimitData (hTemp.trans_le (sub_le_self T hepsilon))
      (T-epsilon) M htotal)
    (L A : ℝ) (s : NonnegativeMassProfile) (hL : 0 < L) (hA : 0 ≤ A)
    (Hstrength : ∀t,Tendsto (fun n=>
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).xs*t)/(M n).xs^2)
      atTop (𝓝 (L*laplaceComparisonShape (A*t))))
    (Hslope : ∀t,Tendsto (fun n=>comparisonLogSlope
      (laplaceComparisonStrength (M n).context.d (M n).lam) ((M n).xs*t))
      atTop (𝓝 (laplaceComparisonSlope (A*t))))
    (Hspin : ∀t,Tendsto (fun n=>(M n).actualScaledRadiusSpin t) atTop (𝓝 (s.mass t)))
    {a b B : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbB : b < B)
    (hasupport : a∈comparisonIncrementSupport d.V.mass)
    (hbsupport : b∈comparisonIncrementSupport d.V.mass)
    (hgap : ∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass) :
    Nonempty (ComparisonVirtualGapData
      (comparisonLocalScalarLimitResponse (hTemp.trans_le (sub_le_self T hepsilon))
        (T-epsilon) d.beta d.U d.sigma) a b) := by
  obtain ⟨Kj,hKj,j,hj,Hj,⟨P⟩⟩ :=
    actual_selected_bad_history_bounded_virtual_gap_primitive_along K hK
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim
      hcompare hwork htotal d L A s hL hA Hstrength Hslope Hspin ha hab hbB
      hasupport hbsupport hgap
  apply Nonempty.intro
  apply comparison_bounded_pinned_primitive_to_gap ha hL hTemp P
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact lt_of_lt_of_le (by positivity : 0 < 1/Kj^2) (Hj t ⟨ht.1.le,ht.2.le⟩).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact actual_selected_bad_history_radius_spin_between_support_along
      (hTemp.trans_le (sub_le_self T hepsilon)) hm hdelta hroom hcl hcu hAz hC0 hCt
      dim hdim root M W hcanonical hWlim epsilon shell hb hh Hhistory htotal d s
      Hspin ht.1 ht.2 hasupport hbsupport
  · exact actual_selected_bad_history_bounded_gap_scalar_closure_along ha hab
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim
      hcompare htotal d L A s Hstrength Hspin hasupport hgap

end OAI.SKFluctuations.LaplaceWindowFormalization
