module

public import ComparisonNativeActualBoundedGradientUniformAlong
public import ComparisonNativeActualHistoryBoundedRadiusGradientFactoryAlong
public import ComparisonBoundedPrincipalIntegrability
public import ComparisonNativeActualVirtualGapExistenceAlong
public import ComparisonNativeActualLocalScalarLimitRadiusReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 20000000

theorem actual_selected_bad_history_bounded_virtual_gap_primitive_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (K : ℝ) (hK : 0 ≤ K)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (_hc0 : 0 < c0) (_hc01 : c0 ≤ 1)
    (_hmargin : delta/4 < 3*m-99*delta) (_hcapmargin : 100*delta < (1:ℝ)/3+m)
    (_hgapmargin : 0 < 9*m-298*delta)
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
    ∃Kj : ℝ,1 ≤ Kj ∧ ∃j : ℝ→ℝ,Monotone j ∧
      (∀t∈Icc a b,j t∈Icc (1/Kj^2) (Kj^2)) ∧
      Nonempty (ComparisonPinnedGapPrimitive a b (fun t=>j t*
        comparisonScaledStationarity (L*laplaceComparisonShape (A*t))
          (laplaceComparisonSlope (A*t)) t (s.mass t))) := by
  have hmass : 0 < d.V.mass ((a+b)/2) := comparison_increment_support_positive_cdf_after
    d.V.monotone d.radius_negative_axis_zero hasupport (by linarith)
  let c:=d.V.mass ((a+b)/2)/2
  have hc : 0 < c := half_pos hmass
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨KG,hKG,Hgradient⟩ := eventually_actual_bounded_strength_gradient_uniform_on_band_along
    K B hK ((ha.trans hab.le).trans hbB.le) hm hdelta hroom hcl hcu hAz hC0 hCt
    hCcal dim hdim M hx hcompare hwork
  let f:=fun t=>comparisonScaledStationarity (L*laplaceComparisonShape (A*t))
    (laplaceComparisonSlope (A*t)) t (s.mass t)
  have hf : IntegrableOn f (Icc a b) := comparison_bounded_principal_density_integrable s hL.le hA ha
  apply actual_virtual_gap_primitive_of_gradient_limit_along hdelta hcu.le hAz hC0 (by linarith)
    dim hdim M hx d.V.mass d.V.monotone d.radius_inverse_cdf_limit ha hab hbB
    hasupport hbsupport hgap hmass f hf
    ⟨KG,hKG.le,Hgradient.mono (fun _ hn t ht _=>hn t ht)⟩
  intro u hu v hv huv
  have Hmass := actual_compact_gap_mass_band_along dim M d.V.mass d.V.monotone
    d.radius_inverse_cdf_limit hab hgap hmass hu hv
  exact actual_selected_bad_history_bounded_radius_gradient_L1_along Bclock
    hm hdelta (by linarith) hcl hcu hAz hC0 hCt hc (ha.trans_lt hu.1) huv hK
    dim hdim root M hx epsilon shell hshell hb hh Hhistory hwork Hmass s
    (fun t _=>Hstrength t) (fun t _=>Hslope t) (fun t _=>Hspin t)

end OAI.SKFluctuations.LaplaceWindowFormalization
