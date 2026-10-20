module

public import ComparisonNativeActualHistoryHighRadiusGradientAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 20000000

theorem eventually_actual_history_high_gradient_uniform_above_mass_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c B : ℝ) (hc : 0 < c) (hB : 0 < B)
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
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (g : ℝ→ℝ)
    (hG : ∀Q > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (hTemp.trans_le (sub_le_self T hepsilon))
        ((M n).inheritedScalarMassProfile (hTemp.trans_le (sub_le_self T hepsilon)) (htotal n)))
      (T-epsilon) (M n).xs) g atTop (Icc (0:ℝ) Q))
    (hg : ∀Q > 0,ContinuousOn g (Icc (0:ℝ) Q)) :
    ∃CG : ℝ,0 < CG ∧ ∀ᶠn in atTop,∀t∈Icc (0:ℝ) B,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) →
        |(M n).actualVirtualScaledGradient t| ≤ CG := by
  let Gamma := fun n=>scalarCovarianceResponse (hTemp.trans_le (sub_le_self T hepsilon))
    ((M n).inheritedScalarMassProfile (hTemp.trans_le (sub_le_self T hepsilon)) (htotal n))
  let S := fun n t=>orderedPathS (dim n+1) (M n).bf (M n).hf
    ((M n).alpha.val.val ((M n).xs*t))
  let K := fun n t=>actualMixedClock (dim n+1) (M n).bf (M n).hf
    ((M n).alpha.val.val ((M n).xs*t))
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  let Cm := 1+cu*(B+Az)
  have hCm : 0 < Cm := by dsimp only [Cm];positivity
  have Hsmall : ∀ᶠn in atTop,(M n).xs*B ≤ 1 := by
    have H : Tendsto (fun n=>(M n).xs*B) atTop (𝓝 0) := by simpa only [zero_mul] using hx.mul_const B
    exact H.eventually (eventually_le_nhds zero_lt_one)
  have Hupper : ∀ᶠn in atTop,∀t∈Icc (0:ℝ) B,
      (M n).alpha.val.val ((M n).xs*t) ≤ Cm*(M n).xs := by
    filter_upwards [Hsmall] with n hn t ht
    let z := max ((M n).xs*B) (M n).z
    have hz : z∈Icc (M n).z 1 := ⟨le_max_right _ _,max_le hn (M n).hz.2⟩
    have hzsize : z ≤ (B+Az)*(M n).xs := by
      apply max_le
      · nlinarith only [mul_nonneg hAz (M n).hxs.le]
      · nlinarith only [(M n).hzxs,mul_nonneg hB.le (M n).hxs.le]
    have H := ((M n).alpha.val.property.2
      ((mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans (le_max_left _ _))).trans
      ((M n).regular z hz).2
    have HM := mul_le_mul_of_nonneg_left hzsize hcu.le
    dsimp only [Cm]
    nlinarith only [H,HM,(M n).hxs]
  obtain ⟨Cs,Q,hCs,hQ,Hclock,Hz⟩ := actual_selected_bad_history_radius_clock_control_along
    Cm 0 B hCm hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory hx htotal Hupper
  obtain ⟨CP,hCP,HP⟩ := comparison_scalar_compact_response_eventually_bounded
    (fun n=>comparisonRescaledScalarResponse (Gamma n) (T-epsilon) (M n).xs) g
    (hG Q hQ) (hg Q hQ)
  let Cbig := max Cm B
  have hbig : 0 < Cbig := hCm.trans_le (le_max_left _ _)
  obtain ⟨CR,hCR,HR⟩ := exists_actual_selected_bad_history_radius_scalar_gap_uniform_along
    c Cbig hc hbig hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim root M epsilon shell hepsilon hshell hTemp hb hh
    Hhistory W hcanonical hWlim hcompare
  have Hclosure := eventually_actual_high_flat_radius_gradient_closure
    dim M hx hlarge 0 B le_rfl hB Gamma (T-epsilon) hTemp
  refine ⟨2*|T-epsilon| *(CP+CR)+2,by positivity,?_⟩
  filter_upwards [Hsmall,Hupper,Hclock,HP,HR,Hclosure,
    (Metric.tendstoUniformlyOn_iff.mp Hz) 1 zero_lt_one]
    with n hs hu hclock hp hr hclosure hz t ht hlo
  obtain ⟨htotalN,hr⟩ := hr
  have hstrip : (M n).xs*t∈(M n).actualRadiusTargetStrip c Cbig := by
    refine ⟨⟨mul_nonneg (M n).hxs.le ht.1,le_min ?_ ?_⟩,hlo,?_⟩
    · exact (mul_le_mul_of_nonneg_left (ht.2.trans (le_max_right _ _)) (M n).hxs.le).trans_eq (mul_comm _ _)
    · exact (mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hs
    · exact (hu t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (M n).hxs.le)
  have hP := hp _ (hclock t ht).2.2
  have hR : |(S n t-Gamma n (K n t))/(M n).xs^3| ≤ CR := hr _ hstrip
  have hZ : |(((M n).b ((M n).alpha.val.val ((M n).xs*t))-(T-epsilon))*S n t+
      (M n).h ((M n).alpha.val.val ((M n).xs*t)))/(M n).xs^3| ≤ 1 := by
    simpa only [Real.dist_eq,zero_sub,abs_neg,S] using (hz t ht).le
  have H := comparison_scalar_density_error_bound (g:=0) (by
    simpa only [mul_div_assoc] using (hclosure t ht).2)
  simp only [mul_zero,sub_zero] at H
  have HPmul := mul_le_mul_of_nonneg_left hP (show 0 ≤ 2*|T-epsilon| by positivity)
  have HRmul := mul_le_mul_of_nonneg_left hR (show 0 ≤ 2*|T-epsilon| by positivity)
  dsimp only [S,K] at hZ HRmul
  nlinarith only [H,HPmul,HRmul,hZ]

end OAI.SKFluctuations.LaplaceWindowFormalization
