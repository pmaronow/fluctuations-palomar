module

public import ComparisonNativeActualHistoryRadiusClockAlong
public import ComparisonNativeActualHistoryRadiusScalarGapUniformAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 20000000

theorem actual_selected_bad_history_high_radius_uniform_identification_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c C a b : ℝ) (hc : 0 < c) (hC : 0 < C) (ha : 0 ≤ a) (hab : a < b)
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
    (hmass : ∀ᶠn in atTop,∀t∈Icc a b,
      c*(M n).xs ≤ (M n).alpha.val.val ((M n).xs*t) ∧
        (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (g : ℝ→ℝ)
    (hG : ∀Q > 0,TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (hTemp.trans_le (sub_le_self T hepsilon))
        ((M n).inheritedScalarMassProfile (hTemp.trans_le (sub_le_self T hepsilon)) (htotal n)))
      (T-epsilon) (M n).xs) g atTop (Icc (0:ℝ) Q))
    (hg : ∀Q > 0,ContinuousOn g (Icc (0:ℝ) Q)) :
    let Gamma := fun n=>scalarCovarianceResponse (hTemp.trans_le (sub_le_self T hepsilon))
      ((M n).inheritedScalarMassProfile (hTemp.trans_le (sub_le_self T hepsilon)) (htotal n))
    let S := fun n t=>orderedPathS (dim n+1) (M n).bf (M n).hf
      ((M n).alpha.val.val ((M n).xs*t))
    let K := fun n t=>actualMixedClock (dim n+1) (M n).bf (M n).hf
      ((M n).alpha.val.val ((M n).xs*t))
    TendstoUniformlyOn (fun n t=>S n t/(M n).xs) (fun t=>t) atTop (Icc a b) ∧
    TendstoUniformlyOn (fun n t=>K n t/((T-epsilon)*(M n).xs)) (fun t=>t) atTop (Icc a b) ∧
    TendstoUniformlyOn (fun n t=>comparisonRescaledScalarResponse (Gamma n) (T-epsilon) (M n).xs
      (K n t/((T-epsilon)*(M n).xs))) g atTop (Icc a b) ∧
    TendstoUniformlyOn (fun n t=>
      (((M n).b ((M n).alpha.val.val ((M n).xs*t))-(T-epsilon))*S n t+
        (M n).h ((M n).alpha.val.val ((M n).xs*t)))/(M n).xs^3)
      (fun _=>0) atTop (Icc a b) := by
  intro Gamma S K
  let h0 := fun n t=>(M n).h ((M n).alpha.val.val ((M n).xs*t))
  let b0 := fun n t=>(M n).b ((M n).alpha.val.val ((M n).xs*t))
  let G := fun n=>comparisonRescaledScalarResponse (Gamma n) (T-epsilon) (M n).xs
  have hbpos : 0 < b := ha.trans_lt hab
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Cs,Q,hCs,hQ,Hclock,Hz⟩ := actual_selected_bad_history_radius_clock_control_along
    C a b hC hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory hx htotal
    (hmass.mono (fun _ hn _ ht=>(hn _ ht).2))
  let Qbig := max Q b
  have hQbig : 0 < Qbig := hQ.trans_le (le_max_left _ _)
  have Hrange : ∀ᶠn in atTop,∀t∈Icc a b,K n t/((T-epsilon)*(M n).xs)∈Icc (0:ℝ) Qbig := by
    filter_upwards [Hclock] with n hn t ht
    exact ⟨(hn t ht).2.2.1,(hn t ht).2.2.2.trans (le_max_left _ _)⟩
  obtain ⟨CG,hCG,Hscalar⟩ := comparison_scalar_compact_response_eventually_bounded
    G g (hG Qbig hQbig) (hg Qbig hQbig)
  let Cbig := max 1 (max C b)
  have hbig : 0 < Cbig := zero_lt_one.trans_le (le_max_left _ _)
  have hCb : C ≤ Cbig := (le_max_left _ _).trans (le_max_right _ _)
  have hbb : b ≤ Cbig := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨CR,hCR,Hrho⟩ := exists_actual_selected_bad_history_radius_scalar_gap_uniform_along
    c Cbig hc hbig hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim root M epsilon shell hepsilon hshell hTemp hb hh
    Hhistory W hcanonical hWlim hcompare
  have Hsmall : ∀ᶠn in atTop,(M n).xs*b ≤ 1 := by
    have H : Tendsto (fun n=>(M n).xs*b) atTop (𝓝 0) := by simpa only [zero_mul] using hx.mul_const b
    exact H.eventually (eventually_le_nhds zero_lt_one)
  have Hr : ∀ᶠn in atTop,∀t∈Icc a b,|(S n t-Gamma n (K n t))/(M n).xs^3| ≤ CR := by
    filter_upwards [Hrho,Hsmall,hmass] with n hn hs hmN t ht
    obtain ⟨htotalN,hn⟩ := hn
    apply hn ((M n).xs*t)
    refine ⟨⟨mul_nonneg (M n).hxs.le (ha.trans ht.1),le_min ?_ ?_⟩,(hmN t ht).1,?_⟩
    · nlinarith only [ht.2,hbb,(M n).hxs]
    · exact (mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hs
    · exact (hmN t ht).2.trans (mul_le_mul_of_nonneg_right hCb (M n).hxs.le)
  have Hflat := comparison_strength_eventually_flat_of_divergence
    (fun n=>(M n).context.d) (fun n=>(M n).lam) (fun n=>(M n).xs)
    (Eventually.of_forall (fun n=>⟨(M n).context.hd,(M n).hlam,(M n).hxs,(M n).hld⟩)) hlarge hbpos
  have Hnative : ∀ᶠn in atTop,∀t∈Icc a b,K n t=
      comparisonNativeScalarClock (h0 n t) (b0 n t) (M n).lam ((M n).xs*t) (S n t) := by
    filter_upwards [Hsmall,Hflat] with n hs hf t ht
    have hrad : (M n).xs*t∈Icc (0:ℝ) 1 :=
      ⟨mul_nonneg (M n).hxs.le (ha.trans ht.1),(mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hs⟩
    have hinv := comparisonSweepQuantile_inverse (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha hrad
    change (M n).R ((M n).alpha.val.val ((M n).xs*t))=(M n).xs*t at hinv
    have H := (M n).inherited_mixed_clock_eq_nativeScalarClock ((M n).alpha.val.property.1 ((M n).xs*t))
    rw [hinv,(hf t ⟨ha.trans ht.1,ht.2⟩).1] at H
    exact H
  let Cprod := |T-epsilon| *(CG+CR)+1
  have hprod : 0 ≤ Cprod := by dsimp only [Cprod];positivity
  have Hbudget : ∀ᶠn in atTop,∀t∈Icc a b,
      |((M n).lam/(M n).xs^2)*(S n t/(M n).xs-t)| ≤ Cprod := by
    filter_upwards [Hnative,Hrange,Hscalar,Hr,(Metric.tendstoUniformlyOn_iff.mp Hz) 1 zero_lt_one]
      with n hn hmN hGbound hr hz t ht
    apply comparison_scalar_product_bound (Gamma n) hTemp.ne' (M n).hxs.ne'
    · rw [←hn t ht]
      exact hGbound _ (hmN t ht)
    · rw [←hn t ht]
      exact hr t ht
    · simpa only [Real.dist_eq,zero_sub,abs_neg] using (hz t ht).le
  have Hlarge : Tendsto (fun n=>(M n).lam/(M n).xs^2) atTop atTop :=
    tendsto_atTop_mono (fun n=>div_le_div_of_nonneg_right
      (laplaceComparisonStrength_le (M n).context.d (M n).hlam.le (M n).xs)
      (sq_nonneg (M n).xs)) hlarge
  obtain ⟨Hspin,HqNative⟩ := comparison_large_strength_uniform_spin_clock h0 b0 S
    (fun n=>(M n).lam) (fun n=>(M n).xs) hTemp (fun n=>(M n).hxs) hx hprod Hlarge Hbudget Hz
  have Hq : TendstoUniformlyOn (fun n t=>K n t/((T-epsilon)*(M n).xs)) (fun t=>t) atTop (Icc a b) :=
    HqNative.congr (Hnative.mono (fun n hn t ht=>
      congrArg (fun z=>z/((T-epsilon)*(M n).xs)) (hn t ht).symm))
  have HP := comparison_uniform_response_at_moving_clock G g
    (fun n t=>K n t/((T-epsilon)*(M n).xs))
    (fun t ht=>⟨ha.trans ht.1,ht.2.trans (le_max_right _ _)⟩)
    (hG Qbig hQbig) (hg Qbig hQbig) Hq Hrange
  exact ⟨Hspin,Hq,HP,Hz⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
