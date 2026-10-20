module

public import ComparisonNativeActualHistoryRadiusScalarIntervalAlong
public import ComparisonNativeActualHistoryRadiusClockAlong
public import ComparisonNativeActualLocalScalarLimitData
public import ComparisonNativeActualRadiusScalarClosureFinite
public import ComparisonScalarClosureCombinedBare

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 22000000

theorem actual_selected_bad_history_bounded_radius_scalar_closure_along
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
    (d : ActualInheritedLocalScalarLimitData (hTemp.trans_le (sub_le_self T hepsilon))
      (T-epsilon) M htotal)
    (L A : ℝ) (s : NonnegativeMassProfile)
    (Hstrength : ∀t∈Icc a b,Tendsto (fun n=>
      laplaceComparisonStrength (M n).context.d (M n).lam ((M n).xs*t)/(M n).xs^2)
        atTop (𝓝 (L*laplaceComparisonShape (A*t))))
    (Hspin : ∀t∈Icc a b,Tendsto (fun n=>
      orderedPathS (dim n+1) (M n).bf (M n).hf
        ((M n).alpha.val.val ((M n).xs*t))/(M n).xs) atTop (𝓝 (s.mass t))) :
    let g := comparisonLocalScalarLimitResponse (hTemp.trans_le (sub_le_self T hepsilon))
      (T-epsilon) d.beta d.U d.sigma
    ∀ᵐ t∂volume.restrict (Icc a b),
      g (s.mass t)=(L*laplaceComparisonShape (A*t))/(T-epsilon)*(s.mass t-t) := by
  intro g
  let hT : 0 < T := hTemp.trans_le (sub_le_self T hepsilon)
  let Gamma := fun n=>scalarCovarianceResponse hT ((M n).inheritedScalarMassProfile hT (htotal n))
  let u := fun n t=>(M n).alpha.val.val ((M n).xs*t)
  let S := fun n t=>orderedPathS (dim n+1) (M n).bf (M n).hf (u n t)
  let K := fun n t=>actualMixedClock (dim n+1) (M n).bf (M n).hf (u n t)
  let e := fun n t=>laplaceComparisonStrength (M n).context.d (M n).lam ((M n).xs*t)
  let b0 := fun n t=>(M n).b (u n t)
  let h0 := fun n t=>(M n).h (u n t)
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have HrhoL1 : Tendsto (fun n=>∫t in Icc a b,
      |(S n t-Gamma n (K n t))/(M n).xs^3|) atTop (𝓝 0) :=
    actual_selected_bad_history_compact_radius_cavity_L1_along c C a b hc hC ha hab
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim
      hcompare htotal hmass
  have Hrhoi : ∀n,Integrable (fun t=>(S n t-Gamma n (K n t))/(M n).xs^3)
      (volume.restrict (Icc a b)) := fun n=>(M n).rescaled_radius_scalar_gap_integrableOn
        hT ((M n).inheritedScalarMassProfile hT (htotal n)) a b
  obtain ⟨phi,hphi,Hrho⟩ := comparison_L1_zero_exists_ae_subsequence
    (volume.restrict (Icc a b)) (fun n t=>(S n t-Gamma n (K n t))/(M n).xs^3) Hrhoi HrhoL1
  obtain ⟨Cs,Q,hCs,hQ,Hclock,Hz⟩ := actual_selected_bad_history_radius_clock_control_along
    C a b hC hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
    dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory hx htotal
    (hmass.mono (fun _ hn t ht=>(hn t ht).2))
  let Qbig := max Q Cs
  have hQbig : 0 < Qbig := hQ.trans_le (le_max_left _ _)
  have Hrange : ∀ᶠn in atTop,∀t∈Icc a b,K n t/((T-epsilon)*(M n).xs)∈Icc (0:ℝ) Qbig := by
    filter_upwards [Hclock] with n hn t ht
    exact ⟨(hn t ht).2.2.1,(hn t ht).2.2.2.trans (le_max_left _ _)⟩
  have Hsrange : ∀t∈Icc a b,s.mass t∈Icc (0:ℝ) Qbig := by
    intro t ht
    refine ⟨s.nonneg t,?_⟩
    apply le_trans _ (le_max_right _ _)
    apply le_of_tendsto (Hspin t ht)
    filter_upwards [Hclock] with n hn
    exact (div_le_iff₀ (M n).hxs).mpr (by simpa only [mul_comm] using (hn t ht).2.1)
  have Hgc : ContinuousOn g (Icc (0:ℝ) Qbig) := by
    have Hi : IntegrableOn (comparisonLocalScalarLimitSlope hT (T-epsilon) d.beta d.U d.sigma)
        (Icc (0:ℝ) Qbig) := (d.limits Qbig hQbig).1.integrableOn_Icc
    change ContinuousOn (fun q=>∫r in 0..q,
      comparisonLocalScalarLimitSlope hT (T-epsilon) d.beta d.U d.sigma r) (Icc (0:ℝ) Qbig)
    have Hi' : IntegrableOn (comparisonLocalScalarLimitSlope hT (T-epsilon) d.beta d.U d.sigma)
        (uIcc (0:ℝ) Qbig) := by simpa only [uIcc_of_le hQbig.le] using Hi
    simpa only [uIcc_of_le hQbig.le] using intervalIntegral.continuousOn_primitive_interval Hi'
  have Hsmall : ∀ᶠn in atTop,(M n).xs*b ≤ 1 := by
    have H : Tendsto (fun n=>(M n).xs*b) atTop (𝓝 0) := by simpa only [zero_mul] using hx.mul_const b
    exact H.eventually (eventually_le_nhds zero_lt_one)
  have Hnative : ∀ᶠn in atTop,∀t∈Icc a b,K n t=
      comparisonNativeScalarClock (h0 n t) (b0 n t) (e n t) ((M n).xs*t) (S n t) := by
    filter_upwards [Hsmall] with n hn t ht
    exact (M n).radius_mixed_clock_eq_nativeScalarClock
      ⟨mul_nonneg (M n).hxs.le (ha.trans ht.1),
        (mul_le_mul_of_nonneg_left ht.2 (M n).hxs.le).trans hn⟩
  filter_upwards [Hrho,ae_restrict_mem measurableSet_Icc] with t hrhot ht
  apply comparison_scalar_closure_identification_combined_bare
    (fun n=>Gamma (phi n)) (fun n=>h0 (phi n) t) (fun n=>b0 (phi n) t)
    (fun n=>e (phi n) t) (fun n=>S (phi n) t) (fun n=>(M (phi n)).xs) g
    hTemp.ne' (fun n=>(M (phi n)).hxs.ne') (hx.comp hphi.tendsto_atTop)
    ((Hstrength t ht).comp hphi.tendsto_atTop) ((Hspin t ht).comp hphi.tendsto_atTop)
    ((Hz.tendsto_at ht).comp hphi.tendsto_atTop)
    ((d.limits Qbig hQbig).2.2.seq_tendstoUniformlyOn phi hphi.tendsto_atTop)
    (Hgc _ (Hsrange t ht))
  · filter_upwards [hphi.tendsto_atTop.eventually Hnative,hphi.tendsto_atTop.eventually Hrange]
      with n hn hr
    rw [←hn t ht]
    exact hr t ht
  · apply hrhot.congr'
    filter_upwards [hphi.tendsto_atTop.eventually Hnative] with n hn
    rw [←hn t ht]

end OAI.SKFluctuations.LaplaceWindowFormalization
