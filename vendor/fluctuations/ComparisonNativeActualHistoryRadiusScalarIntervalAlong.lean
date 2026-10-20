module

public import ComparisonNativeActualHistoryRadiusScalarGapAlong
public import ComparisonNativeActualRadiusScalarRescaling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 20000000

theorem actual_selected_bad_history_compact_radius_cavity_L1_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c C a b : ℝ) (hc : 0 < c) (_hC : 0 < C) (ha : 0 ≤ a) (hab : a < b)
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
        (M n).alpha.val.val ((M n).xs*t) ≤ C*(M n).xs) :
    Tendsto (fun n=>∫t in Icc a b,
      |(orderedPathS (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val ((M n).xs*t))-
        scalarCovarianceResponse (hTemp.trans_le (sub_le_self T hepsilon))
          ((M n).inheritedScalarMassProfile (hTemp.trans_le (sub_le_self T hepsilon)) (htotal n))
          (actualMixedClock (dim n+1) (M n).bf (M n).hf
            ((M n).alpha.val.val ((M n).xs*t))))/(M n).xs^3|) atTop (𝓝 0) := by
  let Cbig:=max 1 (max C b)
  have hbig : 0 < Cbig:=zero_lt_one.trans_le (le_max_left _ _)
  have hCb : C ≤ Cbig := (le_max_left _ _).trans (le_max_right _ _)
  have hbb : b ≤ Cbig := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨eta,heta,Heta,Hbound⟩:=
    exists_actual_selected_bad_history_radius_scalar_gap_integral_along c Cbig hc hbig
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hxb : Tendsto (fun n=>(M n).xs*b) atTop (𝓝 0) := by
    simpa only [zero_mul] using hx.mul_const b
  have hsmall : ∀ᶠn in atTop,(M n).xs*b ≤ 1 :=
    hxb.eventually (eventually_le_nhds zero_lt_one)
  apply squeeze_zero' (Eventually.of_forall (fun n=>integral_nonneg (fun t=>abs_nonneg _))) _ Heta
  filter_upwards [Hbound,hmass,hsmall] with n hn hmN hsN
  obtain ⟨ht,hn⟩:=hn
  let f:=fun r=>orderedPathS (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r)-
    scalarCovarianceResponse (hTemp.trans_le (sub_le_self T hepsilon))
      ((M n).inheritedScalarMassProfile (hTemp.trans_le (sub_le_self T hepsilon)) (htotal n))
      (actualMixedClock (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r))
  have hf : IntegrableOn f ((M n).actualRadiusTargetStrip c Cbig) :=
    ((M n).original_scalar_radius_gap_integrableOn
      (hTemp.trans_le (sub_le_self T hepsilon)) _).mono_set
      (fun r hr=>⟨hr.1.1,hr.1.2.trans (min_le_right _ _)⟩)
  have H:=(M n).radius_scalar_residual_compact_integral_le ha hab.le hbb hsN
    (fun t ht=>⟨(hmN t ht).1,(hmN t ht).2.trans
      (mul_le_mul_of_nonneg_right hCb (M n).hxs.le)⟩) f hf
  exact H.trans hn

end OAI.SKFluctuations.LaplaceWindowFormalization
