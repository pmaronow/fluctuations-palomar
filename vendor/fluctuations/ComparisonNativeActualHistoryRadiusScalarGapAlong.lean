module

public import ComparisonNativeActualHistoryOriginalScalarGapPointwiseAlong
public import ComparisonNativeActualHistoryRadiusStripConcentrationAlong
public import ComparisonNativeActualRadiusScalarModulus

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 20000000

theorem exists_actual_selected_bad_history_radius_scalar_gap_integral_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
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
    ∃eta : ℕ→ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ᶠn in atTop,
        ∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
        (∫r in (M n).actualRadiusTargetStrip c C,
          |orderedPathS (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r)-
            scalarCovarianceResponse (hTemp.trans_le (sub_le_self T hepsilon))
              ((M n).inheritedScalarMassProfile
                (hTemp.trans_le (sub_le_self T hepsilon)) htotal)
              (actualMixedClock (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r))|)/
          (M n).xs^4 ≤ eta n := by
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have HW : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0) := by
    convert hWlim using 1
    exact funext (fun n=>(hcanonical n).symm)
  have Hthermal := actual_selected_bad_history_radius_strip_thermal_tendsto_zero_along
    (c:=c) (C:=C) Bclock hm hdelta (by linarith) hcl hcu hAz hC0 hCt hc
    dim hdim root M hx epsilon shell hshell hb hh Hhistory
  obtain ⟨Cp,hCp,rate,hrate,Hrate,Hpoint⟩ :=
    exists_actual_selected_bad_history_original_scalar_gap_pointwise_along C hC
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
  let eta := fun n=>Cp*Real.sqrt (C*((∫r in (M n).actualRadiusTargetStrip c C,
      (M n).cavityRadiusPointDefect r)/(M n).xs^3))+
      Cp*C/((M n).context.N*(M n).xs)+C*rate n
  have Hsite:=actual_scalar_gap_site_ratio_tendsto_zero_along hm hC0 dim hdim M HW
  have Heta : Tendsto eta atTop (𝓝 0) := by
    have H:=(((Hthermal.const_mul C).sqrt.const_mul Cp).add (Hsite.const_mul (Cp*C))).add
      (Hrate.const_mul C)
    simpa only [eta,mul_zero,Real.sqrt_zero,add_zero,mul_one_div] using H
  refine ⟨eta,?_,Heta,?_⟩
  · intro n
    exact add_nonneg (add_nonneg (mul_nonneg hCp (Real.sqrt_nonneg _))
      (div_nonneg (mul_nonneg hCp hC.le)
        (mul_nonneg (M n).context.hN.le (M n).hxs.le)))
      (mul_nonneg hC.le (hrate n))
  · filter_upwards [Hpoint] with n hn
    obtain ⟨htotal,hn⟩:=hn
    refine ⟨htotal,?_⟩
    let F:=(M n).actualRadiusTargetStrip c C
    have := (M n).actual_radius_target_strip_finite_measure c C
    apply (M n).actual_original_radius_scalar_modulus_integral_le
      (hTemp.trans_le (sub_le_self T hepsilon)) _ F
      ((M n).actual_radius_target_strip_measurable c C)
      (fun r hr=>⟨hr.1.1,hr.1.2.trans (min_le_right _ _)⟩)
      hCp hC.le (hrate n)
    · simpa only [measureReal_restrict_apply_univ] using
        (M n).actual_radius_target_strip_measure_le c C hC.le
    · intro r hr
      exact hn ((M n).alpha.val.val r) ((mul_pos hc (M n).hxs).trans_le hr.2.1) hr.2.2

end OAI.SKFluctuations.LaplaceWindowFormalization
