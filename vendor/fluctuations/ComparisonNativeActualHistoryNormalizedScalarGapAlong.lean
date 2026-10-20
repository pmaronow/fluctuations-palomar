module

public import ComparisonNativeActualNormalizedScalarGap
public import ComparisonNativeActualHistoryOriginalScalarGapIntegralAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology ENNReal
set_option maxHeartbeats 12000000

theorem exists_actual_selected_bad_history_normalized_scalar_gap_along
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
    ∃eta : ℕ→ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      (∀ᶠn in atTop,∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
        ∀v∈Icc (0:ℝ) 1,v ≤ Atarget*(M n).xs →
          Integrable (fun z : ParisiFinite.OrderPoint =>
            (M n).inheritedScalarCavityResidual (hTemp.trans_le (sub_le_self T hepsilon))
              htotal z/(M n).xs^3) (comparisonNormalizedClockMass (M n).xs v) ∧
          (∫z : ParisiFinite.OrderPoint,
            |(M n).inheritedScalarCavityResidual (hTemp.trans_le (sub_le_self T hepsilon))
              htotal z/(M n).xs^3| ∂comparisonNormalizedClockMass (M n).xs v) ≤ eta n) ∧
      (∀htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
        ∀v : ℕ→ℝ,(∀n,v n∈Icc (0:ℝ) 1) →
        (∀ᶠn in atTop,v n ≤ Atarget*(M n).xs) →
          (∀n,Integrable (fun z : ParisiFinite.OrderPoint =>
            (M n).inheritedScalarCavityResidual (hTemp.trans_le (sub_le_self T hepsilon))
              (htotal n) z/(M n).xs^3) (comparisonNormalizedClockMass (M n).xs (v n))) ∧
          Tendsto (fun n=>∫z : ParisiFinite.OrderPoint,
            |(M n).inheritedScalarCavityResidual (hTemp.trans_le (sub_le_self T hepsilon))
              (htotal n) z/(M n).xs^3| ∂comparisonNormalizedClockMass (M n).xs (v n))
            atTop (𝓝 0)) := by
  obtain ⟨eta,heta,hetalim,Hgap⟩ :=
    exists_actual_selected_bad_history_original_scalar_gap_integral_along
      Atarget hAtarget hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim root M epsilon shell hepsilon hshell
      hTemp hb hh Hhistory W hcanonical hWlim hcompare
  have hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  refine ⟨eta,heta,hetalim,
    actual_original_scalar_gap_normalized_envelope_along
      (hTemp.trans_le (sub_le_self T hepsilon)) hAtarget eta M hxlim Hgap,?_⟩
  intro htotal v hv hvA
  exact actual_original_scalar_gap_normalized_l1_tendsto_zero_along
    (hTemp.trans_le (sub_le_self T hepsilon)) hAtarget eta hetalim M htotal hxlim Hgap v hv hvA

end OAI.SKFluctuations.LaplaceWindowFormalization
