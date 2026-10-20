module

public import ComparisonNativeActualLocalTemperatureResponseAlong
public import ComparisonNativeActualHistoryNormalizedScalarGapAlong
public import ComparisonNativeActualSelectedBadHistoryInitialMismatchAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 16000000

theorem actual_selected_bad_history_bounded_strength_response_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (C K : ℝ) (hC : 0 < C) (hK : 0 ≤ K)
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
    (v : ℕ→ℝ) (hv : ∀n,v n∈Icc (0:ℝ) 1) (hvc : ∀n,v n ≤ C*(M n).xs) :
    let hT:=hTemp.trans_le (sub_le_self T hepsilon)
    let nu:=fun n=>comparisonNormalizedClockMass (M n).xs (v n)
    let G:=fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse hT ((M n).inheritedScalarMassProfile hT (htotal n)))
        (T-epsilon) (M n).xs
    let q:=fun n (z : ParisiFinite.OrderPoint)=>
      actualMixedClock (dim n+1) (M n).bf (M n).hf z/((T-epsilon)*(M n).xs)
    (∀n,Integrable (fun z=>G n (q n z)) (nu n)) ∧
      Tendsto (fun n=>∫z,|G n (q n z)|∂nu n) atTop (𝓝 0) ∧
    (∀n,Integrable (fun z=>q n z-(M n).R z/(M n).xs) (nu n)) ∧
      Tendsto (fun n=>∫z,|q n z-(M n).R z/(M n).xs|∂nu n) atTop (𝓝 0) := by
  obtain ⟨_eta,_heta,_hetalim,_Henvelope,Hcavity⟩:=
    exists_actual_selected_bad_history_normalized_scalar_gap_along
      C hC hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
      hmargin hcapmargin hgapmargin dim hdim root M epsilon shell hepsilon hshell
      hTemp hb hh Hhistory W hcanonical hWlim hcompare
  have Hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0):=by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hclock:=actual_selected_bad_history_initial_mismatch_clock_regularity
    dim root M epsilon shell hb hh Hhistory
  have Hnear:=actual_selected_bad_shell_history_near_bare_clocks
    hm hdelta hcl hAz hC0 hc0 hc01 hmargin hcapmargin hgapmargin hdim
    epsilon shell hshell hb hh Hhistory (fun n=>(M n).xs)
    (Eventually.of_forall fun _=>le_rfl) Hxs
  have Hbare : ∀eps > 0,∀ᶠn in atTop,∀z : ParisiFinite.OrderPoint,z.val ≤ v n →
      |(M n).b z-(T-epsilon)| ≤ eps*(M n).xs^2 ∧
        |(M n).h z| ≤ eps*(M n).xs^3 := by
    intro eps heps
    filter_upwards [Hnear C eps hC.le heps] with n hn
    intro z hz
    exact hn z ⟨z.property.1,hz.trans (hvc n)⟩
  have Hcav:=Hcavity htotal v hv (Eventually.of_forall hvc)
  exact actual_inherited_local_temperature_restricted_response_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M (fun n=>(M n).xs)
    (fun _=>le_rfl) Hxs Hclock hTemp (hTemp.trans_le (sub_le_self T hepsilon)) htotal
    (fun n=>{z : ParisiFinite.OrderPoint | (z:ℝ) ≤ v n})
    (fun _=>measurableSet_le measurable_subtype_coe measurable_const)
    C K hC hK (fun n z hz=>hz.trans (hvc n)) hwork Hbare Hcav.1 Hcav.2

end OAI.SKFluctuations.LaplaceWindowFormalization
