module

public import ComparisonActualHighOnlyMacroscopicProfile
public import ComparisonActualHighOnlyComparableBandShrinkingDirectProfile
public import ComparisonNativeActualGeneralHistoryCompleteStrictTest

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar Cavity NativeOverlapMinimum ActualHighOnlyOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 24000000
theorem exists_actual_high_only_comparable_complete_direct_profile
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1 : ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ) → ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualHighOnlyOverlapMinimum.HighOnlyActualComparableBandContext M T)
    (hWupper : ∀ᶠn in atTop,(M n).canonicalDirectTestBandScale ≤ 1)
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃phi : ℕ → ℕ,StrictMono phi ∧
      ∃htotal : ∀n,∀u∈Icc (0 : ℝ) 1,(M (phi n)).h u+(M (phi n)).b u ≤ T,
        ∃d : ActualHighOnlyLocalScalarLimitData
          (G.hT) T
          (fun n => M (phi n)) htotal,
          let hT := G.hT
          let kappa := (T/T)*scalarInitialDensityConstant hT d.beta
          (∀t > 0,d.U.mass t=kappa*t) ∧ (∀t > 0,d.V.mass t=kappa*t) ∧
            cl ≤ kappa ∧ kappa ≤ cu ∧
            2*T*Real.exp (-12*T) ≤ kappa ∧
            kappa ≤ T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) ∧
            TendstoLocallyUniformlyOn
              (fun n v=>(M (phi n)).R ((M (phi n)).xs*v)/(M (phi n)).xs)
              (fun v=>v/kappa) atTop (Ioi (0:ℝ)) ∧ d.sigma=0 ∧
            (∀t ≥ 0,comparisonLocalScalarLimitSlope hT T d.beta d.U d.sigma t=0) ∧
            (∀t ≥ 0,comparisonLocalScalarLimitResponse hT T d.beta d.U d.sigma t=0) ∧
            ∀R : ℝ,0 < R →
              TendstoUniformlyOn (fun n => comparisonLocalScalarSlope hT T
                ((M (phi n)).inheritedScalarMassProfile hT (htotal n)) (M (phi n)).xs)
                (fun _ => 0) atTop (Icc (0 : ℝ) R) ∧
              TendstoUniformlyOn (fun n => comparisonRescaledScalarResponse
                (scalarCovarianceResponse hT ((M (phi n)).inheritedScalarMassProfile hT (htotal n)))
                T (M (phi n)).xs) (fun _ => 0) atTop (Icc (0 : ℝ) R)  := by
  classical
  let W:=fun n=>(M n).canonicalDirectTestBandScale
  by_cases HW : Tendsto W atTop (𝓝 0)
  · exact exists_actual_selected_bad_history_complete_direct_profile_along_comparable_shrinking_high_only
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim M G W (fun _=>rfl) HW hcompare
  · obtain ⟨w0,hw0,theta,htheta,Htheta⟩:=
      exists_positive_lower_subsequence_of_nonnegative_not_tendsto_zero W
        (fun n=>(M n).canonical_direct_test_band_pos.le) HW
    obtain ⟨phi,hphi,Hprofile⟩:=
      exists_actual_selected_bad_history_complete_direct_profile_along_comparable_macro_high_only
        hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
        (fun n=>dim (theta n)) (hdim.comp htheta.tendsto_atTop)
        (fun n=>M (theta n)) (G.comp theta htheta) (fun n=>W (theta n)) (fun _=>rfl)
        w0 hw0 (Eventually.of_forall Htheta) (htheta.tendsto_atTop.eventually hWupper)
        (fun n=>hcompare (theta n))
    exact ⟨theta ∘ phi,htheta.comp hphi,Hprofile⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
