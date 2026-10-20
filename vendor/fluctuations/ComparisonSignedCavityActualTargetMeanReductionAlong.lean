module

public import ComparisonSignedCavityActualTargetMeanReadout
public import ComparisonSignedCavityActualTargetMeanTransportAlong
public import ComparisonSignedCavityActualTargetMeanCorrectionAlong

@[expose] public section

noncomputable section
open Filter Set
open scoped Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

theorem actual_selected_bad_history_target_mean_reduction_along
    (Bclock Temp Ccut Couter : ℝ)
    (hTemp : 0 ≤ Temp) (hCcut : 0 ≤ Ccut) (houter : 0 < Couter)
    {m delta cl cu Az C0 Ct D Cs c0 : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n : ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : NativeOverlapMinimum.ActualSelectedBadHistoryChain c0 root M)
    (x : ℕ → ℝ) (hxs : ∀n,(M n).xs ≤ x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hsmall : ∀ᶠn in atTop,
      (M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0)) :
    ∃eta : ℕ → ℝ,(∀n,0 ≤ eta n) ∧ Tendsto eta atTop (𝓝 0) ∧
      ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀i U V : ℕ,i<U → U ≤ V → V ≤ as.length →
          partitionPoint 0 as i ≤ Ccut*x n →
          partitionPoint 0 as V ≤ Couter*(M n).canonicalDirectTestBandScale →
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          abs (nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as i-
            nativeOriginalScalarPairMean as K i-
            2*((M n).bf (partitionPoint 0 as i):ℝ)*chi*nativeActualTargetLongitudinalResponse (M n) as i V-
            nativeActualTargetOriginalTaylorPart (M n) as i U) ≤ eta n*(x n)^3 := by
  obtain ⟨etaT,hetaT,HetaT,HT⟩:=actual_selected_bad_history_target_mean_transport_vanishing_along
    Bclock Temp Ccut Couter hTemp hCcut houter hm hdelta hroom hcl hcu hAz hC0 hCt
    hCs hc0 hmargin hcapmargin dim hdim root M epsilon shell hepsilon hb hh Hhistory
    x hxs hxlim hsmall hWlim
  obtain ⟨etaM,hetaM,HetaM,HM⟩:=actual_selected_bad_history_target_mean_correction_vanishing_along
    Bclock Temp Ccut hTemp hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
    hc0 hmargin hcapmargin dim hdim root M epsilon shell hepsilon hb hh Hhistory x hxs hxlim
  refine ⟨fun n=>etaM n+etaT n,fun n=>add_nonneg (hetaM n) (hetaT n),?_,?_⟩
  · simpa only [add_zero] using HetaM.add HetaT
  · filter_upwards [HT,HM] with n hnT hnM
    intro L us hus hret hmesh
    filter_upwards [hnT L us hus hret hmesh,hnM us hus] with jGrid hjT hjM
    dsimp only at hjT hjM ⊢
    intro i U V hi hUV hV hmass hVmass
    have H:=actual_target_mean_eq_correction_response_transport_taylor
      (M n) (finiteCutMasses us jGrid) i U V hi (hUV.trans hV)
      (finiteCutMasses_ordered us hus jGrid)
    dsimp only at H
    rw [H]
    rw [show nativeActualTargetOriginalMeanCorrection (M n) (finiteCutMasses us jGrid) i U+
        2*((M n).bf (partitionPoint 0 (finiteCutMasses us jGrid) i):ℝ)*
          (scalarTerminal.schedule (scalarBoundaryClocks (finiteCutMasses us jGrid)
            (relocatedClock U 0 (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (finiteCutMasses us jGrid))))).H 0 0*
          nativeActualTargetLongitudinalResponse (M n) (finiteCutMasses us jGrid) i V+
        nativeActualTargetMeanTransportError (M n) (finiteCutMasses us jGrid) i U V+
        nativeActualTargetOriginalTaylorPart (M n) (finiteCutMasses us jGrid) i U-
        2*((M n).bf (partitionPoint 0 (finiteCutMasses us jGrid) i):ℝ)*
          (scalarTerminal.schedule (scalarBoundaryClocks (finiteCutMasses us jGrid)
            (relocatedClock U 0 (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (finiteCutMasses us jGrid))))).H 0 0*
          nativeActualTargetLongitudinalResponse (M n) (finiteCutMasses us jGrid) i V-
        nativeActualTargetOriginalTaylorPart (M n) (finiteCutMasses us jGrid) i U=
        nativeActualTargetOriginalMeanCorrection (M n) (finiteCutMasses us jGrid) i U+
        nativeActualTargetMeanTransportError (M n) (finiteCutMasses us jGrid) i U V by ring]
    have HB:=(abs_add_le _ _).trans (add_le_add
      (hjM i U hi (hUV.trans hV) hmass) (hjT i U V hi hUV hV hmass hVmass))
    exact HB.trans_eq (by ring)

end OAI.SKFluctuations.Cavity
