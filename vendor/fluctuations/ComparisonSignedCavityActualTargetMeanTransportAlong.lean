module

public import ComparisonSignedCavityActualTargetMeanTransport

@[expose] public section

noncomputable section
open Filter Set
open scoped Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem actual_selected_bad_history_target_mean_transport_vanishing_along
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
          abs (nativeActualTargetMeanTransportError (M n) as i U V) ≤ eta n*(x n)^3 := by
  obtain ⟨Cf,hCf,Hsource⟩ := NativeOverlapMinimum.actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M epsilon shell hepsilon hTemp hb hh Hhistory
  obtain ⟨eta,heta,Heta,Hrate⟩ :=
    actual_selected_bad_history_target_G_cut_comparison_vanishing_envelope_along
      Bclock Temp Ccut Couter hTemp hCcut houter hm hdelta hroom hcl hcu hAz hC0 hCt
      hCs hc0 hmargin hcapmargin dim hdim root M epsilon shell hepsilon hb hh Hhistory
      x hxs hxlim hsmall hWlim
  refine ⟨fun n=>2*Temp*eta n,fun n=>mul_nonneg (mul_nonneg (by norm_num) hTemp) (heta n),?_,?_⟩
  · simpa only [mul_zero] using Heta.const_mul (2*Temp)
  · filter_upwards [Hsource,Hrate] with n hn hrate
    intro L us hus hret hmesh
    filter_upwards [hrate L us hus hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro i U V hi hUV hV hmass hVmass
    have HH:=hj i U V hi hUV hV hmass hVmass
    have Hbound:=actual_inherited_target_mean_transport_error_bound
      (M n) Temp Cf hTemp hn (finiteCutMasses us jGrid)
      (finiteCutMasses_ordered us hus jGrid) i U V hi (hUV.trans hV)
    have hT : (0:ℝ)≤2*Temp := mul_nonneg (by norm_num) hTemp
    have HC:=mul_le_mul_of_nonneg_left HH.1 hT
    exact Hbound.trans (by simpa only [mul_assoc] using HC)

end OAI.SKFluctuations.Cavity
