module

public import ComparisonSignedCavityActualTargetMeanReductionAlong
public import ComparisonNativeContinuumScalarPairRefinement

@[expose] public section

noncomputable section
open Filter Set
open scoped Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

private theorem target_scalar_approximation_triangle
    (s a gamma r t e d : ℝ) (H : |s-a-r-t|≤e) (HA : |a-gamma|≤d) :
    |s-gamma-r-t|≤e+d := by
  rw [show s-gamma-r-t=(s-a-r-t)+(a-gamma) by ring]
  exact (abs_add_le _ _).trans (add_le_add H HA)

theorem actual_selected_bad_history_continuum_target_mean_reduction_along
    (Bclock Temp Ccut Couter : ℝ)
    (hTemp : 0 < Temp) (hCcut : 0 ≤ Ccut) (houter : 0 < Couter)
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
      ∀ᶠn in atTop,∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤Temp,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀u∈us,let i:=retainedMassPrefixIndex u.val as
        ∀U V : ℕ,i<U → U ≤ V → V ≤ as.length → u.val ≤ Ccut*x n →
          partitionPoint 0 as V ≤ Couter*(M n).canonicalDirectTestBandScale →
          let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
          let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
          abs (orderedPathS (dim n+1) (M n).bf (M n).hf u.val-
            scalarCovarianceResponse hTemp ((M n).inheritedScalarMassProfile hTemp htotal)
              (actualMixedClock (dim n+1) (M n).bf (M n).hf u.val)-
            2*((M n).bf u.val:ℝ)*chi*nativeActualTargetLongitudinalResponse (M n) as i V-
            nativeActualTargetOriginalTaylorPart (M n) as i U) ≤ eta n*(x n)^3 := by
  obtain ⟨eta,heta,Heta,Hrate⟩:=actual_selected_bad_history_target_mean_reduction_along
    Bclock Temp Ccut Couter hTemp.le hCcut houter hm hdelta hroom hcl hcu hAz hC0 hCt
    hCs hc0 hmargin hcapmargin dim hdim root M epsilon shell hepsilon hb hh Hhistory
    x hxs hxlim hsmall hWlim
  have Htotal:=NativeOverlapMinimum.actual_selected_bad_history_total_clock_and_root
    dim root M epsilon shell hepsilon hb hh Hhistory
  let e:=fun n=>((dim n+1:ℕ):ℝ)^(-(1:ℝ))
  have He : Tendsto e atTop (𝓝 0) := by
    have H:=(tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).comp
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)).comp hdim)
    simpa only [Function.comp_def,e] using H
  refine ⟨fun n=>eta n+e n,fun n=>add_nonneg (heta n) (by dsimp only [e];positivity),?_,?_⟩
  · simpa only [add_zero] using Heta.add He
  · filter_upwards [Hrate,Htotal] with n hn ht
    refine ⟨ht.1,?_⟩
    intro L us hus hret hmesh
    have hx:=(M n).hxs.trans_le (hxs n)
    have Hscalar:=(M n).inherited_continuum_scalar_pair_errors_on_all_retained_masses
      hTemp ht.1 ht.2 us hus (e n*(x n)^3) (by dsimp only [e];positivity)
    filter_upwards [hn L us hus hret hmesh,Hscalar] with jGrid hj hscalar
    dsimp only at hj hscalar ⊢
    intro u hu U V hi hUV hV hmass hVmass
    let as:=finiteCutMasses us jGrid
    let i:=retainedMassPrefixIndex u.val as
    have ho:=finiteCutMasses_ordered us hus jGrid
    have Hret : partitionPoint 0 as i=u.val :=
      nativeRetainedCut_partitionPoint as ho u (finiteCutMasses_nodes us jGrid hu)
    have Hcenter : nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as i=
        orderedPathS (dim n+1) (M n).bf (M n).hf u.val := by
      have H:=native_ordered_source_center_eq_completed (dim n) (M n).bf (M n).hf
        (M n).inherited_bf_monotone (M n).inherited_hf_monotone (partitionPoint_mem as ho i)
      rw [Hret] at H
      unfold nativePhysicalResourceCenter
      rw [Hret]
      exact H.symm
    have hmass' : partitionPoint 0 as i≤Ccut*x n := by rw [Hret];exact hmass
    have HB:=hj i U V hi hUV hV hmass' hVmass
    rw [Hcenter,Hret] at HB
    have HA:=target_scalar_approximation_triangle _ _ _ _ _ _ _ HB (hscalar u hu)
    exact HA.trans_eq (by ring)

end OAI.SKFluctuations.Cavity
