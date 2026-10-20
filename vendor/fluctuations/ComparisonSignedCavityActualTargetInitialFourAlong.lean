module

public import ComparisonSignedCavityActualTargetInitialFrozenRate
public import ComparisonNativeActualSelectedBadHistorySourceClocks

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set Filter LaplaceWindowFormalization
open scoped Topology NNReal
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

theorem actual_selected_bad_history_target_initial_four_reduction_along
    (Bclock Temp : ℝ) (hTemp : 0≤Temp)
    {m delta cl cu Az C0 Ct D c0 : ℝ} (hm : 0 < m) (hC0 : 0 < C0)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0≤epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : NativeOverlapMinimum.ActualSelectedBadHistoryChain c0 root M)
    (x : ℕ→ℝ) (hxs : ∀n,(M n).xs≤x n) (hxlim : Tendsto x atTop (𝓝 0)) :
    ∀ᶠn in atTop,∀us : List PositiveMass,(∀u∈us,u.val≤1) →∀ᶠjGrid : ℕ in atTop,
      let as:=finiteCutMasses us jGrid
      ∀(i star U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U≤as.length)
        (W : ℝ),W≠0 → 0<nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
      ∀depth : ℕ,
        let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
        abs (nativeActualTargetLongitudinalResponse (M n) as i U-
          (nativeActualMinimumFourResidualSum (M n) hs hU W depth [st]+
            nativeActualOriginalContinuumCenteredFourGFrontier (M n) as W i star U hi hs hU depth))≤
          ((dim n+1:ℕ):ℝ)^(-m)*(x n)^3 := by
  have Hrate:=hdim.eventually (eventually_actual_inherited_initial_frozen_response_cubic
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D)
    Bclock Temp hTemp hm hC0)
  have Htotal:=NativeOverlapMinimum.actual_selected_bad_history_total_clock_and_root
    dim root M epsilon shell hepsilon hb hh Hhistory
  have HX:=hxlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [Hrate,Htotal,HX] with n hn ht hx
  intro us hus
  filter_upwards [hn (M n) ht.1 ht.2 ((hxs n).trans hx) us hus] with jGrid hj
  dsimp only at hj ⊢
  intro i star U hi hs hU W hW hK depth
  have H:=actual_target_response_eq_four_iteration (M n) (finiteCutMasses us jGrid) W i star U hi hs hU
    (finiteCutMasses_ordered us hus jGrid) hW hK depth
  dsimp only at H
  rw [H,sub_sub_cancel_left,abs_neg]
  exact hj i star U (hi.trans (hs.le.trans hU)) W (x n) (hxs n)

end OAI.SKFluctuations.Cavity
