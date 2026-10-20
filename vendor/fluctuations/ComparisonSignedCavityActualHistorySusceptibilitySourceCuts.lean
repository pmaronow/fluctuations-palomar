module

public import ComparisonSignedCavityActualHistorySusceptibilitySource
public import ComparisonSignedCavityActualSharpSourceCutReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 16000000

theorem actual_selected_bad_history_susceptibility_on_source_cuts_along
    {m delta cl cu Az C0 Ct D Bclock T L Cs c0 A cFirst cK : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hA : 0 ≤ A)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hTemp : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) (T-epsilon) L Cs (w n))
    (high outer : ℕ→PositiveMass) (radius : ℕ→ℝ)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀us : List PositiveMass,
      (∀u∈us,u.val ≤ 1)→(w n).star∈us→(high n)∈us→(outer n)∈us→∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let star:=retainedMassPrefixIndex (w n).star.val as
        let U:=retainedMassPrefixIndex (high n).val as
        let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let S:=nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |(T-epsilon)*chi^2-1| ≤ C*(W n)^2+
          |nativeActualConstantJointStarSource (dim n) as star U b h K S|/
            ((3*(starMassBandConstant cu Az/cu)/4)*W n) := by
  obtain ⟨C,hC,HC⟩:=actual_selected_bad_history_susceptibility_bound_by_joint_source_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hA hmargin hcapmargin
    dim hdim root M epsilon shell hepsilon hTemp hb hh Hhistory W hxs hWlim w hw
  refine ⟨C,hC,?_⟩
  filter_upwards [HC,Hcuts] with n hnC hnCuts
  intro us hus hstar hhigh houter
  filter_upwards [hnC us hus hstar] with k hk
  dsimp only at hk ⊢
  let as:=finiteCutMasses us k
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  let V:=retainedMassPrefixIndex (outer n).val as
  obtain ⟨hs,hUV,hV,_,_,hcap,_,_,_,_,_,_,before,after,hgrid,hindex⟩:=
    hnCuts.finite_net_readout us hus hstar hhigh houter k
  have Hbuffer : (high n).val < partitionPoint 0 as V:=by
    rw [nativeRetainedCut_partitionPoint as (finiteCutMasses_ordered us hus k)
      (outer n) (finiteCutMasses_nodes us k houter)]
    exact hnCuts.high_lt
  have H:=hk before after (high n) hgrid.symm V
  rw [←hgrid,hindex] at H
  exact H hs hUV.le hV Hbuffer hcap

end OAI.SKFluctuations.LaplaceWindowFormalization
