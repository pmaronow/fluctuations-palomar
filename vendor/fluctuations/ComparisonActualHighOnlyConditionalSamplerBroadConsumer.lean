module

public import ComparisonActualHighOnlyConditionalCanonicalOrdinaryConsumer
public import ComparisonActualHighOnlyConditionalCanonicalBroadConsumer
public import ComparisonActualHighOnlyConditionalInitialBroadPrefix
public import ComparisonActualHighOnlyConditionalInitialBroadGeometry
public import ComparisonActualHighOnlyConditionalErrorSliceIdentity

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal
set_option maxHeartbeats 18000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock:ℝ}

theorem eventually_actual_conditional_sampler_broad_error_high_only
    (ell:ℕ) (hell:2 < ell) (Bclock:ℝ)
    (hm:0 < m) (hdelta:0 < delta) (hroom:delta < 3*m)
    (hcl:0 < cl) (hcu:0 < cu) (hAz:0 ≤ Az) (hC0:0 < C0) (hCt:0 ≤ Ct)
    (horder:(delta+2)/((ell:ℝ)-1) ≤ delta) :
    ∀ᶠn:ℕ in atTop,∀(a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
      (hs:a.data.s ≤ 1/4) (hsxs:a.data.s ≤ a.xs),
      a.data.d ≤ 1 → a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      a.xs+1 ≤ a.data.N → ∀(P:a.Potential) (cap:ShiftedCapInterval a P)
        (f:WholeCapBroadSampler cap) (i:Fin f.count),
      (P.H cap.left=0 ∨ cap.left=0) ∧ (P.H cap.right=0 ∨ cap.right=1) →
      (∫u in 0..1,(f.slice i).indicator (fun _=>1) (a.R u)*a.comparisonErrorDensity u) ≤
        a.data.N^(6*delta)*a.data.E := by
  have HB:=eventually_actual_conditional_canonical_broad_crop_error_high_only ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt horder
  have Hfirst:=eventually_actual_conditional_initial_broad_prefix_error_high_only ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt horder
  filter_upwards [HB,Hfirst] with n hnB hnFirst
  intro a hs hsxs hd1 hxs hy P cap f i hcontacts
  let l:=a.R (f.node i.val)
  let z:=a.R (f.node (i.val+1))
  let v:=f.scale i
  have HG:=f.geometry i
  have HN:=f.nodes_mem i
  have hαl:a.alpha.val.val l=f.node i.val:=a.shiftedNativeModel.R_spec HN.1
  have hαz:a.alpha.val.val z=f.node (i.val+1):=a.shiftedNativeModel.R_spec HN.2
  have hlz:l < z:=by
    have H:=a.shiftedNativeModel.R_strictMonoOn HN.1 HN.2 HG.2.2.2.2.2.2
    exact H
  have hzcap:z ≤ cap.right:=by
    calc z ≤ a.R (a.alpha.val.val cap.right):=a.shiftedNativeModel.R_monotone HG.2.2.2.2.2.1
         _=cap.right:=a.shiftedNativeModel.R_inverse ⟨cap.hleft.trans cap.hlt.le,cap.hright⟩
  have hcapL:cap.left ≤ l:=by
    calc cap.left=a.R (a.alpha.val.val cap.left):=(a.shiftedNativeModel.R_inverse
           ⟨cap.hleft,cap.hlt.le.trans cap.hright⟩).symm
         _ ≤ l:=a.shiftedNativeModel.R_monotone ((le_max_left _ _).trans HG.2.2.2.2.1)
  have hw:=f.width_bounds i
  have hv:0 < v:=(massCoverBase_pos (a:=a)).trans_le HG.1
  have hv1:v ≤ 1:=hw.1.trans hw.2.2
  have hUv:a.data.U ≤ v:=(le_max_left _ _).trans HG.1
  have HI:=a.massSlice_error_integral_high_only HN.1 HN.2 HG.2.2.2.2.2.2.le
  by_cases hl0:0 < l
  · have HH:=hnB a hs hsxs hd1 hxs hy P cap l z v hcontacts hl0 hlz hcapL hzcap hv hv1 hUv
      (by rw [hαl];exact HG.2.2.1)
      (by rw [hαz];exact le_min HG.2.2.2.1 HN.2.2)
      (by rw [hαz,hαl];exact HG.2.1)
    dsimp only [WholeCapBroadSampler.slice]
    rw [HI]
    simpa only [hαl,hαz] using HH
  · have hlzero:l=0:=le_antisymm (le_of_not_gt hl0) (a.shiftedNativeModel.R_bounds _).1
    have hnode:f.node i.val=a.data.s:=by rw [hlzero,a.alpha.property.1] at hαl;exact hαl.symm
    have hbase:a.massCoverBase ≤ a.data.s:=by
      have H:=(le_max_right _ _).trans HG.2.2.2.2.1
      rw [hnode] at H
      exact H
    have hUs:a.data.U ≤ a.data.s:=(le_max_left _ _).trans hbase
    have hleft:cap.left=0:=by
      by_contra H
      have hlpos:0 < cap.left:=lt_of_le_of_ne cap.hleft (fun hh=>H hh.symm)
      have Hstrict:=inverseConstraint_strictMonoOn a.data.hc a.data.hk a.data.hkc a.alpha.property
        (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num)
        ⟨cap.hleft,cap.hlt.le.trans cap.hright⟩ hlpos
      rw [a.alpha.property.1] at Hstrict
      have Hmass:=(le_max_left _ _).trans HG.2.2.2.2.1
      rw [hnode] at Hmass
      exact Hstrict.not_ge Hmass
    have hi0:i.val=0:=by
      by_contra H
      have Hscale:=f.noninitial_scale_above_wall_high_only i H
      have Hnode:=HG.2.2.1
      rw [hnode] at Hnode
      exact Hscale.not_ge Hnode
    have HF:=f.initial_nodes_scale_high_only hUs hleft
    have hright:4*a.data.s ≤ a.alpha.val.val cap.right:=by
      have H:=HG.2.2.2.2.2.1
      simpa only [hi0,Nat.zero_add,HF.2.2.1] using H
    have HH:=hnFirst a hs hsxs hUs hd1 hxs hy P cap hleft hcontacts.2 hright
    dsimp only [WholeCapBroadSampler.slice]
    rw [HI]
    simpa only [hi0,Nat.zero_add,HF.2.1,HF.2.2.1] using HH

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
