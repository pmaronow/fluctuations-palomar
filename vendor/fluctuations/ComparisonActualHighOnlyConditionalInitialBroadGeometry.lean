module

public import ComparisonActualHighOnlyWholeCapCover

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal
set_option maxHeartbeats 10000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace ActualHighOnlyOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
variable {a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
variable {P:a.Potential} {cap:ShiftedCapInterval a P}

namespace WholeCapBroadSampler

theorem initial_k_zero_high_only (f:WholeCapBroadSampler cap)
    (hUs:a.data.U ≤ a.data.s) (hleft:cap.left=0) : f.k=0 := by
  have hspos:0 < a.data.s:=a.data.hU.trans_le hUs
  have HK:=f.hnear
  simp only [massCoverBase,max_eq_right hUs,hleft,a.alpha.property.1,max_self] at HK
  by_contra H
  have hK:1 ≤ f.k:=by omega
  have HL:=nativeDyadicMass_monotone hspos.le hK
  simp only [nativeDyadicMass,pow_one] at HL HK
  nlinarith only [HL,HK,hspos]

theorem initial_nodes_scale_high_only (f:WholeCapBroadSampler cap)
    (hUs:a.data.U ≤ a.data.s) (hleft:cap.left=0) :
    2 ≤ f.count ∧ f.node 0=a.data.s ∧ f.node 1=4*a.data.s ∧
      ∀i:Fin f.count,i.val=0 → f.scale i=2*a.data.s := by
  have HK:=f.initial_k_zero_high_only hUs hleft
  have HC:2 ≤ f.count:=by
    dsimp only [WholeCapBroadSampler.count,nativeBroadSliceCount]
    have H:=f.hgap
    omega
  refine ⟨HC,?_,?_,?_⟩
  · simp only [WholeCapBroadSampler.node,nativeBroadSliceNode,ite_true,hleft,a.alpha.property.1,
      massCoverBase,max_eq_right hUs,max_self]
  · have H1:1 < nativeBroadSliceCount f.k f.j:=by change 1 < f.count;omega
    have H1':1 < nativeBroadSliceCount 0 f.j:=by simpa only [HK] using H1
    simp only [WholeCapBroadSampler.node,nativeBroadSliceNode,show (1:ℕ)≠0 by norm_num,
      ite_false,HK,H1',ite_true,massCoverBase,max_eq_right hUs,nativeDyadicMass]
    ring
  · intro i hi
    simp only [WholeCapBroadSampler.scale,nativeBroadSliceScale,hi,ite_true,HK,
      massCoverBase,max_eq_right hUs,nativeDyadicMass]
    ring

theorem noninitial_scale_above_wall_high_only (f:WholeCapBroadSampler cap)
    (i:Fin f.count) (hi:i.val≠0) : a.data.s < f.scale i/2 := by
  have HI:2 ≤ f.k+1+i.val:=by omega
  have HM:=nativeDyadicMass_monotone (massCoverBase_pos (a:=a)).le HI
  have HS:a.data.s ≤ a.massCoverBase:=le_max_right _ _
  have HB:=massCoverBase_pos (a:=a)
  change nativeDyadicMass a.massCoverBase 2 ≤ nativeDyadicMass a.massCoverBase (f.k+1+i.val) at HM
  have HE:f.scale i=nativeDyadicMass a.massCoverBase (f.k+1+i.val):=by
    simp only [WholeCapBroadSampler.scale,nativeBroadSliceScale,ite_eq_right hi]
  rw [HE]
  norm_num only [nativeDyadicMass,pow_two] at HM ⊢
  nlinarith only [HM,HS,HB]

end WholeCapBroadSampler
end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
