module

public import ComparisonActualHighWallCapThermalAssembly
public import ComparisonShiftedNativeMassSliceGeometry
public import ComparisonNativeWholeCapDyadicCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

def criticalMassCoverBase (a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) : ℝ:=
  max (comparisonSmallMass a.data.N a.data.E) (8*a.data.s)

theorem criticalMassCoverBase_pos : 0<a.criticalMassCoverBase:=a.data.hU.trans_le (le_max_left _ _)

structure CriticalWholeCapBroadSampler {P : a.Potential} (cap : ShiftedCapInterval a P) where
  k : ℕ
  j : ℕ
  hnear : nativeDyadicMass a.criticalMassCoverBase k ≤ max (a.alpha.val.val cap.left) a.criticalMassCoverBase
  hnearNext : max (a.alpha.val.val cap.left) a.criticalMassCoverBase<nativeDyadicMass a.criticalMassCoverBase (k+1)
  hright : nativeDyadicMass a.criticalMassCoverBase j≤a.alpha.val.val cap.right
  hrightNext : a.alpha.val.val cap.right<nativeDyadicMass a.criticalMassCoverBase (j+1)
  hgap : k+3≤j

namespace CriticalWholeCapBroadSampler
variable {P : a.Potential} {cap : ShiftedCapInterval a P}

abbrev count (f : CriticalWholeCapBroadSampler cap):=nativeBroadSliceCount f.k f.j
abbrev node (f : CriticalWholeCapBroadSampler cap):=
  nativeBroadSliceNode a.criticalMassCoverBase (max (a.alpha.val.val cap.left) a.criticalMassCoverBase)
    (a.alpha.val.val cap.right) f.k f.j
abbrev scale (f : CriticalWholeCapBroadSampler cap) (i : Fin f.count):=
  nativeBroadSliceScale a.criticalMassCoverBase f.k f.j i
abbrev slice (f : CriticalWholeCapBroadSampler cap) (i : Fin f.count):=
  a.shiftedNativeModel.massSlice (f.node i.val) (f.node (i.val+1))

theorem geometry (f : CriticalWholeCapBroadSampler cap) (i : Fin f.count) :
    a.criticalMassCoverBase≤f.scale i ∧ f.scale i≤f.node (i.val+1)-f.node i.val ∧
    f.scale i/2≤f.node i.val ∧ f.node (i.val+1)≤4*f.scale i ∧
    max (a.alpha.val.val cap.left) a.criticalMassCoverBase≤f.node i.val ∧
    f.node (i.val+1)≤a.alpha.val.val cap.right ∧ f.node i.val<f.node (i.val+1):=
  nativeBroadSlice_geometry (criticalMassCoverBase_pos (a:=a)) f.hnear f.hnearNext f.hright f.hrightNext f.hgap i

theorem nodes_mem (f : CriticalWholeCapBroadSampler cap) (i : Fin f.count) :
    f.node i.val∈Icc a.data.s 1 ∧ f.node (i.val+1)∈Icc a.data.s 1 := by
  have hg:=f.geometry i
  have hleft : a.data.s≤f.node i.val:=
    (show a.data.s ≤ a.criticalMassCoverBase by exact (by linarith [a.data.hs.1] : a.data.s ≤ 8*a.data.s).trans (le_max_right _ _)).trans ((le_max_right _ _).trans hg.2.2.2.2.1)
  have hright1:=(a.alpha.val.property.1 cap.right).2
  exact ⟨⟨hleft,hg.2.2.2.2.2.2.le.trans (hg.2.2.2.2.2.1.trans hright1)⟩,
    ⟨hleft.trans hg.2.2.2.2.2.2.le,hg.2.2.2.2.2.1.trans hright1⟩⟩

theorem contracts (f : CriticalWholeCapBroadSampler cap) (i : Fin f.count) :
    a.criticalMassCoverBase≤f.scale i ∧ f.node (i.val+1)∈Icc a.data.s 1 ∧
    f.node (i.val+1)≤4*f.scale i ∧ f.slice i⊆Ioo cap.left cap.right ∧
    (∀r∈f.slice i,a.alpha.val.val r≤f.node (i.val+1)) ∧
    f.scale i≤∫r in f.slice i,deriv a.alpha.val.val r := by
  have hg:=f.geometry i
  have hn:=f.nodes_mem i
  refine ⟨hg.1,hn.2,hg.2.2.2.1,?_,?_,?_⟩
  · intro r hr
    have hl:=a.shiftedNativeModel.R_monotone ((le_max_left _ _).trans hg.2.2.2.2.1)
    have hz:=a.shiftedNativeModel.R_monotone hg.2.2.2.2.2.1
    rw [a.shiftedNativeModel.R_inverse ⟨cap.hleft,cap.hlt.le.trans cap.hright⟩] at hl
    rw [a.shiftedNativeModel.R_inverse ⟨cap.hleft.trans cap.hlt.le,cap.hright⟩] at hz
    exact ⟨hl.trans_lt hr.1,hr.2.trans_le hz⟩
  · intro r hr
    exact (a.shiftedNativeModel.massSlice_profile_mem hn.1 hn.2 hr).2.le
  · rw [a.shiftedNativeModel.massSlice_mass hn.1 hn.2 hg.2.2.2.2.2.2.le]
    exact hg.2.1

theorem width_bounds (f : CriticalWholeCapBroadSampler cap) (i : Fin f.count) :
    f.scale i≤(∫r in f.slice i,deriv a.alpha.val.val r) ∧
    (∫r in f.slice i,deriv a.alpha.val.val r)≤4*f.scale i ∧
    (∫r in f.slice i,deriv a.alpha.val.val r)≤1 := by
  have hg:=f.geometry i
  have hn:=f.nodes_mem i
  rw [a.shiftedNativeModel.massSlice_mass hn.1 hn.2 hg.2.2.2.2.2.2.le]
  exact ⟨hg.2.1,by linarith [hn.1.1,a.data.hs.1,hg.2.2.2.1],
    by linarith [hn.1.1,a.data.hs.1,hn.2.2]⟩

theorem disjoint (f : CriticalWholeCapBroadSampler cap) :
    Pairwise (fun i j=>Disjoint (f.slice i) (f.slice j)) := by
  have hd:=nativeBroadSlice_pairwise_disjoint (criticalMassCoverBase_pos (a:=a))
    f.hnear f.hnearNext f.hright f.hrightNext f.hgap
  intro i j hij
  apply Set.disjoint_left.mpr
  intro r hi hj
  have hmi:=a.shiftedNativeModel.massSlice_profile_mem (f.nodes_mem i).1 (f.nodes_mem i).2 hi
  have hmj:=a.shiftedNativeModel.massSlice_profile_mem (f.nodes_mem j).1 (f.nodes_mem j).2 hj
  exact Set.disjoint_left.mp (hd hij) ⟨hmi.1,hmi.2.le⟩ ⟨hmj.1,hmj.2.le⟩

end CriticalWholeCapBroadSampler

theorem exists_critical_whole_cap_broad_sampler {P : a.Potential} (cap : ShiftedCapInterval a P)
    (hbroad : 8*max (a.alpha.val.val cap.left) a.criticalMassCoverBase<a.alpha.val.val cap.right) :
    Nonempty (CriticalWholeCapBroadSampler cap) := by
  obtain ⟨k,hk,hk1⟩:=nativeDyadicMass_exists_near (criticalMassCoverBase_pos (a:=a))
    (le_max_right (a.alpha.val.val cap.left) a.criticalMassCoverBase)
  have hbase : a.criticalMassCoverBase≤a.alpha.val.val cap.right:=by
    have HH:=le_max_right (a.alpha.val.val cap.left) a.criticalMassCoverBase
    have HP:=(criticalMassCoverBase_pos (a:=a))
    linarith
  obtain ⟨j,hj,hj1⟩:=nativeDyadicMass_exists_near (criticalMassCoverBase_pos (a:=a)) hbase
  exact ⟨⟨k,j,hk,hk1,hj,hj1,native_broad_dyadic_index_gap (criticalMassCoverBase_pos (a:=a)) hk hj1 hbroad⟩⟩

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
