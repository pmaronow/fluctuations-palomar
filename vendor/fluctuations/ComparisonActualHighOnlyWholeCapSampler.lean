module

public import ComparisonActualHighOnlyCapThermalGeometry
public import ComparisonShiftedNativeMassSliceGeometry
public import ComparisonNativeWholeCapDyadicCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

def massCoverBase (a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) : ℝ:=
  max a.data.U a.data.s

theorem massCoverBase_pos : 0<a.massCoverBase:=a.data.hU.trans_le (le_max_left _ _)

structure WholeCapBroadSampler {P : a.Potential} (cap : ShiftedCapInterval a P) where
  k : ℕ
  j : ℕ
  hnear : nativeDyadicMass a.massCoverBase k ≤ max (a.alpha.val.val cap.left) a.massCoverBase
  hnearNext : max (a.alpha.val.val cap.left) a.massCoverBase<nativeDyadicMass a.massCoverBase (k+1)
  hright : nativeDyadicMass a.massCoverBase j≤a.alpha.val.val cap.right
  hrightNext : a.alpha.val.val cap.right<nativeDyadicMass a.massCoverBase (j+1)
  hgap : k+3≤j

namespace WholeCapBroadSampler
variable {P : a.Potential} {cap : ShiftedCapInterval a P}

abbrev count (f : WholeCapBroadSampler cap):=nativeBroadSliceCount f.k f.j
abbrev node (f : WholeCapBroadSampler cap):=
  nativeBroadSliceNode a.massCoverBase (max (a.alpha.val.val cap.left) a.massCoverBase)
    (a.alpha.val.val cap.right) f.k f.j
abbrev scale (f : WholeCapBroadSampler cap) (i : Fin f.count):=
  nativeBroadSliceScale a.massCoverBase f.k f.j i
abbrev slice (f : WholeCapBroadSampler cap) (i : Fin f.count):=
  a.shiftedNativeModel.massSlice (f.node i.val) (f.node (i.val+1))

theorem geometry (f : WholeCapBroadSampler cap) (i : Fin f.count) :
    a.massCoverBase≤f.scale i ∧ f.scale i≤f.node (i.val+1)-f.node i.val ∧
    f.scale i/2≤f.node i.val ∧ f.node (i.val+1)≤4*f.scale i ∧
    max (a.alpha.val.val cap.left) a.massCoverBase≤f.node i.val ∧
    f.node (i.val+1)≤a.alpha.val.val cap.right ∧ f.node i.val<f.node (i.val+1):=
  nativeBroadSlice_geometry (massCoverBase_pos (a:=a)) f.hnear f.hnearNext f.hright f.hrightNext f.hgap i

theorem nodes_mem (f : WholeCapBroadSampler cap) (i : Fin f.count) :
    f.node i.val∈Icc a.data.s 1 ∧ f.node (i.val+1)∈Icc a.data.s 1 := by
  have hg:=f.geometry i
  have hleft : a.data.s≤f.node i.val:=
    (le_max_right a.data.U a.data.s).trans ((le_max_right _ _).trans hg.2.2.2.2.1)
  have hright1:=(a.alpha.val.property.1 cap.right).2
  exact ⟨⟨hleft,hg.2.2.2.2.2.2.le.trans (hg.2.2.2.2.2.1.trans hright1)⟩,
    ⟨hleft.trans hg.2.2.2.2.2.2.le,hg.2.2.2.2.2.1.trans hright1⟩⟩

theorem contracts (f : WholeCapBroadSampler cap) (i : Fin f.count) :
    a.massCoverBase≤f.scale i ∧ f.node (i.val+1)∈Icc a.data.s 1 ∧
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

theorem width_bounds (f : WholeCapBroadSampler cap) (i : Fin f.count) :
    f.scale i≤(∫r in f.slice i,deriv a.alpha.val.val r) ∧
    (∫r in f.slice i,deriv a.alpha.val.val r)≤4*f.scale i ∧
    (∫r in f.slice i,deriv a.alpha.val.val r)≤1 := by
  have hg:=f.geometry i
  have hn:=f.nodes_mem i
  rw [a.shiftedNativeModel.massSlice_mass hn.1 hn.2 hg.2.2.2.2.2.2.le]
  exact ⟨hg.2.1,by linarith [hn.1.1,a.data.hs.1,hg.2.2.2.1],
    by linarith [hn.1.1,a.data.hs.1,hn.2.2]⟩

theorem disjoint (f : WholeCapBroadSampler cap) :
    Pairwise (fun i j=>Disjoint (f.slice i) (f.slice j)) := by
  have hd:=nativeBroadSlice_pairwise_disjoint (massCoverBase_pos (a:=a))
    f.hnear f.hnearNext f.hright f.hrightNext f.hgap
  intro i j hij
  apply Set.disjoint_left.mpr
  intro r hi hj
  have hmi:=a.shiftedNativeModel.massSlice_profile_mem (f.nodes_mem i).1 (f.nodes_mem i).2 hi
  have hmj:=a.shiftedNativeModel.massSlice_profile_mem (f.nodes_mem j).1 (f.nodes_mem j).2 hj
  exact Set.disjoint_left.mp (hd hij) ⟨hmi.1,hmi.2.le⟩ ⟨hmj.1,hmj.2.le⟩

end WholeCapBroadSampler

theorem exists_whole_cap_broad_sampler {P : a.Potential} (cap : ShiftedCapInterval a P)
    (hbroad : 8*max (a.alpha.val.val cap.left) a.massCoverBase<a.alpha.val.val cap.right) :
    Nonempty (WholeCapBroadSampler cap) := by
  obtain ⟨k,hk,hk1⟩:=nativeDyadicMass_exists_near (massCoverBase_pos (a:=a))
    (le_max_right (a.alpha.val.val cap.left) a.massCoverBase)
  have hbase : a.massCoverBase≤a.alpha.val.val cap.right:=by
    have HH:=le_max_right (a.alpha.val.val cap.left) a.massCoverBase
    have HP:=(massCoverBase_pos (a:=a))
    linarith
  obtain ⟨j,hj,hj1⟩:=nativeDyadicMass_exists_near (massCoverBase_pos (a:=a)) hbase
  exact ⟨⟨k,j,hk,hk1,hj,hj1,native_broad_dyadic_index_gap (massCoverBase_pos (a:=a)) hk hj1 hbroad⟩⟩

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
