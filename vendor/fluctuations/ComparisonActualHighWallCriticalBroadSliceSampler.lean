module

public import ComparisonActualHighWallSelectedDefectLimit
public import ComparisonActualHighWallCriticalBroadBudgets
public import ComparisonNativeBroadSliceSampler

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 22000000
attribute [local instance] Classical.propDecidable
namespace ActualHighWallOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (cap : ShiftedCapInterval a P)

abbrev croppedRows (l z : ℝ) (as : List PositiveMass) :=
  P.retainedRows (fun _ : Fin 1=>cap) {l,z,cap.left,cap.right} l z as

theorem croppedSupport_eq {l z : ℝ} (hl : cap.left≤l) (hz : z≤cap.right) :
    P.retainedSupport (fun _ : Fin 1=>cap) l z=Ioo l z := by
  ext r
  simp only [Potential.retainedSupport,mem_inter_iff,NativeSelectedMask.fixedSupport,mem_ofPred_eq]
  constructor
  · exact fun h=>h.1
  · intro hr
    exact ⟨hr,Or.inl ⟨0,⟨hl.trans_lt hr.1,hr.2.trans_le hz⟩⟩⟩

theorem croppedRows_data {l z : ℝ} (hl : cap.left≤l) (hz : z≤cap.right)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (i : Fin ((sampleClockSteps a.shiftedNativeModel.q 0 as).length+1))
    (hi : i∈cap.croppedRows l z as) :
    i.val<as.length ∧ 0<pathMassDifferences (sampleClockSteps a.shiftedNativeModel.q 0 as) 0 i ∧
      a.data.s≤partitionPoint 0 as i.val ∧ l≤a.shiftedNativeModel.R (partitionPoint 0 as i.val) ∧
      a.shiftedNativeModel.R (partitionPoint 0 as (i.val+1))≤z ∧
      a.shiftedNativeModel.R (partitionPoint 0 as i.val)∈Ioo cap.left cap.right := by
  have hd:=(P.retainedRows_mem (fun _ : Fin 1=>cap) {l,z,cap.left,cap.right} l z as i).mp hi
  have hneL:=hd.2.1.1 cap.left (by simp)
  have hneR:=hd.2.1.1 cap.right (by simp)
  have hrr:=a.shiftedNativeModel.R_monotone (partitionPoint_mono as ho (Nat.le_succ i.val))
  exact ⟨hd.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.1,hd.2.2.2.2.2,
    lt_of_le_of_ne (hl.trans hd.2.2.2.2.1) hneL.symm,
    lt_of_le_of_ne ((hrr.trans hd.2.2.2.2.2).trans hz) hneR⟩

theorem croppedRows_support_ae {l z : ℝ} (hl0 : a.data.rmin<l) (hz1 : z≤1)
    (hl : cap.left≤l) (hz : z≤cap.right)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hm : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) :
    ∀ᵐr∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠj in atTop,
      (r∈NativeSelectedMask.finiteSupport (fun i=>a.shiftedNativeModel.R
        (partitionPoint 0 (as j) i)) (cap.croppedRows l z (as j)) ↔r∈Ioo l z) := by
  simpa only [croppedRows,cap.croppedSupport_eq hl hz] using
    P.retainedRows_support_ae (fun _ : Fin 1=>cap) {l,z,cap.left,cap.right}
      as mesh ho he hm hm0 hlim hl0 hz1

theorem croppedRows_binary_columns {l z : ℝ} (hl0 : a.data.rmin<l) (hz1 : z≤1)
    (hl : cap.left≤l) (hz : z≤cap.right)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hm : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) :
    (∀ᵐr∂volume.restrict (Ioo l z),Tendsto (fun j=>a.shiftedNativeModel.unitColumn
      (as j) (cap.croppedRows l z (as j)) (fun _=>(0:Fin 1)) (fun _=>1) r) atTop
        (𝓝 ((Ioo l z).indicator (fun _=>1) r))) ∧
    Tendsto (fun j=>∫r in Ioo l z,|a.shiftedNativeModel.unitColumn (as j)
      (cap.croppedRows l z (as j)) (fun _=>(0:Fin 1)) (fun _=>1) r-
        (Ioo l z).indicator (fun _=>1) r|) atTop (𝓝 0) := by
  apply a.shiftedNativeModel.binary_column_L1_of_support_eventually as ho (fun _=>1)
    (fun j=>cap.croppedRows l z (as j)) (fun _ _=>(0:Fin 1))
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).1) (Ioo l z)
  exact ae_restrict_of_ae_restrict_of_subset
    (Ioo_subset_Ioo (a.data.hrbounds.1.le.trans hl0.le) hz1) (cap.croppedRows_support_ae hl0 hz1 hl hz as mesh ho he hm hm0 hlim)

theorem croppedRows_mass_tendsto {l z : ℝ} (hl0 : a.data.rmin<l) (hz1 : z≤1)
    (hl : cap.left≤l) (hz : z≤cap.right)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hm : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun j=>physicalWindowMass (sampleClockSteps a.shiftedNativeModel.q 0 (as j)) 0
      (cap.croppedRows l z (as j))) atTop (𝓝 (∫r in Ioo l z,deriv a.alpha.val.val r)) := by
  apply a.shiftedNativeModel.binary_mass_tendsto_of_support_eventually as ho he
    (fun j=>cap.croppedRows l z (as j))
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).1)
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).2.2.1)
    hl0 hz1
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).2.2.2.1)
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).2.2.2.2.1)
    (Ioo l z) measurableSet_Ioo (Subset.refl _)
  exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo (a.data.hrbounds.1.le.trans hl0.le) hz1)
    (cap.croppedRows_support_ae hl0 hz1 hl hz as mesh ho he hm hm0 hlim)

theorem croppedRows_original_mass_L1 {l z : ℝ} (hl0 : a.data.rmin<l) (hz1 : z≤1)
    (hl : cap.left≤l) (hz : z≤cap.right)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hm : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun j=>∫u in 0..1,|nativeSelectedMassMask a.shiftedNativeModel.q (as j)
      (cap.croppedRows l z (as j)) u-(Ioo l z).indicator (fun _=>1)
        (a.shiftedNativeModel.R u)|) atTop (𝓝 0) := by
  apply a.shiftedNativeModel.binary_mass_L1_of_support_eventually as ho he
    (fun j=>cap.croppedRows l z (as j))
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).1)
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).2.2.1)
    hl0 hz1
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).2.2.2.1)
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).2.2.2.2.1)
    (Ioo l z) measurableSet_Ioo (Subset.refl _)
  exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo (a.data.hrbounds.1.le.trans hl0.le) hz1)
    (cap.croppedRows_support_ae hl0 hz1 hl hz as mesh ho he hm hm0 hlim)

theorem croppedRows_original_defect_tendsto {l z : ℝ} (hl0 : a.data.rmin<l) (hz1 : z≤1)
    (hl : cap.left≤l) (hz : z≤cap.right)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hm : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun j=>a.shiftedNativeModel.selectedDefect (as j) (cap.croppedRows l z (as j))) atTop
      (𝓝 (∫r in Ioo l z,deriv a.alpha.val.val r*a.shiftedNativeModel.thermal
        (a.alpha.val.val r))) := by
  apply a.shiftedNativeModel.selectedDefect_tendsto_radius as mesh ho he hm hlim
    (fun j=>cap.croppedRows l z (as j))
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).1)
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).2.2.1)
    hl0 hz1
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).2.2.2.1)
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).2.2.2.2.1)
    (Ioo l z) measurableSet_Ioo (Subset.refl _)
  exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo (a.data.hrbounds.1.le.trans hl0.le) hz1)
    (cap.croppedRows_support_ae hl0 hz1 hl hz as mesh ho he hm hm0 hlim)

end ActualHighWallOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
