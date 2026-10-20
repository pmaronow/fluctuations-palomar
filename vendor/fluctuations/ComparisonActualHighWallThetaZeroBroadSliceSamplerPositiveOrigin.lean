module

public import ComparisonActualHighWallThetaZeroBroadSliceSampler
public import ComparisonActualHighWallThetaZeroSelectedRowsGeometryPositiveOrigin
public import ComparisonShiftedNativePositiveOriginSelectedDefectLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option autoImplicit false
set_option maxHeartbeats 24000000
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : Q.Potential} (cap : ShiftedCapInterval Q P)

theorem croppedRows_support_ae_positive_origin {l z : ℝ} (hl0 : Q.data.rmin≤l) (hz1 : z≤1)
    (hl : cap.left≤l) (hz : z≤cap.right)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hm : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) :
    ∀ᵐr∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠj in atTop,
      (r∈NativeSelectedMask.finiteSupport (fun i=>Q.shiftedNativeModel.R
        (partitionPoint 0 (as j) i)) (cap.croppedRows l z (as j)) ↔r∈Ioo l z) := by
  simpa only [croppedRows,cap.croppedSupport_eq hl hz] using
    P.retainedRows_support_ae_positive_origin (fun _ : Fin 1=>cap) {l,z,cap.left,cap.right}
      as mesh ho he hm hm0 hlim hl0 hz1

theorem croppedRows_binary_columns_positive_origin {l z : ℝ} (hl0 : Q.data.rmin≤l) (hz1 : z≤1)
    (hl : cap.left≤l) (hz : z≤cap.right)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hm : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) :
    (∀ᵐr∂volume.restrict (Ioo l z),Tendsto (fun j=>Q.shiftedNativeModel.unitColumn
      (as j) (cap.croppedRows l z (as j)) (fun _=>(0:Fin 1)) (fun _=>1) r) atTop
        (𝓝 ((Ioo l z).indicator (fun _=>1) r))) ∧
    Tendsto (fun j=>∫r in Ioo l z,|Q.shiftedNativeModel.unitColumn (as j)
      (cap.croppedRows l z (as j)) (fun _=>(0:Fin 1)) (fun _=>1) r-
        (Ioo l z).indicator (fun _=>1) r|) atTop (𝓝 0) := by
  apply Q.shiftedNativeModel.binary_column_L1_of_support_eventually as ho (fun _=>1)
    (fun j=>cap.croppedRows l z (as j)) (fun _ _=>(0:Fin 1))
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).1) (Ioo l z)
  exact ae_restrict_of_ae_restrict_of_subset
    (Ioo_subset_Ioo (Q.data.hrbounds.1.le.trans hl0) hz1) (cap.croppedRows_support_ae_positive_origin hl0 hz1 hl hz as mesh ho he hm hm0 hlim)

theorem croppedRows_mass_tendsto_positive_origin {l z : ℝ} (hl0 : Q.data.rmin≤l) (hz1 : z≤1)
    (hl : cap.left≤l) (hz : z≤cap.right)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hm : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun j=>physicalWindowMass (sampleClockSteps Q.shiftedNativeModel.q 0 (as j)) 0
      (cap.croppedRows l z (as j))) atTop (𝓝 (∫r in Ioo l z,deriv Q.alpha.val.val r)) := by
  apply Q.shiftedNativeModel.binary_mass_tendsto_of_support_eventually_positive_origin as ho he
    (fun j=>cap.croppedRows l z (as j))
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).1)
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).2.2.1)
    hl0 hz1
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).2.2.2.1)
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).2.2.2.2.1)
    (Ioo l z) measurableSet_Ioo (Subset.refl _)
  exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo (Q.data.hrbounds.1.le.trans hl0) hz1)
    (cap.croppedRows_support_ae_positive_origin hl0 hz1 hl hz as mesh ho he hm hm0 hlim)

theorem croppedRows_original_mass_L1_positive_origin {l z : ℝ} (hl0 : Q.data.rmin≤l) (hz1 : z≤1)
    (hl : cap.left≤l) (hz : z≤cap.right)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hm : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun j=>∫u in 0..1,|nativeSelectedMassMask Q.shiftedNativeModel.q (as j)
      (cap.croppedRows l z (as j)) u-(Ioo l z).indicator (fun _=>1)
        (Q.shiftedNativeModel.R u)|) atTop (𝓝 0) := by
  apply Q.shiftedNativeModel.binary_mass_L1_of_support_eventually_positive_origin as ho he
    (fun j=>cap.croppedRows l z (as j))
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).1)
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).2.2.1)
    hl0 hz1
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).2.2.2.1)
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).2.2.2.2.1)
    (Ioo l z) measurableSet_Ioo (Subset.refl _)
  exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo (Q.data.hrbounds.1.le.trans hl0) hz1)
    (cap.croppedRows_support_ae_positive_origin hl0 hz1 hl hz as mesh ho he hm hm0 hlim)

theorem croppedRows_original_defect_tendsto_positive_origin {l z : ℝ} (hl0 : Q.data.rmin≤l) (hz1 : z≤1)
    (hl : cap.left≤l) (hz : z≤cap.right)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hm : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun j=>Q.shiftedNativeModel.selectedDefect (as j) (cap.croppedRows l z (as j))) atTop
      (𝓝 (∫r in Ioo l z,deriv Q.alpha.val.val r*Q.shiftedNativeModel.thermal
        (Q.alpha.val.val r))) := by
  apply Q.shiftedNativeModel.selectedDefect_tendsto_radius_positive_origin as mesh ho he hm hlim
    (fun j=>cap.croppedRows l z (as j))
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).1)
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).2.2.1)
    hl0 hz1
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).2.2.2.1)
    (fun j i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).2.2.2.2.1)
    (Ioo l z) measurableSet_Ioo (Subset.refl _)
  exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo (Q.data.hrbounds.1.le.trans hl0) hz1)
    (cap.croppedRows_support_ae_positive_origin hl0 hz1 hl hz as mesh ho he hm hm0 hlim)

end ActualThetaZeroOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
