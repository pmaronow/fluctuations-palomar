module

public import ComparisonActualHighWallCriticalBroadSliceSampler
public import ComparisonActualHighOnlyBroadSideColumns
public import ComparisonNativeBroadSliceColumns

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
attribute [local instance] Classical.propDecidable

namespace ActualHighWallOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (cap : ShiftedCapInterval a P)
theorem croppedRows_side_coefficient_tendsto {l z : ℝ} (hl0 : a.data.rmin<l) (hz1 : z≤1)
    (hl : cap.left≤l) (hz : z≤cap.right)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {cut : ℝ} (hcut : 0<cut) (hw : 2*cut≤∫r in Ioo l z,deriv a.alpha.val.val r)
    (hwidths : ∀j,2*cut≤physicalWindowMass (sampleClockSteps a.shiftedNativeModel.q 0 (as j)) 0
      (cap.croppedRows l z (as j))) :
    let widths := fun j=>physicalWindowMass (sampleClockSteps a.shiftedNativeModel.q 0 (as j)) 0
      (cap.croppedRows l z (as j))
    let width := ∫r in Ioo l z,deriv a.alpha.val.val r
    Tendsto (fun j=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) 0) atTop
      (𝓝 (sideSquareColumn (nativeBroadPoints width) cut width 0)) := by
  dsimp only
  let widths := fun j=>physicalWindowMass (sampleClockSteps a.shiftedNativeModel.q 0 (as j)) 0
    (cap.croppedRows l z (as j))
  let width := ∫r in Ioo l z,deriv a.alpha.val.val r
  have hpositive j : 0<widths j := by linarith [hwidths j]
  have hpositiveLimit : 0<width := by linarith [hw]
  have hwidthMax j : widths j≤1 := (physicalWindowMass_mem_Icc_one _
    (sampleClockSteps_ordered a.shiftedNativeModel.q (as j) (ho j)) _).2
  have ht := sideSquareColumnLR_tendsto hcut hw hpositiveLimit widths (fun _=>0) widths
    hwidths hwidthMax hpositive
    (cap.croppedRows_mass_tendsto hl0 hz1 hl hz as mesh ho he hmesh hm0 hlim)
    tendsto_const_nhds
    (cap.croppedRows_mass_tendsto hl0 hz1 hl hz as mesh ho he hmesh hm0 hlim)
  have heq j := sideSquareColumn_eq_LR (nativeBroadPoints (widths j)) 0 hcut (hwidths j)
    (by simpa [nativeBroadPoints] using hpositive j)
  have heqLimit := sideSquareColumn_eq_LR (nativeBroadPoints width) 0 hcut hw
    (by simpa [nativeBroadPoints] using hpositiveLimit)
  change Tendsto (fun j=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) 0)
    atTop (𝓝 (sideSquareColumn (nativeBroadPoints width) cut width 0))
  have hpoint j : sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) 0=
      sideSquareColumnLR cut (widths j) 0 (widths j) := by
    simpa only [nativeBroadPoints,ite_true,show (1:ℕ)≠0 by omega,ite_false] using heq j
  have hpointLimit : sideSquareColumn (nativeBroadPoints width) cut width 0=
      sideSquareColumnLR cut width 0 width := by
    simpa only [nativeBroadPoints,ite_true,show (1:ℕ)≠0 by omega,ite_false] using heqLimit
  rw [hpointLimit]
  exact ht.congr' (Eventually.of_forall (fun j=>(hpoint j).symm))

theorem croppedRows_side_L1 {l z : ℝ} (hl0 : a.data.rmin<l) (hz1 : z≤1)
    (hl : cap.left≤l) (hz : z≤cap.right)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {cut ag zg : ℝ} (hag : a.data.rmin≤ag) (hzg : zg≤1) (hcut : 0<cut)
    (hw : 2*cut≤∫r in Ioo l z,deriv a.alpha.val.val r)
    (hwidths : ∀j,2*cut≤physicalWindowMass (sampleClockSteps a.shiftedNativeModel.q 0 (as j)) 0
      (cap.croppedRows l z (as j))) :
    let J := fun j=>cap.croppedRows l z (as j)
    let widths := fun j=>physicalWindowMass (sampleClockSteps a.shiftedNativeModel.q 0 (as j)) 0 (J j)
    let width := ∫r in Ioo l z,deriv a.alpha.val.val r
    Tendsto (fun j=>∫r in Ioo ag zg,
      |a.shiftedNativeModel.unitColumn (as j) (J j)
        (fun _=>(0:Fin 1))
        (fun u=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) u.val) r-
      (Ioo l z).indicator (fun _=>sideSquareColumn (nativeBroadPoints width) cut width 0) r|)
      atTop (𝓝 0) := by
  dsimp only
  let J := fun j=>cap.croppedRows l z (as j)
  let widths := fun j=>physicalWindowMass (sampleClockSteps a.shiftedNativeModel.q 0 (as j)) 0 (J j)
  let width := ∫r in Ioo l z,deriv a.alpha.val.val r
  let coeff := fun j=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) 0
  let coeffLimit := sideSquareColumn (nativeBroadPoints width) cut width 0
  have hcoeff := cap.croppedRows_side_coefficient_tendsto hl0 hz1 hl hz as mesh ho he hmesh hm0 hlim hcut hw hwidths
  have hmask := ae_restrict_of_ae_restrict_of_subset
    (Ioo_subset_Ioo (a.data.hrbounds.1.le.trans hag) hzg)
    (cap.croppedRows_support_ae hl0 hz1 hl hz as mesh ho he hmesh hm0 hlim)
  apply bounded_contact_weights_tendsto_L1 (B:=2/cut) (Ioo ag zg) (by simp)
  · intro j
    exact (a.shiftedNativeModel.unitColumn_measurable (as j) _ _ _).aestronglyMeasurable.restrict
  · intro j
    apply ae_of_all
    intro r
    have hp : 0<widths j := by linarith [hwidths j]
    have hh := a.shiftedNativeModel.unitColumn_side_bound (cut:=cut) (width:=widths j) (as j) (ho j)
      (J j) (fun _=>(0:Fin 1)) (nativeBroadPoints (widths j))
      (by simp [nativeBroadPoints]) (by simp [nativeBroadPoints]) hcut (hwidths j)
      (fun u=>by
        have hu : u.val=0 := by omega
        simpa [hu,nativeBroadPoints] using hp) r
    have hn : ‖a.shiftedNativeModel.unitColumn (as j) (J j)
        (fun _=>(0:Fin 1))
        (fun u=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) u.val) r‖≤2/cut := by
      simpa only [Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2
    exact hn
  · filter_upwards [hmask] with r hr
    have hmt : Tendsto (fun j=>a.shiftedNativeModel.unitColumn (as j)
      (J j) (fun _=>(0:Fin 1)) (fun _=>1) r) atTop (𝓝 ((Ioo l z).indicator (fun _=>1) r)) :=
      tendsto_nhds_of_eventually_eq (by
        filter_upwards [hr] with j hj
        rw [a.shiftedNativeModel.unitColumn_binary_eq_support (as j) (ho j) (J j)
          (fun _=>(0:Fin 1)) (fun i hi=>(cap.croppedRows_data hl hz (as j) (ho j) i hi).1)]
        simp only [J,Set.indicator_apply,hj])
    have ht := hcoeff.mul hmt
    have heq j : a.shiftedNativeModel.unitColumn (as j) (J j)
        (fun _=>(0:Fin 1))
        (fun u=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) u.val) r=
        coeff j*a.shiftedNativeModel.unitColumn (as j) (J j)
          (fun _=>(0:Fin 1)) (fun _=>1) r := by
      have hfn : (fun u:Fin 1=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) u.val)=
          fun _=>coeff j := by funext u;rw [Fin.eq_zero u];rfl
      rw [hfn]
      exact a.shiftedNativeModel.unitColumn_fin_one (as j) (J j) _ r
    have hfixed : (Ioo l z).indicator (fun _=>coeffLimit) r=
        coeffLimit*(Ioo l z).indicator (fun _=>1) r := by
      by_cases hs:r∈Ioo l z <;> simp [hs]
    change Tendsto (fun j=>a.shiftedNativeModel.unitColumn (as j) (J j)
      (fun _=>(0:Fin 1))
      (fun u=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) u.val) r)
      atTop (𝓝 ((Ioo l z).indicator (fun _=>coeffLimit) r))
    simp only [heq,hfixed]
    exact ht

end ActualHighWallOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
