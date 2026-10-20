module

public import ComparisonNativeBroadSliceSampler

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3800000
attribute [local instance] Classical.propDecidable

theorem radiusCellEnergyDensity_const_mul (R : ℝ→ℝ) {u : ℝ}
    (as : List PositiveMass) (C : ℕ→ℝ) (v r : ℝ) :
    radiusCellEnergyDensity R u as (fun i=>v*C i) r=v*radiusCellEnergyDensity R u as C r := by
  induction as generalizing u C with
  | nil=>simp [radiusCellEnergyDensity]
  | cons a as ih=>
    simp only [radiusCellEnergyDensity,ih,Set.indicator_apply]
    split_ifs <;> ring

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparisonNativeUnitColumnWeight_fin_one {ι : Type} (q : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1))) (v r : ℝ) :
    comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J (fun _=>(0:Fin 1)) (fun _=>v) r=
      v*comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J (fun _=>(0:Fin 1)) (fun _=>1) r := by
  unfold comparisonNativeUnitColumnWeight
  rw [←radiusCellEnergyDensity_const_mul]
  congr 1
  funext i
  unfold nativeSelectedColumn
  split_ifs <;> simp

theorem comparisonNativeSliceColumn_support {ι : Type} (q : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass) (a b v : ℝ)
    {r : ℝ} (hr : r∉Ioc a b) :
    comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as
      (comparisonNativeSliceRows hc hk hkc hm hM q α as a b)
      (fun _=>(0:Fin 1)) (fun _=>v) r=0 := by
  rw [comparisonNativeUnitColumnWeight,radiusCellEnergyDensity_eq_finite_sum]
  unfold finiteRadiusCellDensity
  apply Finset.sum_eq_zero
  intro i hi
  have hil := Finset.mem_range.mp hi
  let ii : Fin ((sampleClockSteps q 0 as).length+1) :=
    ⟨i,by simpa only [sampleClockSteps_length] using Nat.lt_succ_of_lt hil⟩
  have he : nativeSelectedColumn
      (comparisonNativeSliceRows hc hk hkc hm hM q α as a b)
      (fun _=>(0:Fin 1)) (fun _=>v) i=
      if ii∈comparisonNativeSliceRows hc hk hkc hm hM q α as a b then v else 0 :=
    nativeSelectedColumn_atIndex _ _ _ ii
  rw [he]
  by_cases hs:ii∈comparisonNativeSliceRows hc hk hkc hm hM q α as a b
  · have hgeom := (comparisonNativeSliceRows_mem hc hk hkc hm hM q α as a b ii).mp hs
    have hno : r∉Ioc
        (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i))
        (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as (i+1))) := by
      intro hri
      exact hr ⟨hgeom.2.1.1.trans hri.1,hri.2.trans hgeom.2.2⟩
    exact indicator_of_notMem hno _
  · simp only [hs,ite_false,indicator_zero]

theorem comparisonNativeSliceColumn_group_support {ι : Type} (q : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass) (a b v ag zg : ℝ)
    (ha : ag≤a) (hb : b≤zg) :
    ∀ᵐ r,r∉Ioo ag zg→comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as
      (comparisonNativeSliceRows hc hk hkc hm hM q α as a b)
      (fun _=>(0:Fin 1)) (fun _=>v) r=0 := by
  filter_upwards [volume.ae_ne zg] with r hr hn
  apply comparisonNativeSliceColumn_support hc hk hkc hm hM q α as a b v
  intro hri
  apply hn
  exact ⟨ha.trans_lt hri.1,lt_of_le_of_ne (hri.2.trans hb) hr⟩

theorem comparisonNativeSlice_side_coefficient_tendsto {ι : Type} (q : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0))
    {a b cut : ℝ} (ha : 0≤a) (hb : b≤1) (hcut : 0<cut)
    (hw : 2*cut≤∫r in Ioo a b,deriv α.val.val r)
    (hwidths : ∀j,2*cut≤physicalWindowMass (sampleClockSteps q 0 (as j)) 0
      (comparisonNativeSliceRows hc hk hkc hm hM q α (as j) a b)) :
    let widths := fun j=>physicalWindowMass (sampleClockSteps q 0 (as j)) 0
      (comparisonNativeSliceRows hc hk hkc hm hM q α (as j) a b)
    let width := ∫r in Ioo a b,deriv α.val.val r
    Tendsto (fun j=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) 0) atTop
      (𝓝 (sideSquareColumn (nativeBroadPoints width) cut width 0)) := by
  dsimp only
  let widths := fun j=>physicalWindowMass (sampleClockSteps q 0 (as j)) 0
    (comparisonNativeSliceRows hc hk hkc hm hM q α (as j) a b)
  let width := ∫r in Ioo a b,deriv α.val.val r
  have hpositive j : 0<widths j := by linarith [hwidths j]
  have hpositiveLimit : 0<width := by linarith [hw]
  have hwidthMax j : widths j≤1 := (physicalWindowMass_mem_Icc_one _
    (sampleClockSteps_ordered q (as j) (ho j)) _).2
  have ht := sideSquareColumnLR_tendsto hcut hw hpositiveLimit widths (fun _=>0) widths
    hwidths hwidthMax hpositive
    (comparisonNativeSliceRows_mass_tendsto hc hk hkc hm hM q α as mesh ho he hmesh hlim ha hb)
    tendsto_const_nhds
    (comparisonNativeSliceRows_mass_tendsto hc hk hkc hm hM q α as mesh ho he hmesh hlim ha hb)
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

theorem comparisonNativeSlice_side_L1 {ι : Type} (q : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0))
    {a b cut ag zg : ℝ} (ha : 0≤a) (hb : b≤1) (hag : 0≤ag) (hzg : zg≤1) (hcut : 0<cut)
    (hw : 2*cut≤∫r in Ioo a b,deriv α.val.val r)
    (hwidths : ∀j,2*cut≤physicalWindowMass (sampleClockSteps q 0 (as j)) 0
      (comparisonNativeSliceRows hc hk hkc hm hM q α (as j) a b)) :
    let J := fun j=>comparisonNativeSliceRows hc hk hkc hm hM q α (as j) a b
    let widths := fun j=>physicalWindowMass (sampleClockSteps q 0 (as j)) 0 (J j)
    let width := ∫r in Ioo a b,deriv α.val.val r
    Tendsto (fun j=>∫r in Ioo ag zg,
      |comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j) (J j)
        (fun _=>(0:Fin 1))
        (fun u=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) u.val) r-
      (Ioo a b).indicator (fun _=>sideSquareColumn (nativeBroadPoints width) cut width 0) r|)
      atTop (𝓝 0) := by
  dsimp only
  let J := fun j=>comparisonNativeSliceRows hc hk hkc hm hM q α (as j) a b
  let widths := fun j=>physicalWindowMass (sampleClockSteps q 0 (as j)) 0 (J j)
  let width := ∫r in Ioo a b,deriv α.val.val r
  let coeff := fun j=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) 0
  let coeffLimit := sideSquareColumn (nativeBroadPoints width) cut width 0
  have hcoeff := comparisonNativeSlice_side_coefficient_tendsto hc hk hkc hm hM q α as mesh
    ho he hmesh hlim ha hb hcut hw hwidths
  have hmask := ae_restrict_of_ae_restrict_of_subset
    (Ioo_subset_Ioo hag hzg)
    (comparisonNativeSliceRows_mask_ae hc hk hkc hm hM q α as mesh ho he hmesh hlim a b)
  apply bounded_contact_weights_tendsto_L1 (B:=2/cut) (Ioo ag zg) (by simp)
  · intro j
    exact (comparisonNativeUnitColumnWeight_measurable hc hk hkc hm hM q α (as j) _ _ _).aestronglyMeasurable.restrict
  · intro j
    apply ae_of_all
    intro r
    have hp : 0<widths j := by linarith [hwidths j]
    have hh := comparisonNativeUnitColumnWeight_side_bound (δ:=cut) (width:=widths j) hc hk hkc hm hM q α (as j) (ho j)
      (J j) (fun _=>(0:Fin 1)) (nativeBroadPoints (widths j))
      (by simp [nativeBroadPoints]) (by simp [nativeBroadPoints]) hcut (hwidths j)
      (fun u=>by
        have hu : u.val=0 := by omega
        simpa [hu,nativeBroadPoints] using hp) r
    have hn : ‖comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j) (J j)
        (fun _=>(0:Fin 1))
        (fun u=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) u.val) r‖≤2/cut := by
      simpa only [Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2
    exact hn
  · filter_upwards [hmask] with r hr
    have hmt : Tendsto (fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
      (J j) (fun _=>(0:Fin 1)) (fun _=>1) r) atTop (𝓝 ((Ioo a b).indicator (fun _=>1) r)) :=
      tendsto_const_nhds.congr' (hr.mono (fun j hj=>hj.symm))
    have ht := hcoeff.mul hmt
    have heq j : comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j) (J j)
        (fun _=>(0:Fin 1))
        (fun u=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) u.val) r=
        coeff j*comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j) (J j)
          (fun _=>(0:Fin 1)) (fun _=>1) r := by
      have hfn : (fun u:Fin 1=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) u.val)=
          fun _=>coeff j := by funext u;rw [Fin.eq_zero u];rfl
      rw [hfn]
      exact comparisonNativeUnitColumnWeight_fin_one hc hk hkc hm hM q α (as j) (J j) _ r
    have hfixed : (Ioo a b).indicator (fun _=>coeffLimit) r=
        coeffLimit*(Ioo a b).indicator (fun _=>1) r := by
      by_cases hs:r∈Ioo a b <;> simp [hs]
    change Tendsto (fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j) (J j)
      (fun _=>(0:Fin 1))
      (fun u=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) u.val) r)
      atTop (𝓝 ((Ioo a b).indicator (fun _=>coeffLimit) r))
    simp only [heq,hfixed]
    exact ht

theorem comparisonNativeSlice_mask_group_L1 {ι : Type} (q : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0))
    (a b ag zg : ℝ) (hag : 0≤ag) (hzg : zg≤1) :
    Tendsto (fun j=>∫r in Ioo ag zg,
      |comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
        (comparisonNativeSliceRows hc hk hkc hm hM q α (as j) a b)
        (fun _=>(0:Fin 1)) (fun _=>1) r-(Ioo a b).indicator (fun _=>1) r|) atTop (𝓝 0) := by
  apply bounded_contact_weights_tendsto_L1 (B:=1) (Ioo ag zg) (by simp)
  · intro j
    exact (comparisonNativeUnitColumnWeight_measurable hc hk hkc hm hM q α (as j) _ _ _).aestronglyMeasurable.restrict
  · intro j
    apply ae_of_all
    intro r
    have hh := radiusCellEnergyDensity_mem_Icc _
      (comparisonSweepQuantile_monotone hc hk hkc hm hM α) (as j) (ho j)
      (nativeSelectedColumn (comparisonNativeSliceRows hc hk hkc hm hM q α (as j) a b)
        (fun _=>(0:Fin 1)) (fun _=>(1:ℝ)))
      (fun i=>by unfold nativeSelectedColumn;split_ifs <;> norm_num) r
    simpa only [comparisonNativeUnitColumnWeight,Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2
  · have hmask := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo hag hzg)
      (comparisonNativeSliceRows_mask_ae hc hk hkc hm hM q α as mesh ho he hmesh hlim a b)
    filter_upwards [hmask] with r hr
    exact tendsto_const_nhds.congr' (hr.mono (fun j hj=>hj.symm))

end
end OAI.SKFluctuations.LaplaceWindowFormalization
