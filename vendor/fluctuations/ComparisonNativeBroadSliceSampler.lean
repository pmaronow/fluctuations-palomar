module

public import ComparisonNativeBroadBandAssembly
public import ComparisonNativeKeptUnionMass
public import ComparisonNativeConstructedRows

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3800000
attribute [local instance] Classical.propDecidable

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

abbrev comparisonNativeSliceRows {ι : Type} (q : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass) (a b : ℝ) :=
  comparisonNativeSelectedRows hc hk hkc hm hM q α as
    (fun _ : Fin 1=>a) (fun _=>b) (fun _=>1) {a,b}

theorem comparisonNativeSliceRows_mem {ι : Type} (q : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass) (a b : ℝ)
    (i : Fin ((sampleClockSteps q 0 as).length+1)) :
    i∈comparisonNativeSliceRows hc hk hkc hm hM q α as a b ↔
      i.val<as.length ∧
      comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i.val)∈Ioo a b ∧
      comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as (i.val+1))≤b := by
  simp [comparisonNativeSliceRows,comparisonNativeSelectedRows_mem,NativeSelectedMask.rowSelected]
  intro hl h1 h2 h3
  exact ⟨ne_of_gt h1,ne_of_lt h2⟩

theorem physicalSelectedUnitMass_fin_one {ι : Type} (steps : List (GaussianStep ι))
    (J : Finset (Fin (steps.length+1))) :
    physicalSelectedUnitMass steps J (fun _=>(0:Fin 1)) 0=physicalWindowMass steps 0 J := by
  simp [physicalSelectedUnitMass,physicalWindowMass]

theorem comparisonNativeSliceRows_mask_ae {ι : Type} (q : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0))
    (a b : ℝ) :
    ∀ᵐ r∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
      comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
        (comparisonNativeSliceRows hc hk hkc hm hM q α (as j) a b)
        (fun _=>(0:Fin 1)) (fun _=>1) r=(Ioo a b).indicator (fun _=>1) r := by
  have hs : NativeSelectedMask.fixedSupport (fun _ : Fin 1=>a) (fun _=>b) (fun _=>1)=Ioo a b := by
    ext r
    simp [NativeSelectedMask.fixedSupport]
  simpa only [comparisonNativeSliceRows,hs] using
    comparisonNativeSelectedRows_mask_ae hc hk hkc hm hM q α as mesh ho he hmesh hlim
      (fun _ : Fin 1=>a) (fun _=>b) (fun _=>1) continuousOn_const {a,b}

theorem comparisonNativeSliceRows_mask_L1 {ι : Type} (q : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0))
    (a b : ℝ) :
    Tendsto (fun j=>∫r in Ioo (0:ℝ) 1,
      |comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
        (comparisonNativeSliceRows hc hk hkc hm hM q α (as j) a b)
        (fun _=>(0:Fin 1)) (fun _=>1) r-(Ioo a b).indicator (fun _=>1) r|) atTop (𝓝 0) := by
  have hs : NativeSelectedMask.fixedSupport (fun _ : Fin 1=>a) (fun _=>b) (fun _=>1)=Ioo a b := by
    ext r
    simp [NativeSelectedMask.fixedSupport]
  simpa only [comparisonNativeSliceRows,hs] using
    comparisonNativeSelectedRows_mask_L1 hc hk hkc hm hM q α as mesh ho he hmesh hlim
      (fun _ : Fin 1=>a) (fun _=>b) (fun _=>1) continuousOn_const {a,b}

theorem comparisonNativeSliceRows_mass_L1 {ι : Type} (q : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0))
    (a b : ℝ) :
    Tendsto (fun j=>∫u in Icc (0:ℝ) 1,
      |massStepFunction (as j) (nativeSelectedColumn
        (comparisonNativeSliceRows hc hk hkc hm hM q α (as j) a b)
        (fun _=>(0:Fin 1)) (fun _=>1)) u-
        (Ioo a b).indicator (fun _=>1) (comparisonSweepQuantile hc hk hkc hm hM α u)|) atTop (𝓝 0) := by
  apply comparisonNativeMask_mass_L1_tendsto_of_radius_ae hc hk hkc hm hM q α as ho he
    (fun _=>1) _ (fun _ _=>(0:Fin 1)) ((Ioo a b).indicator (fun _=>1))
  have hs := comparisonNativeSliceRows_mask_ae hc hk hkc hm hM q α as mesh ho he hmesh hlim a b
  rw [restrict_Ioo_eq_restrict_Icc] at hs
  filter_upwards [hs] with r hr
  exact tendsto_const_nhds.congr' (hr.mono (fun j hj=>hj.symm))

theorem comparisonNativeSliceRows_support_ae {ι : Type} (q : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0))
    (a b : ℝ) :
    ∀ᵐ r∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
      (r∈NativeSelectedMask.finiteSupport
        (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i))
        (comparisonNativeSliceRows hc hk hkc hm hM q α (as j) a b) ↔ r∈Ioo a b) := by
  filter_upwards [comparisonNativeSliceRows_mask_ae hc hk hkc hm hM q α as mesh ho he hmesh hlim a b,
    ae_restrict_mem measurableSet_Ioo] with r hr hr01
  filter_upwards [hr] with j hj
  rw [comparisonNativeMask_eq_finiteSupport hc hk hkc hm hM q α (as j) (ho j) (he j)
    _ _ (fun i hi=>(comparisonNativeSliceRows_mem hc hk hkc hm hM q α (as j) a b i).mp hi |>.1)
    hr01] at hj
  by_cases hs:r∈NativeSelectedMask.finiteSupport
      (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i))
      (comparisonNativeSliceRows hc hk hkc hm hM q α (as j) a b)
  all_goals by_cases ht:r∈Ioo a b <;> simp_all

theorem comparisonNativeSliceRows_mass_tendsto {ι : Type} (q : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0))
    {a b : ℝ} (ha : 0≤a) (hb : b≤1) :
    Tendsto (fun j=>physicalWindowMass (sampleClockSteps q 0 (as j)) 0
      (comparisonNativeSliceRows hc hk hkc hm hM q α (as j) a b)) atTop
      (𝓝 (∫r in Ioo a b,deriv α.val.val r)) := by
  let J := fun j=>comparisonNativeSliceRows hc hk hkc hm hM q α (as j) a b
  have ht := comparisonNativeKeptUnion_mass_tendsto hc hk hkc hm hM q α as ho he
    (fun (j : ℕ) (_ : Fin 1)=>J j)
    (fun j _ i hi=>(comparisonNativeSliceRows_mem hc hk hkc hm hM q α (as j) a b i).mp hi |>.1)
    (fun _=>1) (fun _ _=>(0:Fin 1)) (fun _=>true) (fun _=>Ioo a b)
    (fun _=>measurableSet_Ioo)
    (fun _=>comparisonNativeSliceRows_support_ae hc hk hkc hm hM q α as mesh ho he hmesh hlim a b)
  have hrows j : nativeKeptRows (fun _ : Fin 1=>J j) (fun _=>true)=J j := by
    ext i
    simp [nativeKeptRows_mem]
  have hs : nativeKeptSupport (fun _ : Fin 1=>Ioo a b) (fun _=>true)=Ioo a b := by
    ext r
    simp [nativeKeptSupport]
  simp only [hrows,hs] at ht
  rw [comparison_quantile_weighted_integral hc hk hkc hm hM α] at ht
  have heq : (∫r in Icc (0:ℝ) 1,deriv α.val.val r*(Ioo a b).indicator (fun _=>1) r)=
      ∫r in Ioo a b,deriv α.val.val r := by
    simp_rw [←Set.indicator_mul_right,mul_one]
    rw [setIntegral_indicator measurableSet_Ioo]
    rw [inter_eq_right.mpr (Ioo_subset_Icc_self.trans (Icc_subset_Icc ha hb))]
  simpa only [heq,J] using ht

theorem comparisonNativeSliceRows_positive {ι : Type} (q : ℝ→ι→ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass) (a b : ℝ)
    (hstrict : ∀i<as.length,partitionPoint 0 as i<partitionPoint 0 as (i+1)) :
    ∀i∈comparisonNativeSliceRows hc hk hkc hm hM q α as a b,
      0<pathMassDifferences (sampleClockSteps q 0 as) 0 i := by
  intro i hi
  have hil := (comparisonNativeSliceRows_mem hc hk hkc hm hM q α as a b i).mp hi |>.1
  rw [pathMassDifferences_eq_cutMass,
    physicalCutMass_sampleClockSteps q 0 as i.val (by omega),
    physicalCutMass_sampleClockSteps q 0 as (i.val+1) (by omega)]
  exact sub_pos.mpr (hstrict _ hil)

end
end OAI.SKFluctuations.LaplaceWindowFormalization
