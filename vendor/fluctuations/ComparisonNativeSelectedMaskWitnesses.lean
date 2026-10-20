module

public import ComparisonNativeSelectedMaskGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2400000
attribute [local instance] Classical.propDecidable

namespace NativeSelectedMask

theorem finite_cap_labels_subsequence {τ : Type*} [Fintype τ] {bins : ℕ}
    (labels : ℕ → τ → Fin bins) :
    ∃b : τ → Fin bins,∃φ : ℕ → ℕ,StrictMono φ ∧ ∀ᶠ j in atTop,labels (φ j)=b := by
  obtain ⟨b,φ,hφ,ht⟩ := CompactSpace.tendsto_subseq labels
  refine ⟨b,φ,hφ,?_⟩
  have he := ht.eventually ((isOpen_discrete {b}).mem_nhds (by simp))
  exact he.mono (fun _ hj=>Set.mem_singleton_iff.mp hj)

theorem contact_cells_eventually_outside_retained {τ : Type*} [Fintype τ]
    (a z : τ → ℝ) (H : ℝ → ℝ)
    (hneg : ∀t,∀s∈Ioo (a t) (z t),H s<0)
    (p : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (mesh : ℕ → ℝ)
    (hmesh : ∀j i,i<N j → p j (i+1)-p j i ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {r : ℝ} (hHr : H r=0) (hra : ∀t,r≠a t) (hrz : ∀t,r≠z t) :
    ∀ᶠ j in atTop,∀i<N j,r ∈ Ioc (p j i) (p j (i+1)) →
      ∀t,p j i ∉ Ioo (a t) (z t) := by
  let G := (⋃t,Icc (a t) (z t))ᶜ
  have hG : IsOpen G := (isClosed_iUnion_of_finite (fun _=>isClosed_Icc)).isOpen_compl
  have hrG : r∈G := by
    intro hh
    obtain ⟨t,ht⟩ := mem_iUnion.mp hh
    have hi : r∈Ioo (a t) (z t) :=
      ⟨lt_of_le_of_ne ht.1 (hra t).symm,lt_of_le_of_ne ht.2 (hrz t)⟩
    have hh := hneg t r hi
    rw [hHr] at hh
    exact lt_irrefl _ hh
  filter_upwards [cells_eventually_subset_open p N mesh hmesh hlim G hG hrG] with j hj
  intro i hi hri t ht
  have hlo : p j i ∈ Icc (p j i) (p j (i+1)) := ⟨le_rfl,hri.1.le.trans hri.2⟩
  exact hj i hi hri hlo (mem_iUnion.mpr ⟨t,ht.1.le,ht.2.le⟩)

theorem same_unit_row_meets_contact {τ : Type*}
    (a z : τ → ℝ) (H : ℝ → ℝ) (U : Set ℝ) (p : ℕ → ℝ) (D : Finset ℝ)
    (hcaps : ∀t,∀r∈Ioo (a t) (z t),wholeUnit U r=Ioo (a t) (z t))
    {i j : ℕ} (hsel : rowSelected a z H id p D j)
    (hi : ∀t,p i ∉ Ioo (a t) (z t))
    (he : wholeUnit U (p j)=wholeUnit U (p i)) :
    ∃r∈Icc (p j) (p (j+1)),H r=0 := by
  rcases hsel.2 with ⟨t,ht,_⟩ | hh
  · have hp : p i ∈ wholeUnit U (p j) := he.symm ▸ self_mem_wholeUnit U (p i)
    rw [hcaps t (p j) ht] at hp
    exact False.elim (hi t hp)
  · exact hh

end NativeSelectedMask

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparisonNativeMask_eq_finiteSupport {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps q 0 as).length+1) → Fin K)
    (hJ : ∀i∈J,i.val<as.length) {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) :
    comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J unit (fun _=>1) r=
      (NativeSelectedMask.finiteSupport
        (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i)) J).indicator
          (fun _=>1) r := by
  by_cases hs : r∈NativeSelectedMask.finiteSupport
      (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i)) J
  · obtain ⟨i,hi,hri⟩ := hs
    rw [comparisonNativeMask_on_cell hc hk hkc hm hM q α as ho J unit i (hJ i hi) hri,
      ite_eq_left hi,indicator_of_mem (show r∈NativeSelectedMask.finiteSupport
        (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i)) J from ⟨i,hi,hri⟩)]
  · obtain ⟨i,hi,_,hri⟩ := comparison_contactMeetingCells_cover hc hk hkc hm hM α
      (fun _=>0) as he ⟨hr.1,hr.2.le⟩ rfl
    let ii : Fin ((sampleClockSteps q 0 as).length+1) :=
      ⟨i,by simpa only [sampleClockSteps_length] using Nat.lt_succ_of_lt hi⟩
    have hn : ii∉J := fun hii=>hs ⟨ii,hii,hri⟩
    rw [comparisonNativeMask_on_cell hc hk hkc hm hM q α as ho J unit ii hi hri,
      ite_eq_right hn,indicator_of_notMem hs]

theorem comparisonNativeMask_tendsto_of_support_eventually {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1) (K : ℕ → ℕ)
    (J : ∀j,Finset (Fin ((sampleClockSteps q 0 (as j)).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps q 0 (as j)).length+1) → Fin (K j))
    (hJ : ∀j,∀i∈J j,i.val<(as j).length) (F : Set ℝ)
    (hmem : ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
      (r∈NativeSelectedMask.finiteSupport
        (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)) (J j) ↔ r∈F)) :
    (∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),Tendsto
      (fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j) (J j) (unit j)
        (fun _=>1) r) atTop (𝓝 (F.indicator (fun _=>1) r))) ∧
    Tendsto (fun j=>∫r in Ioo (0:ℝ) 1,
      |comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j) (J j) (unit j)
        (fun _=>1) r-F.indicator (fun _=>1) r|) atTop (𝓝 0) := by
  have hpoint : ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),Tendsto
      (fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j) (J j) (unit j)
        (fun _=>1) r) atTop (𝓝 (F.indicator (fun _=>1) r)) := by
    filter_upwards [hmem,ae_restrict_mem measurableSet_Ioo] with r hr hr01
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [hr] with j hj
    rw [comparisonNativeMask_eq_finiteSupport hc hk hkc hm hM q α (as j) (ho j) (he j)
      (J j) (unit j) (hJ j) hr01]
    simp only [Set.indicator_apply,hj]
  refine ⟨hpoint,?_⟩
  apply bounded_contact_weights_tendsto_L1 (B:=1) (Ioo (0:ℝ) 1) (by simp)
    _ _ (fun j=>(comparisonNativeUnitColumnWeight_measurable hc hk hkc hm hM q α
      (as j) (J j) (unit j) _).aestronglyMeasurable.restrict) _ hpoint
  intro j
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  rw [comparisonNativeMask_eq_finiteSupport hc hk hkc hm hM q α (as j) (ho j) (he j)
    (J j) (unit j) (hJ j) hr]
  simp only [Set.indicator_apply]
  split_ifs <;> norm_num

theorem comparisonNativeSelectedRows_contact_witness_eventually {ι : Type} {τ : Type*}
    [Fintype τ]
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hlim : Tendsto mesh atTop (𝓝 0))
    (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ) (U : Set ℝ)
    (hneg : ∀t,∀s∈Ioo (a t) (z t),H s<0)
    (hcaps : ∀t,∀r∈Ioo (a t) (z t),wholeUnit U r=Ioo (a t) (z t))
    (K : ℕ → ℕ)
    (J : ∀j,Finset (Fin ((sampleClockSteps q 0 (as j)).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps q 0 (as j)).length+1) → Fin (K j))
    (hJ : ∀j,J j⊆comparisonNativeSelectedRows hc hk hkc hm hM q α (as j) a z H D)
    (hclass : ∀m,∀i∈J m,∀j∈J m,unit m i=unit m j →
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α
        (physicalCutMass 0 (sampleClockSteps q 0 (as m)) i.val))=
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α
        (physicalCutMass 0 (sampleClockSteps q 0 (as m)) j.val)))
    {r : ℝ} (hHr : H r=0) (hra : ∀t,r≠a t) (hrz : ∀t,r≠z t)
    (hcell : ∀ᶠ j in atTop,∃i : Fin ((sampleClockSteps q 0 (as j)).length+1),
      i∈J j ∧ i.val<(as j).length ∧
      r∈Ioc (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i.val))
        (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) (i.val+1)))) :
    ∀ᶠ j in atTop,comparisonNativeContactCellWitness hc hk hkc hm hM q α
      (as j) (J j) (unit j) H U r := by
  let p := fun j i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)
  obtain ⟨_,_,_,hdiam,ht⟩ := comparisonNativeSelectedRows_grid hc hk hkc hm hM α
    as mesh ho he hmesh hlim
  filter_upwards [hcell,NativeSelectedMask.contact_cells_eventually_outside_retained
    a z H hneg p _ _ hdiam ht hHr hra hrz] with m hcell hout
  obtain ⟨i,hi,hil,hri⟩ := hcell
  refine ⟨i,hi,hil,hri,?_⟩
  intro _ j hj hji
  have hjglobal := (comparisonNativeSelectedRows_mem hc hk hkc hm hM q α (as m) a z H D j).mp
    (hJ m hj)
  have hie := physicalCutMass_sampleClockSteps q 0 (as m) i.val hil.le
  have hje := physicalCutMass_sampleClockSteps q 0 (as m) j.val hjglobal.1.le
  have hjnext := physicalCutMass_sampleClockSteps q 0 (as m) (j.val+1) (by omega)
  have heq := hclass m j hj i hi hji
  rw [hie,hje] at heq
  have hh := NativeSelectedMask.same_unit_row_meets_contact a z H U (p m) D hcaps
    hjglobal.2 (hout i.val hil hri) heq
  simpa only [hje,hjnext,sub_zero] using hh

theorem comparisonNativeSelectedRows_cap_bin_cell_eventually {ι : Type} {τ : Type*}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hlim : Tendsto mesh atTop (𝓝 0))
    (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ)
    (K : ℕ → ℕ)
    (unit : ∀j,Fin ((sampleClockSteps q 0 (as j)).length+1) → Fin (K j))
    (capUnit : ∀j,τ → Fin (K j))
    (hcapclass : ∀j,∀i∈comparisonNativeSelectedRows hc hk hkc hm hM q α (as j) a z H D,
      ∀t,comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i.val)∈Ioo (a t) (z t) →
        unit j i=capUnit j t)
    (S : ∀j,Fin ((sampleClockSteps q 0 (as j)).length+1) → ℝ)
    (bins : ℕ) (w : ℕ → ℝ) (b : Fin bins) (t : τ)
    (hlabel : ∀ᶠ j in atTop,heightBin bins (w j)
      (NativeUnitHeight.height (S j)
        (comparisonNativeSelectedRows hc hk hkc hm hM q α (as j) a z H D) (unit j) (capUnit j t))=b.val)
    {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) (hrD : r∉D) (hrt : r∈Ioo (a t) (z t)) :
    ∀ᶠ j in atTop,∃i : Fin ((sampleClockSteps q 0 (as j)).length+1),
      i∈NativeUnitHeight.bin (S j)
        (comparisonNativeSelectedRows hc hk hkc hm hM q α (as j) a z H D)
        (unit j) bins (w j) b ∧ i.val<(as j).length ∧ unit j i=capUnit j t ∧
      r∈Ioc (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i.val))
        (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) (i.val+1))) := by
  let p := fun j i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)
  obtain ⟨_,_,_,hdiam,ht⟩ := comparisonNativeSelectedRows_grid hc hk hkc hm hM α
    as mesh ho he hmesh hlim
  have hcell := comparisonNativeSelectedRows_cell_eventually hc hk hkc hm hM q α
    as mesh ho he hmesh hlim a z H D hr hrD (Or.inl ⟨t,hrt⟩)
  have hincap := NativeSelectedMask.cells_eventually_subset_open p (fun j=>(as j).length)
    (fun j=>mesh j/c) hdiam ht (Ioo (a t) (z t)) isOpen_Ioo hrt
  filter_upwards [hcell,hincap,hlabel] with j hj hcap hl
  obtain ⟨i,hi,hil,hri⟩ := hj
  have hleft : p j i.val∈Ioo (a t) (z t) :=
    hcap i.val hil hri (left_mem_Icc.mpr (hri.1.le.trans hri.2))
  have hui := hcapclass j i hi t hleft
  refine ⟨i,?_,hil,hui,hri⟩
  apply Finset.mem_filter.mpr
  exact ⟨hi,by rw [hui]; exact hl⟩

theorem comparisonNativeSelectedRows_contact_witness_ae {ι : Type} {τ : Type*}
    [Fintype τ]
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hlim : Tendsto mesh atTop (𝓝 0))
    (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ) (U : Set ℝ)
    (hneg : ∀t,∀s∈Ioo (a t) (z t),H s<0)
    (hcaps : ∀t,∀r∈Ioo (a t) (z t),wholeUnit U r=Ioo (a t) (z t))
    (K : ℕ → ℕ)
    (J : ∀j,Finset (Fin ((sampleClockSteps q 0 (as j)).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps q 0 (as j)).length+1) → Fin (K j))
    (hJ : ∀j,J j⊆comparisonNativeSelectedRows hc hk hkc hm hM q α (as j) a z H D)
    (hclass : ∀m,∀i∈J m,∀j∈J m,unit m i=unit m j →
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α
        (physicalCutMass 0 (sampleClockSteps q 0 (as m)) i.val))=
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α
        (physicalCutMass 0 (sampleClockSteps q 0 (as m)) j.val)))
    (A : Set ℝ) (hA : MeasurableSet A) (hzero : ∀r∈A,H r=0)
    (hmem : ∀ᵐ r ∂volume.restrict A,∀ᶠ j in atTop,r∈NativeSelectedMask.finiteSupport
      (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)) (J j)) :
    ∀ᵐ r ∂volume.restrict A,∀ᶠ j in atTop,
      comparisonNativeContactCellWitness hc hk hkc hm hM q α (as j) (J j) (unit j) H U r := by
  have ha : ∀ᵐ r : ℝ,∀t,r≠a t := ae_all_iff.mpr (fun t=>volume.ae_ne (a t))
  have hz : ∀ᵐ r : ℝ,∀t,r≠z t := ae_all_iff.mpr (fun t=>volume.ae_ne (z t))
  filter_upwards [hmem,ae_restrict_mem hA,ae_mono Measure.restrict_le_self ha,
    ae_mono Measure.restrict_le_self hz] with r hr hrA hra hrz
  apply comparisonNativeSelectedRows_contact_witness_eventually hc hk hkc hm hM q α
    as mesh ho he hmesh hlim a z H D U hneg hcaps K J unit hJ hclass (hzero r hrA) hra hrz
  filter_upwards [hr] with j hj
  obtain ⟨i,hi,hri⟩ := hj
  have hh := (comparisonNativeSelectedRows_mem hc hk hkc hm hM q α (as j) a z H D i).mp
    (hJ j hi)
  exact ⟨i,hi,hh.1,hri⟩

end
end OAI.SKFluctuations.LaplaceWindowFormalization
