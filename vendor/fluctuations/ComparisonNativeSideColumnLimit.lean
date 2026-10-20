module

public import ComparisonSideColumnParameterContinuity
public import ComparisonNativeContactColumnConvergence
public import ComparisonCapSideVarianceComposition

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 2400000

theorem fixedCapContactWeight_at_cap {τ : Type*} [Fintype τ] [DecidableEq τ]
    (a z weight : τ → ℝ) (A : Set ℝ) (w : ℝ → ℝ)
    (hdisjoint : Pairwise (fun i j=>Disjoint (Ioo (a i) (z i)) (Ioo (a j) (z j))))
    (hcontact : ∀i,Disjoint (Ioo (a i) (z i)) A)
    (i : τ) {r : ℝ} (hr : r ∈ Ioo (a i) (z i)) :
    fixedCapContactWeight a z weight A w r=weight i := by
  have hnA : r ∉ A := fun h=>Set.disjoint_left.mp (hcontact i) hr h
  unfold fixedCapContactWeight
  rw [indicator_of_notMem hnA,add_zero]
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hr _
  · intro j _ hji
    exact indicator_of_notMem (fun hj=>Set.disjoint_left.mp (hdisjoint hji) hj hr) _
  · simp

theorem fixedCapContactWeight_at_contact {τ : Type*} [Fintype τ]
    (a z weight : τ → ℝ) (A : Set ℝ) (w : ℝ → ℝ)
    (hcontact : ∀i,Disjoint (Ioo (a i) (z i)) A)
    {r : ℝ} (hr : r ∈ A) : fixedCapContactWeight a z weight A w r=w r := by
  have hn i : r ∉ Ioo (a i) (z i) := fun h=>Set.disjoint_left.mp (hcontact i) h hr
  simp [fixedCapContactWeight,hn,hr]

theorem fixedCapContactWeight_outside {τ : Type*} [Fintype τ]
    (a z weight : τ → ℝ) (A : Set ℝ) (w : ℝ → ℝ) {r : ℝ}
    (hr : ∀i,r ∉ Ioo (a i) (z i)) (hrA : r ∉ A) :
    fixedCapContactWeight a z weight A w r=0 := by
  simp [fixedCapContactWeight,hr,hrA]

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r ∈ Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparisonNativeUnitColumnWeight_mul_mask {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps q 0 as).length+1) → Fin K)
    (col : Fin K → ℝ) (r : ℝ) :
    comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J unit col r*
      comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J unit (fun _=>1) r=
      comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J unit col r := by
  unfold comparisonNativeUnitColumnWeight
  rw [radiusCellEnergyDensity_mul _ (comparisonSweepQuantile_monotone hc hk hkc hm hM α) as ho]
  congr 1
  funext i
  unfold nativeSelectedColumn
  split_ifs  <;> simp

theorem comparisonNativeSideColumn_tendsto_zero_of_mask {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (K : ℕ → ℕ) (J : ∀j,Finset (Fin ((sampleClockSteps q 0 (as j)).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps q 0 (as j)).length+1) → Fin (K j))
    (x : ℕ → ℕ → ℝ) (widths : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hstart : ∀j,x j 0=0) (hend : ∀j,x j (K j)=widths j)
    (hwidths : ∀j,2*δ ≤ widths j)
    (hx : ∀j,∀u : Fin (K j),x j u.val < x j (u.val+1))
    (r : ℝ) (hmask : Tendsto (fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM
      q α (as j) (J j) (unit j) (fun _=>1) r) atTop (𝓝 0)) :
    Tendsto (fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
      (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val) r)
      atTop (𝓝 0) := by
  let moving := fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
    (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val) r
  let mask := fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
    (J j) (unit j) (fun _=>1) r
  have hb j : moving j ∈ Icc (0:ℝ) (2/δ) :=
    comparisonNativeUnitColumnWeight_side_bound hc hk hkc hm hM q α (as j) (ho j)
      (J j) (unit j) (x j) (hstart j) (hend j) hδ (hwidths j) (hx j) r
  have hm0 j : 0 ≤ mask j :=
    (radiusCellEnergyDensity_mem_Icc_bound _ (comparisonSweepQuantile_monotone hc hk hkc hm hM α)
      (as j) (ho j) (nativeSelectedColumn (J j) (unit j) (fun _=>1)) zero_le_one (fun i=>by
        unfold nativeSelectedColumn
        split_ifs  <;> norm_num) r).1
  have he j : moving j*mask j=moving j :=
    comparisonNativeUnitColumnWeight_mul_mask hc hk hkc hm hM q α (as j) (ho j)
      (J j) (unit j) _ r
  have hup j : moving j ≤ (2/δ)*mask j := by
    rw [←he j]
    exact mul_le_mul_of_nonneg_right (hb j).2 (hm0 j)
  exact squeeze_zero (fun j=>(hb j).1) hup (by
    simpa only [mul_zero] using hmask.const_mul (2/δ))

theorem comparisonNativeSideColumn_cap_tendsto {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (K : ℕ → ℕ) (J : ∀j,Finset (Fin ((sampleClockSteps q 0 (as j)).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps q 0 (as j)).length+1) → Fin (K j))
    (x : ℕ → ℕ → ℝ) (widths : ℕ → ℝ) (capUnit : ∀j,Fin (K j))
    {δ width l rr : ℝ} (hδ : 0 < δ) (hw : 2*δ ≤ width) (hlr : l < rr)
    (hwidths : ∀j,2*δ ≤ widths j) (hwidthMax : ∀j,widths j ≤ 1)
    (hx : ∀j,∀u : Fin (K j),x j u.val < x j (u.val+1))
    (hwidthlim : Tendsto widths atTop (𝓝 width))
    (hleft : Tendsto (fun j=>x j (capUnit j).val) atTop (𝓝 l))
    (hright : Tendsto (fun j=>x j ((capUnit j).val+1)) atTop (𝓝 rr))
    (r : ℝ)
    (hcell : ∀ᶠ j in atTop,∃i : Fin ((sampleClockSteps q 0 (as j)).length+1),
      i ∈ J j  ∧  i.val < (as j).length  ∧  unit j i=capUnit j  ∧ 
      r ∈ Ioc (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i.val))
        (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) (i.val+1)))) :
    Tendsto (fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
      (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val) r)
      atTop (𝓝 (sideSquareColumnLR δ width l rr)) := by
  have hcol := sideSquareColumnLR_tendsto hδ hw hlr widths
    (fun j=>x j (capUnit j).val) (fun j=>x j ((capUnit j).val+1))
    hwidths hwidthMax (fun j=>hx j (capUnit j)) hwidthlim hleft hright
  apply (tendsto_congr' (f₁:=fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM
    q α (as j) (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val) r)
    (f₂:=fun j=>sideSquareColumnLR δ (widths j) (x j (capUnit j).val)
      (x j ((capUnit j).val+1))) ?_).mpr hcol
  filter_upwards [hcell] with j hj
  obtain ⟨i,hi,hil,hu,hr⟩ := hj
  unfold comparisonNativeUnitColumnWeight
  rw [radiusCellEnergyDensity_on_original_cell _
    (comparisonSweepQuantile_monotone hc hk hkc hm hM α) (as j) (ho j) _ hil hr,
    nativeSelectedColumn_atIndex,ite_eq_left hi,hu,
    sideSquareColumn_eq_LR (x j) (capUnit j).val hδ (hwidths j) (hx j (capUnit j))]

theorem comparisonNativeSideColumn_full_L1_of_geometry {ι : Type} {τ : Type*}
    [Fintype τ] [DecidableEq τ]
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (K : ℕ → ℕ) (J : ∀j,Finset (Fin ((sampleClockSteps q 0 (as j)).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps q 0 (as j)).length+1) → Fin (K j))
    (x : ℕ → ℕ → ℝ) (widths : ℕ → ℝ) (capUnit : ∀j,τ → Fin (K j))
    {δ width ag zg : ℝ} (hδ : 0 < δ) (hw : 2*δ ≤ width)
    (hag : 0 < ag) (hzg : zg ≤ 1)
    (hstart : ∀j,x j 0=0) (hend : ∀j,x j (K j)=widths j)
    (hwidths : ∀j,2*δ ≤ widths j) (hwidthMax : ∀j,widths j ≤ 1)
    (hx : ∀j,∀u : Fin (K j),x j u.val < x j (u.val+1))
    (hwidthlim : Tendsto widths atTop (𝓝 width))
    (a z l rr : τ → ℝ) (hlr : ∀i,l i < rr i)
    (hleft : ∀i,Tendsto (fun j=>x j (capUnit j i).val) atTop (𝓝 (l i)))
    (hright : ∀i,Tendsto (fun j=>x j ((capUnit j i).val+1)) atTop (𝓝 (rr i)))
    (A : Set ℝ) (w : ℝ → ℝ)
    (hdisjoint : Pairwise (fun i j=>Disjoint (Ioo (a i) (z i)) (Ioo (a j) (z j))))
    (hcontact : ∀i,Disjoint (Ioo (a i) (z i)) A)
    (hgeometry : ∀ᵐ r ∂ volume.restrict (Ioo ag zg),
      (∀t,r ∈ Ioo (a t) (z t) → ∀ᶠ j in atTop,
        ∃i : Fin ((sampleClockSteps q 0 (as j)).length+1),
          i ∈ J j  ∧  i.val < (as j).length  ∧  unit j i=capUnit j t  ∧ 
          r ∈ Ioc (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i.val))
            (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) (i.val+1))))  ∧ 
      (r ∈ A → Tendsto (fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
        (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val) r) atTop (𝓝 (w r)))  ∧ 
      ((∀t,r ∉ Ioo (a t) (z t)) → r ∉ A → Tendsto
        (fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
          (J j) (unit j) (fun _=>1) r) atTop (𝓝 0))) :
    let moving := fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
      (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val)
    let fixed := fixedCapContactWeight a z (fun i=>sideSquareColumnLR δ width (l i) (rr i)) A w
    (∀ᵐ r ∂ volume.restrict (Ioo ag zg),Tendsto (fun j=>moving j r) atTop (𝓝 (fixed r)))  ∧ 
    Tendsto (fun j=>∫r in Ioo ag zg,|moving j r-fixed r|) atTop (𝓝 0)  ∧ 
    Tendsto (fun j=>∫r in Ioo ag zg,
      |deriv α.val.val r*moving j r-deriv α.val.val r*fixed r|) atTop (𝓝 0) := by
  dsimp only
  let moving := fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
    (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val)
  let fixed := fixedCapContactWeight a z (fun i=>sideSquareColumnLR δ width (l i) (rr i)) A w
  have hpoint : ∀ᵐ r ∂ volume.restrict (Ioo ag zg),
      Tendsto (fun j=>moving j r) atTop (𝓝 (fixed r)) := by
    filter_upwards [hgeometry] with r hr
    by_cases hcap : ∃t,r ∈ Ioo (a t) (z t)
    · obtain ⟨t,ht⟩ := hcap
      rw [show fixed r=sideSquareColumnLR δ width (l t) (rr t) from
        fixedCapContactWeight_at_cap a z _ A w hdisjoint hcontact t ht]
      exact comparisonNativeSideColumn_cap_tendsto hc hk hkc hm hM q α as ho K J unit
        x widths (fun j=>capUnit j t) hδ hw (hlr t) hwidths hwidthMax hx hwidthlim
        (hleft t) (hright t) r (hr.1 t ht)
    · have hn : ∀t,r ∉ Ioo (a t) (z t) := not_exists.mp hcap
      by_cases hrA : r ∈ A
      · rw [show fixed r=w r from fixedCapContactWeight_at_contact a z _ A w hcontact hrA]
        exact hr.2.1 hrA
      · rw [show fixed r=0 from fixedCapContactWeight_outside a z _ A w hn hrA]
        exact comparisonNativeSideColumn_tendsto_zero_of_mask hc hk hkc hm hM q α
          as ho K J unit x widths hδ hstart hend hwidths hx r (hr.2.2 hn hrA)
  have hfinite : volume (Ioo ag zg)≠⊤ := ne_top_of_le_ne_top
    (by simp : volume (Icc ag zg)≠⊤) (measure_mono Ioo_subset_Icc_self)
  have hmeas j : AEStronglyMeasurable (moving j) (volume.restrict (Ioo ag zg)) :=
    (comparisonNativeUnitColumnWeight_measurable hc hk hkc hm hM q α (as j)
      (J j) (unit j) _).aestronglyMeasurable.restrict
  have hb j r : ‖moving j r‖ ≤ 2/δ := by
    have hh := comparisonNativeUnitColumnWeight_side_bound hc hk hkc hm hM q α
      (as j) (ho j) (J j) (unit j) (x j) (hstart j) (hend j) hδ (hwidths j) (hx j) r
    change moving j r ∈ Icc (0:ℝ) (2/δ) at hh
    simpa only [Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2
  have hL1 := bounded_contact_weights_tendsto_L1 (Ioo ag zg) hfinite moving fixed
    hmeas (fun j=>ae_of_all _ (hb j)) hpoint
  have hderiv j : AEStronglyMeasurable (fun r=>deriv α.val.val r*moving j r)
      (volume.restrict (Ioo ag zg)) :=
    (stronglyMeasurable_deriv α.val.val).aestronglyMeasurable.restrict.mul (hmeas j)
  have hdb j : ∀ᵐ r ∂ volume.restrict (Ioo ag zg),
      ‖deriv α.val.val r*moving j r‖ ≤ M 1*(2/δ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have h01 : r ∈ Ioo (0:ℝ) 1 := ⟨hag.trans hr.1,hr.2.trans_le hzg⟩
    have hd := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds h01.1 h01.2)
      (inverseIntegralConstraints_lipschitz hm hM α.property)
    rw [norm_mul]
    exact mul_le_mul hd (hb j r) (norm_nonneg _) hM
  have hdL1 := bounded_contact_weights_tendsto_L1 (Ioo ag zg) hfinite
    (fun j r=>deriv α.val.val r*moving j r) (fun r=>deriv α.val.val r*fixed r)
    hderiv hdb (hpoint.mono (fun r hr=>hr.const_mul (deriv α.val.val r)))
  exact ⟨hpoint,hL1,hdL1⟩

theorem comparisonNativeSideColumn_full_L1_from_uniform_cumulative {ι : Type} {τ : Type*}
    [Fintype τ] [DecidableEq τ]
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    {ag zg δ : ℝ} (hag : 0 < ag) (hzg : zg ≤ 1) (hδ : 0 < δ)
    (A : Set ℝ) (hA : MeasurableSet A) (hAband : A ⊆ Ioo ag zg)
    (H : ℝ → ℝ) {U : Set ℝ} (hopen : IsOpen U) (hU : U ⊆ Ioo (0:ℝ) 1)
    (hneg : ∀r ∈ U,H r < 0)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hmeshlim : Tendsto mesh atTop (𝓝 0)) (K : ℕ → ℕ)
    (J : ∀j,Finset (Fin ((sampleClockSteps q 0 (as j)).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps q 0 (as j)).length+1) → Fin (K j))
    (x : ℕ → ℕ → ℝ) (hstart : ∀j,x j 0=0)
    (hx : ∀j,∀u : Fin (K j),x j u.val < x j (u.val+1))
    (hmass : ∀j,∀u : Fin (K j),
      physicalSelectedUnitMass (sampleClockSteps q 0 (as j)) (J j) (unit j) u=
        x j (u.val+1)-x j u.val)
    (horder : ∀j,MonotoneOn (unit j) (J j:Set (Fin ((sampleClockSteps q 0 (as j)).length+1))))
    (hwidths : ∀j,2*δ ≤ x j (K j)) (hwidthMax : ∀j,x j (K j) ≤ 1)
    (hpos : ∀j,∀i ∈ J j,0 < pathMassDifferences (sampleClockSteps q 0 (as j)) 0 i)
    (hclass : ∀m,∀i ∈ J m,∀j ∈ J m,unit m i=unit m j ↔
      WholeUnitSideKernel.wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α
        (physicalCutMass 0 (sampleClockSteps q 0 (as m)) i.val))=
      WholeUnitSideKernel.wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α
        (physicalCutMass 0 (sampleClockSteps q 0 (as m)) j.val)))
    (hcell : ∀ᵐ r ∂volume.restrict A,∀ᶠ j in atTop,
      comparisonNativeContactCellWitness hc hk hkc hm hM q α (as j) (J j) (unit j) H U r)
    (f : Icc (0:ℝ) 1 →ᵇ ℝ)
    (huniform : Tendsto (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM
      q α (as j) (ho j) (J j)) atTop (𝓝 f))
    (a z l rr : τ → ℝ) (capUnit : ∀j,τ → Fin (K j))
    (hlr : ∀i,l i < rr i)
    (hleft : ∀i,Tendsto (fun j=>x j (capUnit j i).val) atTop (𝓝 (l i)))
    (hright : ∀i,Tendsto (fun j=>x j ((capUnit j i).val+1)) atTop (𝓝 (rr i)))
    (hdisjoint : Pairwise (fun i j=>Disjoint (Ioo (a i) (z i)) (Ioo (a j) (z j))))
    (hcontact : ∀i,Disjoint (Ioo (a i) (z i)) A)
    (hcapcell : ∀ᵐ r ∂volume.restrict (Ioo ag zg),∀t,r ∈ Ioo (a t) (z t) →
      ∀ᶠ j in atTop,∃i : Fin ((sampleClockSteps q 0 (as j)).length+1),
        i ∈ J j ∧ i.val < (as j).length ∧ unit j i=capUnit j t ∧
        r ∈ Ioc (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i.val))
          (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) (i.val+1))))
    (hoff : ∀ᵐ r ∂volume.restrict (Ioo ag zg),(∀t,r ∉ Ioo (a t) (z t)) → r ∉ A →
      Tendsto (fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
        (J j) (unit j) (fun _=>1) r) atTop (𝓝 0)) :
    let width := f ⟨1,by simp⟩
    let w := fun r=>pointSideColumn δ width (comparisonContactLimitCoordinate f r)
    let moving := fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
      (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (x j (K j)) u.val)
    let fixed := fixedCapContactWeight a z (fun i=>sideSquareColumnLR δ width (l i) (rr i)) A w
    Tendsto (fun j=>x j (K j)) atTop (𝓝 width) ∧ 2*δ ≤ width ∧
    (∀ᵐ r ∂volume.restrict (Ioo ag zg),Tendsto (fun j=>moving j r) atTop (𝓝 (fixed r))) ∧
    Tendsto (fun j=>∫r in Ioo ag zg,|moving j r-fixed r|) atTop (𝓝 0) ∧
    Tendsto (fun j=>∫r in Ioo ag zg,
      |deriv α.val.val r*moving j r-deriv α.val.val r*fixed r|) atTop (𝓝 0) ∧
    (∫r in A,deriv α.val.val r*w r) ≤ 2*Real.log (width/δ) := by
  dsimp only
  have hnative := comparisonNativeContactColumn_convergence_of_uniform_cumulative
    hc hk hkc hm hM q α hag hzg hδ A hA hAband H hopen hU hneg as mesh ho hend
    hmesh hmeshlim K J unit x hstart hx hmass horder hwidths hpos hclass hcell f huniform
  dsimp only at hnative
  have hcontactpoint : ∀ᵐ r ∂volume.restrict (Ioo ag zg),r ∈ A →
      Tendsto (fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
        (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (x j (K j)) u.val) r)
        atTop (𝓝 (pointSideColumn δ (f ⟨1,by simp⟩) (comparisonContactLimitCoordinate f r))) :=
    ae_mono Measure.restrict_le_self ((ae_restrict_iff' hA).mp hnative.2.2.1)
  have hfull := comparisonNativeSideColumn_full_L1_of_geometry hc hk hkc hm hM q α as ho
    K J unit x (fun j=>x j (K j)) capUnit hδ hnative.2.1 hag hzg hstart (fun _=>rfl)
    hwidths hwidthMax hx hnative.1 a z l rr hlr hleft hright A
    (fun r=>pointSideColumn δ (f ⟨1,by simp⟩) (comparisonContactLimitCoordinate f r))
    hdisjoint hcontact (by
      filter_upwards [hcapcell,hcontactpoint,hoff] with r hcap hcon hout
      exact ⟨hcap,hcon,hout⟩)
  exact ⟨hnative.1,hnative.2.1,hfull.1,hfull.2.1,hfull.2.2,hnative.2.2.2.2⟩

end
end OAI.SKFluctuations.LaplaceWindowFormalization
