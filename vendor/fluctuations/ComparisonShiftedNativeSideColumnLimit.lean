module

public import ComparisonShiftedNativeMaskColumns
public import ComparisonShiftedNativeSideColumns
public import ComparisonNativeSideColumnLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 12000000
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem unitColumn_mul_mask
    (as : List PositiveMass) (ho : MassOrdered 0 as) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1) → Fin K)
    (col : Fin K → ℝ) (r : ℝ) :
    m.unitColumn as J unit col r*
      m.unitColumn as J unit (fun _=>1) r=
      m.unitColumn as J unit col r := by
  unfold unitColumn
  rw [radiusCellEnergyDensity_mul _ m.R_monotone as ho]
  congr 1
  funext i
  unfold nativeSelectedColumn
  split_ifs  <;> simp

theorem sideColumn_tendsto_zero_of_mask
    (as : ℕ → List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (K : ℕ → ℕ) (J : ∀j,Finset (Fin ((sampleClockSteps m.q 0 (as j)).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps m.q 0 (as j)).length+1) → Fin (K j))
    (x : ℕ → ℕ → ℝ) (widths : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hstart : ∀j,x j 0=0) (hend : ∀j,x j (K j)=widths j)
    (hwidths : ∀j,2*δ ≤ widths j)
    (hx : ∀j,∀u : Fin (K j),x j u.val < x j (u.val+1))
    (r : ℝ) (hmask : Tendsto (fun j=>m.unitColumn (as j) (J j) (unit j) (fun _=>1) r) atTop (𝓝 0)) :
    Tendsto (fun j=>m.unitColumn (as j)
      (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val) r)
      atTop (𝓝 0) := by
  let moving := fun j=>m.unitColumn (as j)
    (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val) r
  let mask := fun j=>m.unitColumn (as j)
    (J j) (unit j) (fun _=>1) r
  have hb j : moving j ∈ Icc (0:ℝ) (2/δ) :=
    m.unitColumn_side_bound (as j) (ho j)
      (J j) (unit j) (x j) (hstart j) (hend j) hδ (hwidths j) (hx j) r
  have hm0 j : 0 ≤ mask j :=
    (radiusCellEnergyDensity_mem_Icc_bound _ m.R_monotone
      (as j) (ho j) (nativeSelectedColumn (J j) (unit j) (fun _=>1)) zero_le_one (fun i=>by
        unfold nativeSelectedColumn
        split_ifs  <;> norm_num) r).1
  have he j : moving j*mask j=moving j :=
    m.unitColumn_mul_mask (as j) (ho j)
      (J j) (unit j) _ r
  have hup j : moving j ≤ (2/δ)*mask j := by
    rw [←he j]
    exact mul_le_mul_of_nonneg_right (hb j).2 (hm0 j)
  exact squeeze_zero (fun j=>(hb j).1) hup (by
    simpa only [mul_zero] using hmask.const_mul (2/δ))

theorem sideColumn_cap_tendsto
    (as : ℕ → List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (K : ℕ → ℕ) (J : ∀j,Finset (Fin ((sampleClockSteps m.q 0 (as j)).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps m.q 0 (as j)).length+1) → Fin (K j))
    (x : ℕ → ℕ → ℝ) (widths : ℕ → ℝ) (capUnit : ∀j,Fin (K j))
    {δ width l rr : ℝ} (hδ : 0 < δ) (hw : 2*δ ≤ width) (hlr : l < rr)
    (hwidths : ∀j,2*δ ≤ widths j) (hwidthMax : ∀j,widths j ≤ 1)
    (hx : ∀j,∀u : Fin (K j),x j u.val < x j (u.val+1))
    (hwidthlim : Tendsto widths atTop (𝓝 width))
    (hleft : Tendsto (fun j=>x j (capUnit j).val) atTop (𝓝 l))
    (hright : Tendsto (fun j=>x j ((capUnit j).val+1)) atTop (𝓝 rr))
    (r : ℝ)
    (hcell : ∀ᶠ j in atTop,∃i : Fin ((sampleClockSteps m.q 0 (as j)).length+1),
      i ∈ J j  ∧  i.val < (as j).length  ∧  unit j i=capUnit j  ∧ 
      r ∈ Ioc (m.R (partitionPoint 0 (as j) i.val))
        (m.R (partitionPoint 0 (as j) (i.val+1)))) :
    Tendsto (fun j=>m.unitColumn (as j)
      (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val) r)
      atTop (𝓝 (sideSquareColumnLR δ width l rr)) := by
  have hcol := sideSquareColumnLR_tendsto hδ hw hlr widths
    (fun j=>x j (capUnit j).val) (fun j=>x j ((capUnit j).val+1))
    hwidths hwidthMax (fun j=>hx j (capUnit j)) hwidthlim hleft hright
  apply (tendsto_congr' (f₁:=fun j=>m.unitColumn (as j) (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val) r)
    (f₂:=fun j=>sideSquareColumnLR δ (widths j) (x j (capUnit j).val)
      (x j ((capUnit j).val+1))) ?_).mpr hcol
  filter_upwards [hcell] with j hj
  obtain ⟨i,hi,hil,hu,hr⟩ := hj
  unfold unitColumn
  rw [radiusCellEnergyDensity_on_original_cell _
    m.R_monotone (as j) (ho j) _ hil hr,
    nativeSelectedColumn_atIndex,ite_eq_left hi,hu,
    sideSquareColumn_eq_LR (x j) (capUnit j).val hδ (hwidths j) (hx j (capUnit j))]

theorem sideColumn_full_L1_of_geometry {τ : Type*}
    [Fintype τ] [DecidableEq τ]
    (as : ℕ → List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (K : ℕ → ℕ) (J : ∀j,Finset (Fin ((sampleClockSteps m.q 0 (as j)).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps m.q 0 (as j)).length+1) → Fin (K j))
    (x : ℕ → ℕ → ℝ) (widths : ℕ → ℝ) (capUnit : ∀j,τ → Fin (K j))
    {δ width ag zg : ℝ} (hδ : 0 < δ) (hw : 2*δ ≤ width)
    (hag : m.rmin < ag) (hzg : zg ≤ 1)
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
        ∃i : Fin ((sampleClockSteps m.q 0 (as j)).length+1),
          i ∈ J j  ∧  i.val < (as j).length  ∧  unit j i=capUnit j t  ∧ 
          r ∈ Ioc (m.R (partitionPoint 0 (as j) i.val))
            (m.R (partitionPoint 0 (as j) (i.val+1))))  ∧ 
      (r ∈ A → Tendsto (fun j=>m.unitColumn (as j)
        (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val) r) atTop (𝓝 (w r)))  ∧ 
      ((∀t,r ∉ Ioo (a t) (z t)) → r ∉ A → Tendsto
        (fun j=>m.unitColumn (as j)
          (J j) (unit j) (fun _=>1) r) atTop (𝓝 0))) :
    let moving := fun j=>m.unitColumn (as j)
      (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val)
    let fixed := fixedCapContactWeight a z (fun i=>sideSquareColumnLR δ width (l i) (rr i)) A w
    (∀ᵐ r ∂ volume.restrict (Ioo ag zg),Tendsto (fun j=>moving j r) atTop (𝓝 (fixed r)))  ∧ 
    Tendsto (fun j=>∫r in Ioo ag zg,|moving j r-fixed r|) atTop (𝓝 0)  ∧ 
    Tendsto (fun j=>∫r in Ioo ag zg,
      |deriv m.alpha.val.val r*moving j r-deriv m.alpha.val.val r*fixed r|) atTop (𝓝 0) := by
  dsimp only
  let moving := fun j=>m.unitColumn (as j)
    (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val)
  let fixed := fixedCapContactWeight a z (fun i=>sideSquareColumnLR δ width (l i) (rr i)) A w
  have hpoint : ∀ᵐ r ∂ volume.restrict (Ioo ag zg),
      Tendsto (fun j=>moving j r) atTop (𝓝 (fixed r)) := by
    filter_upwards [hgeometry] with r hr
    by_cases hcap : ∃t,r ∈ Ioo (a t) (z t)
    · obtain ⟨t,ht⟩ := hcap
      rw [show fixed r=sideSquareColumnLR δ width (l t) (rr t) from
        fixedCapContactWeight_at_cap a z _ A w hdisjoint hcontact t ht]
      exact m.sideColumn_cap_tendsto as ho K J unit
        x widths (fun j=>capUnit j t) hδ hw (hlr t) hwidths hwidthMax hx hwidthlim
        (hleft t) (hright t) r (hr.1 t ht)
    · have hn : ∀t,r ∉ Ioo (a t) (z t) := not_exists.mp hcap
      by_cases hrA : r ∈ A
      · rw [show fixed r=w r from fixedCapContactWeight_at_contact a z _ A w hcontact hrA]
        exact hr.2.1 hrA
      · rw [show fixed r=0 from fixedCapContactWeight_outside a z _ A w hn hrA]
        exact m.sideColumn_tendsto_zero_of_mask
          as ho K J unit x widths hδ hstart hend hwidths hx r (hr.2.2 hn hrA)
  have hfinite : volume (Ioo ag zg)≠⊤ := ne_top_of_le_ne_top
    (by simp : volume (Icc ag zg)≠⊤) (measure_mono Ioo_subset_Icc_self)
  have hmeas j : AEStronglyMeasurable (moving j) (volume.restrict (Ioo ag zg)) :=
    (m.unitColumn_measurable (as j)
      (J j) (unit j) _).aestronglyMeasurable.restrict
  have hb j r : ‖moving j r‖ ≤ 2/δ := by
    have hh := m.unitColumn_side_bound
      (as j) (ho j) (J j) (unit j) (x j) (hstart j) (hend j) hδ (hwidths j) (hx j) r
    change moving j r ∈ Icc (0:ℝ) (2/δ) at hh
    simpa only [Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2
  have hL1 := bounded_contact_weights_tendsto_L1 (Ioo ag zg) hfinite moving fixed
    hmeas (fun j=>ae_of_all _ (hb j)) hpoint
  have hderiv j : AEStronglyMeasurable (fun r=>deriv m.alpha.val.val r*moving j r)
      (volume.restrict (Ioo ag zg)) :=
    (stronglyMeasurable_deriv m.alpha.val.val).aestronglyMeasurable.restrict.mul (hmeas j)
  have hdb j : ∀ᵐ r ∂ volume.restrict (Ioo ag zg),
      ‖deriv m.alpha.val.val r*moving j r‖ ≤ m.M 1*(2/δ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have h01 : r ∈ Ioo m.rmin 1 := ⟨hag.trans hr.1,hr.2.trans_le hzg⟩
    have hd := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds h01.1 h01.2)
      (inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property)
    rw [norm_mul]
    exact mul_le_mul hd (hb j r) (norm_nonneg _) m.hM
  have hdL1 := bounded_contact_weights_tendsto_L1 (Ioo ag zg) hfinite
    (fun j r=>deriv m.alpha.val.val r*moving j r) (fun r=>deriv m.alpha.val.val r*fixed r)
    hderiv hdb (hpoint.mono (fun r hr=>hr.const_mul (deriv m.alpha.val.val r)))
  exact ⟨hpoint,hL1,hdL1⟩

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
