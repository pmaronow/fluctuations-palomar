module

public import ComparisonShiftedNativeContactUnitMass
public import ComparisonShiftedNativeSideColumns
public import ComparisonActualHighWallSelectedCumulative
public import ComparisonNativeContactColumnConvergence

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 16000000
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem unitColumn_point_bound
    (as : List PositiveMass) (ho : MassOrdered 0 as) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K)
    (x : ℕ→ℝ) {δ width r s small : ℝ} (hδ : 0 < δ) (hw : 2*δ ≤ width)
    (hx : ∀u : Fin K,x u.val < x (u.val+1))
    (i : Fin ((sampleClockSteps m.q 0 as).length+1)) (hi : i ∈ J)
    (hil : i.val < as.length)
    (hr : r ∈ Ioc
      (m.R (partitionPoint 0 as i.val))
      (m.R (partitionPoint 0 as (i.val+1))))
    (hs : s ∈ Icc (x (unit i).val) (x ((unit i).val+1)))
    (hsmall : x ((unit i).val+1)-x (unit i).val ≤ small) :
    |m.unitColumn as J unit
        (fun u=>sideSquareColumn x δ width u.val) r-pointSideColumn δ width s| ≤
      2*(δ⁻¹)^2*small := by
  have he := radiusCellEnergyDensity_on_original_cell
    (m.R)
    (m.R_monotone) as ho
    (nativeSelectedColumn J unit (fun u=>sideSquareColumn x δ width u.val)) hil hr
  change m.unitColumn as J unit
    (fun u=>sideSquareColumn x δ width u.val) r=
      nativeSelectedColumn J unit (fun u=>sideSquareColumn x δ width u.val) i.val at he
  rw [he,nativeSelectedColumn_atIndex,ite_eq_left hi]
  exact (sideSquareColumn_point_stability x (unit i).val hδ hw (hx (unit i)) hs).trans
    (mul_le_mul_of_nonneg_left hsmall (by positivity))

private theorem shiftedPartitionPoint_succ_length (a : ℝ) (as : List PositiveMass) :
    partitionPoint a as (as.length+1)=partitionEnd a as := by
  induction as generalizing a with
  | nil=>rfl
  | cons b bs ih=>simpa only [List.length_cons,Nat.add_right_comm,
      partitionPoint,partitionValues,partitionEnd] using ih b.val

theorem selectedCDF_at_one_eq_width (hr0 : 0≤ m.rmin)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (hhigh : ∀i∈J,m.u0≤ partitionPoint 0 as i.val)
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K) (x : ℕ→ℝ)
    (h0 : x 0=0)
    (hmass : ∀u : Fin K,physicalSelectedUnitMass (sampleClockSteps m.q 0 as) J unit u=
      x (u.val+1)-x u.val) :
    m.selectedCDF as ho J
      ⟨1,by simp⟩=x K := by
  have hp := m.selected_cumulative_at_cut hr0 as ho he J hhigh (as.length+1)
  rw [shiftedPartitionPoint_succ_length,he,m.R_one] at hp
  change cumulativeCellMass (m.selectedMassDensity as J) 1=x K
  rw [hp]
  have hsum : (∑i : Fin ((sampleClockSteps m.q 0 as).length+1),
      pathMassDifferences (sampleClockSteps m.q 0 as) 0 i*
        (if i∈J ∧ i.val< as.length+1 then 1 else 0))=
      ∑u : Fin K,physicalSelectedUnitMass (sampleClockSteps m.q 0 as) J unit u := by
    have hg := selected_mass_grouping (sampleClockSteps m.q 0 as) J unit (fun _=>1)
    simpa only [sampleClockSteps_length,mul_one,and_true,
      show ∀i : Fin ((sampleClockSteps m.q 0 as).length+1),i.val< as.length+1 by
        intro i;simpa only [sampleClockSteps_length] using i.isLt] using hg
  rw [hsum]
  have hx := WholeUnitSideKernel.finite_unit_coordinate_eq_cumulative x
    (physicalSelectedUnitMass (sampleClockSteps m.q 0 as) J unit) h0
    (fun u=>(hmass u).symm) K le_rfl
  simpa only [Fin.is_lt,ite_true] using hx.symm

theorem contactColumn_limit_mass (hr0 : 0≤ m.rmin)
    {a z : ℝ} (ha : m.rmin < a) (hz : z ≤ 1)
    (A : Set ℝ) (hA : MeasurableSet A) (hAband : A ⊆ Ioo a z)
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (hend : ∀j,partitionEnd 0 (as j)=1) (K : ℕ→ℕ)
    (J : ∀j,Finset (Fin ((sampleClockSteps m.q 0 (as j)).length+1)))
    (hhigh : ∀j,∀i∈J j,m.u0≤ partitionPoint 0 (as j) i.val)
    (unit : ∀j,Fin ((sampleClockSteps m.q 0 (as j)).length+1)→Fin (K j))
    (x : ℕ→ℕ→ℝ) (widths : ℕ→ℝ) (small : ℕ→ℝ→ℝ) {δ width : ℝ}
    (hδ : 0 < δ) (hw : 2*δ ≤ width) (hwidths : ∀j,2*δ ≤ widths j)
    (hstart : ∀j,x j 0=0) (hxend : ∀j,x j (K j)=widths j)
    (hx : ∀j,∀u : Fin (K j),x j u.val < x j (u.val+1))
    (hmass : ∀j,∀u : Fin (K j),
      physicalSelectedUnitMass (sampleClockSteps m.q 0 (as j)) (J j) (unit j) u=
        x j (u.val+1)-x j u.val)
    (hwlim : Tendsto widths atTop (𝓝 width))
    (hsmall : ∀ᵐ r ∂volume.restrict A,Tendsto (fun j=>small j r) atTop (𝓝 0))
    (Fseq : ℕ→ℝ→ℝ) (F : ℝ→ℝ)
    (hFlim : ∀ᵐ r ∂volume.restrict A,Tendsto (fun j=>Fseq j r) atTop (𝓝 (F r)))
    (hcell : ∀ᵐ r ∂volume.restrict A,∀ᶠ j in atTop,
      ∃i : Fin ((sampleClockSteps m.q 0 (as j)).length+1),i ∈ J j ∧ i.val < (as j).length ∧
        r ∈ Ioc
          (m.R (partitionPoint 0 (as j) i.val))
          (m.R (partitionPoint 0 (as j) (i.val+1))) ∧
        Fseq j r ∈ Icc (x j (unit j i).val) (x j ((unit j i).val+1)) ∧
        x j ((unit j i).val+1)-x j (unit j i).val ≤ small j r) :
    (∫r in A,deriv m.alpha.val.val r*pointSideColumn δ width (F r)) ≤
      2*Real.log (width/δ) := by
  let wj := fun j=>m.unitColumn
    (as j) (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val)
  have hwj j r : wj j r ∈ Icc (0:ℝ) (2/δ) :=
    m.unitColumn_side_bound (as j) (ho j)
      (J j) (unit j) (x j) (hstart j) (hxend j) hδ (hwidths j) (hx j) r
  have hwi j : Integrable (fun r=>deriv m.alpha.val.val r*wj j r) := by
    exact (m.original_coefficients_mass_radius_eq (as j) (ho j) _
      (m.nativeColumn_high_support (as j) (J j) (unit j) _ (hhigh j))).1
  have hlim : ∀ᵐ r ∂volume.restrict A,
      Tendsto (fun j=>wj j r) atTop (𝓝 (pointSideColumn δ width (F r))) := by
    filter_upwards [hFlim,hcell,hsmall] with r hFr hcr hsr
    have hclose : Tendsto (fun j=>wj j r-pointSideColumn δ (widths j) (Fseq j r))
        atTop (𝓝 0) := by
      have he : Tendsto (fun j=>2*(δ⁻¹)^2*small j r) atTop (𝓝 0) := by
        simpa only [mul_zero] using hsr.const_mul (2*(δ⁻¹)^2)
      have hb : ∀ᶠ j in atTop,
          |wj j r-pointSideColumn δ (widths j) (Fseq j r)| ≤ 2*(δ⁻¹)^2*small j r := by
        filter_upwards [hcr] with j hj
        obtain ⟨i,hi,hil,hr,hs,hsm⟩ := hj
        exact m.unitColumn_point_bound
          (as j) (ho j) (J j) (unit j) (x j) hδ (hwidths j) (hx j) i hi hil hr hs hsm
      have hh := squeeze_zero' (Eventually.of_forall (fun _=>abs_nonneg _)) hb he
      exact (tendsto_zero_iff_norm_tendsto_zero).mpr (by simpa only [Real.norm_eq_abs] using hh)
    have hp := pointSideColumn_varying_tendsto hδ hw widths (fun j=>Fseq j r) (F r)
      hwidths hwlim hFr
    simpa only [sub_add_cancel,zero_add] using hclose.add hp
  have hAf : volume A ≠ ⊤ := ne_top_of_le_ne_top
    (by simp : volume (Icc (0:ℝ) 1) ≠ ⊤) (measure_mono (fun r hr=>
      ⟨hr0.trans (ha.le.trans (hAband hr).1.le),(hAband hr).2.le.trans hz⟩))
  have hbound j : ∀ᵐ r ∂volume.restrict A,
      ‖deriv m.alpha.val.val r*wj j r‖ ≤ m.M 1*(2/δ) := by
    apply (ae_restrict_iff' hA).mpr
    exact ae_of_all _ (fun r hr=>by
      have hr01 : r ∈ Ioo m.rmin 1 := ⟨ha.trans (hAband hr).1,(hAband hr).2.trans_le hz⟩
      have hd := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hr01.1 hr01.2)
        (inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property)
      have hw0 := hwj j r
      have hwn : ‖wj j r‖ ≤ 2/δ := by
        simpa only [Real.norm_eq_abs,abs_of_nonneg hw0.1] using hw0.2
      rw [norm_mul]
      exact mul_le_mul hd hwn (norm_nonneg _) m.hM)
  have htrace := tendsto_integral_of_dominated_convergence (μ:=volume.restrict A)
    (fun _=>m.M 1*(2/δ)) (fun j=>(hwi j).aestronglyMeasurable.restrict)
    (integrableOn_const hAf) hbound (hlim.mono (fun r hr=>hr.const_mul (deriv m.alpha.val.val r)))
  have hmassbound j : (∫r in A,deriv m.alpha.val.val r*wj j r) ≤ 2*Real.log (widths j/δ) := by
    have hpositive : ∀r,0 ≤ deriv m.alpha.val.val r*wj j r :=
      fun r=>mul_nonneg m.alpha.val.property.2.deriv_nonneg (hwj j r).1
    exact (setIntegral_le_integral (hwi j) (ae_of_all _ hpositive)).trans
      (m.unitColumn_side_mass_le_log
        (as j) (ho j) (hend j) (J j) (unit j) (hhigh j) (x j) (hstart j) (hxend j) hδ
        (hwidths j) (hx j) (hmass j))
  have hwidth0 : 0 < width := by linarith
  have hloglim : Tendsto (fun j=>2*Real.log (widths j/δ)) atTop
      (𝓝 (2*Real.log (width/δ))) :=
    ((Real.continuousAt_log (div_pos hwidth0 hδ).ne').tendsto.comp
      (hwlim.div_const δ)).const_mul 2
  exact le_of_tendsto_of_tendsto htrace hloglim (Eventually.of_forall hmassbound)
theorem sampled_contact_geometry_unit_mass_le_mesh
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as)
    (H : ℝ→ℝ) {U : Set ℝ} (hopen : IsOpen U) (hU : U⊆Icc m.rmin 1)
    (hneg : ∀r ∈ U,H r<0) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K)
    (hhigh : ∀i∈J,m.u0≤ physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val)
    (hpos : ∀i ∈ J,0 < pathMassDifferences (sampleClockSteps m.q 0 as) 0 i)
    (hclass : ∀i ∈ J,∀j ∈ J,unit i=unit j↔
      wholeUnit U (m.R
        (physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val))=
      wholeUnit U (m.R
        (physicalCutMass 0 (sampleClockSteps m.q 0 as) j.val)))
    (i : Fin ((sampleClockSteps m.q 0 as).length+1)) (hi : i ∈ J)
    (hmeet : m.R
        (physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val) ∈ U →
      ∀j ∈ J,unit j=unit i→∃t ∈ Icc
        (m.R
          (physicalCutMass 0 (sampleClockSteps m.q 0 as) j.val))
        (m.R
          (physicalCutMass 0 (sampleClockSteps m.q 0 as) (j.val+1))),H t=0) :
    physicalSelectedUnitMass (sampleClockSteps m.q 0 as) J unit (unit i) ≤ mesh := by
  by_cases hiU : m.R (physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val)∈U
  · exact m.sampled_contact_cap_unit_mass_le_mesh as ho hmesh H hopen hU hneg
      J unit hhigh hclass hi hiU (hmeet hiU)
  · exact m.sampled_contact_unit_mass_le_mesh as ho hmesh U J unit hhigh hpos hclass hi hiU

def contactCellWitness
    (as : List PositiveMass) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K)
    (H : ℝ→ℝ) (U : Set ℝ) (r : ℝ) : Prop :=
  ∃i : Fin ((sampleClockSteps m.q 0 as).length+1),i ∈ J ∧ i.val < as.length ∧
    r ∈ Ioc
      (m.R (partitionPoint 0 as i.val))
      (m.R (partitionPoint 0 as (i.val+1))) ∧
    (m.R
        (physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val) ∈ U →
      ∀j ∈ J,unit j=unit i→∃t ∈ Icc
        (m.R
          (physicalCutMass 0 (sampleClockSteps m.q 0 as) j.val))
        (m.R
          (physicalCutMass 0 (sampleClockSteps m.q 0 as) (j.val+1))),H t=0)

theorem contactColumn_convergence_of_uniform_cumulative (hr0 : 0≤ m.rmin)
    {a z δ : ℝ} (ha : m.rmin < a) (hz : z ≤ 1) (hδ : 0 < δ)
    (A : Set ℝ) (hA : MeasurableSet A) (hAband : A⊆Ioo a z)
    (H : ℝ→ℝ) {U : Set ℝ} (hopen : IsOpen U) (hU : U⊆Icc m.rmin 1)
    (hneg : ∀r ∈ U,H r<0)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hmeshlim : Tendsto mesh atTop (𝓝 0)) (K : ℕ→ℕ)
    (J : ∀j,Finset (Fin ((sampleClockSteps m.q 0 (as j)).length+1)))
    (hhigh : ∀j,∀i∈J j,m.u0≤ partitionPoint 0 (as j) i.val)
    (unit : ∀j,Fin ((sampleClockSteps m.q 0 (as j)).length+1)→Fin (K j))
    (x : ℕ→ℕ→ℝ) (hstart : ∀j,x j 0=0)
    (hx : ∀j,∀u : Fin (K j),x j u.val < x j (u.val+1))
    (hmass : ∀j,∀u : Fin (K j),
      physicalSelectedUnitMass (sampleClockSteps m.q 0 (as j)) (J j) (unit j) u=
        x j (u.val+1)-x j u.val)
    (horder : ∀j,MonotoneOn (unit j) (J j:Set (Fin ((sampleClockSteps m.q 0 (as j)).length+1))))
    (hwidths : ∀j,2*δ ≤ x j (K j))
    (hpos : ∀j,∀i ∈ J j,0 < pathMassDifferences (sampleClockSteps m.q 0 (as j)) 0 i)
    (hclass : ∀jnet,∀i ∈ J jnet,∀j ∈ J jnet,unit jnet i=unit jnet j↔
      wholeUnit U (m.R
        (physicalCutMass 0 (sampleClockSteps m.q 0 (as jnet)) i.val))=
      wholeUnit U (m.R
        (physicalCutMass 0 (sampleClockSteps m.q 0 (as jnet)) j.val)))
    (hcell : ∀ᵐ r ∂volume.restrict A,∀ᶠ j in atTop,
      m.contactCellWitness (as j) (J j) (unit j) H U r)
    (f : Icc (0:ℝ) 1 →ᵇ ℝ)
    (huniform : Tendsto (fun j=>m.selectedCDF (as j) (ho j) (J j)) atTop (𝓝 f)) :
    let width := f ⟨1,by simp⟩
    let w := fun r=>pointSideColumn δ width (comparisonContactLimitCoordinate f r)
    let moving := fun j=>m.unitColumn
      (as j) (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (x j (K j)) u.val)
    Tendsto (fun j=>x j (K j)) atTop (𝓝 width) ∧ 2*δ ≤ width ∧
    (∀ᵐ r ∂volume.restrict A,Tendsto (fun j=>moving j r) atTop (𝓝 (w r))) ∧
    Tendsto (fun j=>∫r in A,|deriv m.alpha.val.val r*moving j r-deriv m.alpha.val.val r*w r|)
      atTop (𝓝 0) ∧
    (∫r in A,deriv m.alpha.val.val r*w r) ≤ 2*Real.log (width/δ) := by
  dsimp only
  let width := f ⟨1,by simp⟩
  let widths := fun j=>x j (K j)
  let Fseq := fun j=>comparisonContactLimitCoordinate
    (m.selectedCDF (as j) (ho j) (J j))
  let F := comparisonContactLimitCoordinate f
  let w := fun r=>pointSideColumn δ width (F r)
  let moving := fun j=>m.unitColumn
    (as j) (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val)
  have hwlim : Tendsto widths atTop (𝓝 width) := by
    have he := (BoundedContinuousFunction.lipschitz_eval_const
      (⟨1,by simp⟩ : Icc (0:ℝ) 1)).continuous.tendsto f |>.comp huniform
    have heq : ((fun g : Icc (0:ℝ) 1 →ᵇ ℝ=>g ⟨1,by simp⟩)∘
        (fun j=>m.selectedCDF (as j) (ho j) (J j)))=
        widths := by
      funext j
      exact m.selectedCDF_at_one_eq_width hr0
        (as j) (ho j) (hend j) (J j) (hhigh j) (unit j) (x j) (hstart j) (hmass j)
    rw [heq] at he
    exact he
  have hw : 2*δ ≤ width := ge_of_tendsto hwlim (Eventually.of_forall hwidths)
  have hFlim : ∀ᵐ r ∂volume.restrict A,Tendsto (fun j=>Fseq j r) atTop (𝓝 (F r)) := by
    apply ae_of_all
    intro r
    exact (BoundedContinuousFunction.lipschitz_eval_const
      (projIcc 0 1 (by norm_num) r)).continuous.tendsto f |>.comp huniform
  have hcell' : ∀ᵐ r ∂volume.restrict A,∀ᶠ j in atTop,
      ∃i : Fin ((sampleClockSteps m.q 0 (as j)).length+1),i ∈ J j ∧ i.val < (as j).length ∧
        r ∈ Ioc
          (m.R (partitionPoint 0 (as j) i.val))
          (m.R (partitionPoint 0 (as j) (i.val+1))) ∧
        Fseq j r ∈ Icc (x j (unit j i).val) (x j ((unit j i).val+1)) ∧
        x j ((unit j i).val+1)-x j (unit j i).val ≤ mesh j := by
    filter_upwards [hcell,ae_restrict_mem hA] with r hcr hrA
    have hr01 : r ∈ Icc (0:ℝ) 1 :=
      ⟨hr0.trans (ha.le.trans (hAband hrA).1.le),(hAband hrA).2.le.trans hz⟩
    filter_upwards [hcr] with j hj
    obtain ⟨i,hi,hil,hr,hmeet⟩ := hj
    refine ⟨i,hi,hil,hr,?_,?_⟩
    · have hh := m.selected_cumulative_mem_unit_interval hr0 (as j) (ho j) (hend j) (J j) (hhigh j) (unit j) (x j) (hstart j) (hmass j)
        (horder j) i hi hr
      simpa only [Fseq,comparisonContactLimitCoordinate,projIcc_of_mem zero_le_one hr01,
        selectedCDF_apply] using hh
    · rw [←hmass j (unit j i)]
      exact m.sampled_contact_geometry_unit_mass_le_mesh
        (as j) (ho j) (hmesh j) H hopen hU hneg (J j) (unit j)
        (fun k hk=>by
          rw [physicalCutMass_sampleClockSteps m.q 0 (as j) k.val (by
            have h:=k.isLt;simp only [sampleClockSteps_length] at h;omega)]
          exact hhigh j k hk) (hpos j)
        (hclass j) i hi hmeet
  have hlim : ∀ᵐ r ∂volume.restrict A,
      Tendsto (fun j=>moving j r) atTop (𝓝 (w r)) := by
    filter_upwards [hFlim,hcell'] with r hFr hcr
    have hclose : Tendsto (fun j=>moving j r-pointSideColumn δ (widths j) (Fseq j r))
        atTop (𝓝 0) := by
      have he : Tendsto (fun j=>2*(δ⁻¹)^2*mesh j) atTop (𝓝 0) := by
        simpa only [mul_zero] using hmeshlim.const_mul (2*(δ⁻¹)^2)
      have hb : ∀ᶠ j in atTop,
          |moving j r-pointSideColumn δ (widths j) (Fseq j r)| ≤ 2*(δ⁻¹)^2*mesh j := by
        filter_upwards [hcr] with j hj
        obtain ⟨i,hi,hil,hr,hs,hsm⟩ := hj
        exact m.unitColumn_point_bound
          (as j) (ho j) (J j) (unit j) (x j) hδ (hwidths j) (hx j) i hi hil hr hs hsm
      exact (tendsto_zero_iff_norm_tendsto_zero).mpr (by
        simpa only [Real.norm_eq_abs] using
          squeeze_zero' (Eventually.of_forall (fun _=>abs_nonneg _)) hb he)
    have hp := pointSideColumn_varying_tendsto hδ hw widths (fun j=>Fseq j r) (F r)
      hwidths hwlim hFr
    simpa only [sub_add_cancel,zero_add] using hclose.add hp
  have hAf : volume A ≠ ⊤ := ne_top_of_le_ne_top
    (by simp : volume (Icc (0:ℝ) 1) ≠ ⊤) (measure_mono (fun r hr=>
      ⟨hr0.trans (ha.le.trans (hAband hr).1.le),(hAband hr).2.le.trans hz⟩))
  have hmb j : ∀ᵐ r ∂volume.restrict A,
      ‖deriv m.alpha.val.val r*moving j r‖ ≤ m.M 1*(2/δ) := by
    apply (ae_restrict_iff' hA).mpr
    exact ae_of_all _ (fun r hr=>by
      have hr01 : r ∈ Ioo m.rmin 1 := ⟨ha.trans (hAband hr).1,(hAband hr).2.trans_le hz⟩
      have hd := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hr01.1 hr01.2)
        (inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property)
      have hh := m.unitColumn_side_bound
        (as j) (ho j) (J j) (unit j) (x j) (hstart j) (show x j (K j)=widths j from rfl)
        hδ (hwidths j) (hx j) r
      change moving j r ∈ Icc (0:ℝ) (2/δ) at hh
      rw [norm_mul]
      exact mul_le_mul hd (by simpa only [Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2)
        (norm_nonneg _) m.hM)
  have hL1 := bounded_contact_weights_tendsto_L1 A hAf
    (fun j r=>deriv m.alpha.val.val r*moving j r) (fun r=>deriv m.alpha.val.val r*w r)
    (fun j=>((stronglyMeasurable_deriv m.alpha.val.val).mul
      (m.unitColumn_measurable (as j)
        (J j) (unit j) _).stronglyMeasurable).aestronglyMeasurable.restrict)
    hmb (hlim.mono (fun r hr=>hr.const_mul (deriv m.alpha.val.val r)))
  have hmasslim := m.contactColumn_limit_mass hr0
    ha hz A hA hAband as ho hend K J hhigh unit x widths (fun j _=>mesh j)
    hδ hw hwidths hstart (fun _=>rfl) hx hmass hwlim
    (ae_of_all _ (fun _=>hmeshlim)) Fseq F hFlim hcell'
  exact ⟨hwlim,hw,hlim,hL1,hmasslim⟩

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
