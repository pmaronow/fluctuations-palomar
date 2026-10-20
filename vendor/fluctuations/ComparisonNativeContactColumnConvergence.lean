module

public import ComparisonSelectedCumulativeCoordinates
public import ComparisonNativeVarianceBinGeometry
public import ComparisonContactOnlyVaryingWeights

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
open WholeUnitSideKernel
set_option maxHeartbeats 2400000

def comparisonContactLimitCoordinate (f : Icc (0:ℝ) 1 →ᵇ ℝ) (r : ℝ) : ℝ :=
  f (projIcc 0 1 (by norm_num) r)

theorem comparisonContactLimitCoordinate_continuous (f : Icc (0:ℝ) 1 →ᵇ ℝ) :
    Continuous (comparisonContactLimitCoordinate f) :=
  f.continuous.comp continuous_projIcc

theorem pointSideColumn_coarse_norm_bound {δ width : ℝ}
    (hδ : 0 < δ) (hw : 2*δ ≤ width) (s : ℝ) :
    ‖pointSideColumn δ width s‖ ≤ 2*(δ⁻¹)^2*(width-2*δ) := by
  have hpq : δ ≤ width-δ := by linarith
  have hleft : ‖∫t in δ..width-δ,pointLeftSquare s t‖ ≤
      (δ⁻¹)^2*(width-2*δ) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=δ) (b:=width-δ) (C:=(δ⁻¹)^2) (f:=pointLeftSquare s)
      (fun t ht=>by
        have htδ : δ ≤ t := by simpa only [min_eq_left hpq] using ht.1.le
        have ht0 : 0 < t := hδ.trans_le htδ
        have hi : t⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ htδ
        unfold pointLeftSquare
        by_cases hs : s ≤ t
        · rw [indicator_of_mem (show t∈Ici s from hs),Real.norm_eq_abs,
            abs_of_nonneg (sq_nonneg _)]
          nlinarith [inv_nonneg.mpr ht0.le,inv_nonneg.mpr hδ.le]
        · rw [indicator_of_notMem (show t∉Ici s from hs),norm_zero]
          positivity)
    rw [abs_of_nonneg (by linarith : 0 ≤ width-δ-δ)] at hh
    convert hh using 1; ring
  have hright : ‖∫t in δ..width-δ,pointRightSquare width s t‖ ≤
      (δ⁻¹)^2*(width-2*δ) := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=δ) (b:=width-δ) (C:=(δ⁻¹)^2) (f:=pointRightSquare width s)
      (fun t ht=>by
        have htδ : δ ≤ width-t := by
          have htt : t ≤ width-δ := by simpa only [max_eq_right hpq] using ht.2
          linarith
        have ht0 : 0 < width-t := hδ.trans_le htδ
        have hi : (width-t)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ htδ
        unfold pointRightSquare
        by_cases hs : t ≤ s
        · rw [indicator_of_mem (show t∈Iic s from hs),Real.norm_eq_abs,
            abs_of_nonneg (sq_nonneg _)]
          nlinarith [inv_nonneg.mpr ht0.le,inv_nonneg.mpr hδ.le]
        · rw [indicator_of_notMem (show t∉Iic s from hs),norm_zero]
          positivity)
    rw [abs_of_nonneg (by linarith : 0 ≤ width-δ-δ)] at hh
    convert hh using 1; ring
  exact (norm_add_le _ _).trans ((add_le_add hleft hright).trans_eq (by ring))

private theorem nativePartitionPoint_succ_length (a : ℝ) (as : List PositiveMass) :
    partitionPoint a as (as.length+1)=partitionEnd a as := by
  induction as generalizing a with
  | nil=>rfl
  | cons b bs ih=>simpa only [List.length_cons,Nat.add_right_comm,
      partitionPoint,partitionValues,partitionEnd] using ih b.val

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r ∈ Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparison_selected_cumulative_at_one_eq_width {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps q 0 as).length+1)→Fin K) (x : ℕ→ℝ)
    (h0 : x 0=0)
    (hmass : ∀u : Fin K,physicalSelectedUnitMass (sampleClockSteps q 0 as) J unit u=
      x (u.val+1)-x u.val) :
    comparisonSelectedCumulativeMap hc hk hkc hm hM q α as ho J
      ⟨1,by simp⟩=x K := by
  have hR1 : comparisonSweepQuantile hc hk hkc hm hM α 1=1 := by
    simpa only [α.property.2.1] using comparisonSweepQuantile_inverse hc hk hkc hm hM α
      (show (1:ℝ)∈Icc (0:ℝ) 1 by simp)
  have hp := comparison_selected_cumulative_at_cut hc hk hkc hm hM q α as ho he J
    (as.length+1)
  rw [nativePartitionPoint_succ_length,he,hR1] at hp
  change cumulativeCellMass (comparisonSelectedMassDensity hc hk hkc hm hM q α as J) 1=x K
  rw [hp]
  have hsum : (∑i : Fin ((sampleClockSteps q 0 as).length+1),
      pathMassDifferences (sampleClockSteps q 0 as) 0 i*
        (if i∈J ∧ i.val< as.length+1 then 1 else 0))=
      ∑u : Fin K,physicalSelectedUnitMass (sampleClockSteps q 0 as) J unit u := by
    have hg := selected_mass_grouping (sampleClockSteps q 0 as) J unit (fun _=>1)
    simpa only [sampleClockSteps_length,mul_one,and_true,
      show ∀i : Fin ((sampleClockSteps q 0 as).length+1),i.val< as.length+1 by
        intro i;simpa only [sampleClockSteps_length] using i.isLt] using hg
  rw [hsum]
  have hx := WholeUnitSideKernel.finite_unit_coordinate_eq_cumulative x
    (physicalSelectedUnitMass (sampleClockSteps q 0 as) J unit) h0
    (fun u=>(hmass u).symm) K le_rfl
  simpa only [Fin.is_lt,ite_true] using hx.symm

theorem comparison_sampled_contact_geometry_unit_mass_le_mesh {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as)
    (H : ℝ→ℝ) {U : Set ℝ} (hopen : IsOpen U) (hU : U⊆Ioo (0:ℝ) 1)
    (hneg : ∀r ∈ U,H r<0) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps q 0 as).length+1)→Fin K)
    (hpos : ∀i ∈ J,0 < pathMassDifferences (sampleClockSteps q 0 as) 0 i)
    (hclass : ∀i ∈ J,∀j ∈ J,unit i=unit j↔
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α
        (physicalCutMass 0 (sampleClockSteps q 0 as) i.val))=
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α
        (physicalCutMass 0 (sampleClockSteps q 0 as) j.val)))
    (i : Fin ((sampleClockSteps q 0 as).length+1)) (hi : i ∈ J)
    (hmeet : comparisonSweepQuantile hc hk hkc hm hM α
        (physicalCutMass 0 (sampleClockSteps q 0 as) i.val) ∈ U →
      ∀j ∈ J,unit j=unit i→∃t ∈ Icc
        (comparisonSweepQuantile hc hk hkc hm hM α
          (physicalCutMass 0 (sampleClockSteps q 0 as) j.val))
        (comparisonSweepQuantile hc hk hkc hm hM α
          (physicalCutMass 0 (sampleClockSteps q 0 as) (j.val+1))),H t=0) :
    physicalSelectedUnitMass (sampleClockSteps q 0 as) J unit (unit i) ≤ mesh := by
  by_cases hiU : comparisonSweepQuantile hc hk hkc hm hM α
      (physicalCutMass 0 (sampleClockSteps q 0 as) i.val) ∈ U
  · exact comparison_sampled_contact_cap_unit_mass_le_mesh hc hk hkc hm hM α
      q as ho hmesh H hopen hU hneg J unit hclass hi hiU (hmeet hiU)
  · exact comparison_sampled_contact_unit_mass_le_mesh hc hk hkc hm hM α
      q as ho hmesh U J unit hpos hclass hi hiU

def comparisonNativeContactCellWitness {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps q 0 as).length+1)→Fin K)
    (H : ℝ→ℝ) (U : Set ℝ) (r : ℝ) : Prop :=
  ∃i : Fin ((sampleClockSteps q 0 as).length+1),i ∈ J ∧ i.val < as.length ∧
    r ∈ Ioc
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i.val))
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as (i.val+1))) ∧
    (comparisonSweepQuantile hc hk hkc hm hM α
        (physicalCutMass 0 (sampleClockSteps q 0 as) i.val) ∈ U →
      ∀j ∈ J,unit j=unit i→∃t ∈ Icc
        (comparisonSweepQuantile hc hk hkc hm hM α
          (physicalCutMass 0 (sampleClockSteps q 0 as) j.val))
        (comparisonSweepQuantile hc hk hkc hm hM α
          (physicalCutMass 0 (sampleClockSteps q 0 as) (j.val+1))),H t=0)

theorem comparisonNativeContactColumn_convergence_of_uniform_cumulative {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    {a z δ : ℝ} (ha : 0 < a) (hz : z ≤ 1) (hδ : 0 < δ)
    (A : Set ℝ) (hA : MeasurableSet A) (hAband : A⊆Ioo a z)
    (H : ℝ→ℝ) {U : Set ℝ} (hopen : IsOpen U) (hU : U⊆Ioo (0:ℝ) 1)
    (hneg : ∀r ∈ U,H r<0)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hmeshlim : Tendsto mesh atTop (𝓝 0)) (K : ℕ→ℕ)
    (J : ∀j,Finset (Fin ((sampleClockSteps q 0 (as j)).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps q 0 (as j)).length+1)→Fin (K j))
    (x : ℕ→ℕ→ℝ) (hstart : ∀j,x j 0=0)
    (hx : ∀j,∀u : Fin (K j),x j u.val < x j (u.val+1))
    (hmass : ∀j,∀u : Fin (K j),
      physicalSelectedUnitMass (sampleClockSteps q 0 (as j)) (J j) (unit j) u=
        x j (u.val+1)-x j u.val)
    (horder : ∀j,MonotoneOn (unit j) (J j:Set (Fin ((sampleClockSteps q 0 (as j)).length+1))))
    (hwidths : ∀j,2*δ ≤ x j (K j))
    (hpos : ∀j,∀i ∈ J j,0 < pathMassDifferences (sampleClockSteps q 0 (as j)) 0 i)
    (hclass : ∀m,∀i ∈ J m,∀j ∈ J m,unit m i=unit m j↔
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α
        (physicalCutMass 0 (sampleClockSteps q 0 (as m)) i.val))=
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α
        (physicalCutMass 0 (sampleClockSteps q 0 (as m)) j.val)))
    (hcell : ∀ᵐ r ∂volume.restrict A,∀ᶠ j in atTop,
      comparisonNativeContactCellWitness hc hk hkc hm hM q α (as j) (J j) (unit j) H U r)
    (f : Icc (0:ℝ) 1 →ᵇ ℝ)
    (huniform : Tendsto (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM
      q α (as j) (ho j) (J j)) atTop (𝓝 f)) :
    let width := f ⟨1,by simp⟩
    let w := fun r=>pointSideColumn δ width (comparisonContactLimitCoordinate f r)
    let moving := fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α
      (as j) (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (x j (K j)) u.val)
    Tendsto (fun j=>x j (K j)) atTop (𝓝 width) ∧ 2*δ ≤ width ∧
    (∀ᵐ r ∂volume.restrict A,Tendsto (fun j=>moving j r) atTop (𝓝 (w r))) ∧
    Tendsto (fun j=>∫r in A,|deriv α.val.val r*moving j r-deriv α.val.val r*w r|)
      atTop (𝓝 0) ∧
    (∫r in A,deriv α.val.val r*w r) ≤ 2*Real.log (width/δ) := by
  dsimp only
  let width := f ⟨1,by simp⟩
  let widths := fun j=>x j (K j)
  let Fseq := fun j=>comparisonContactLimitCoordinate
    (comparisonSelectedCumulativeMap hc hk hkc hm hM q α (as j) (ho j) (J j))
  let F := comparisonContactLimitCoordinate f
  let w := fun r=>pointSideColumn δ width (F r)
  let moving := fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α
    (as j) (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (widths j) u.val)
  have hwlim : Tendsto widths atTop (𝓝 width) := by
    have he := (BoundedContinuousFunction.lipschitz_eval_const
      (⟨1,by simp⟩ : Icc (0:ℝ) 1)).continuous.tendsto f |>.comp huniform
    have heq : ((fun g : Icc (0:ℝ) 1 →ᵇ ℝ=>g ⟨1,by simp⟩)∘
        (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM q α (as j) (ho j) (J j)))=
        widths := by
      funext j
      exact comparison_selected_cumulative_at_one_eq_width hc hk hkc hm hM q α
        (as j) (ho j) (hend j) (J j) (unit j) (x j) (hstart j) (hmass j)
    rw [heq] at he
    exact he
  have hw : 2*δ ≤ width := ge_of_tendsto hwlim (Eventually.of_forall hwidths)
  have hFlim : ∀ᵐ r ∂volume.restrict A,Tendsto (fun j=>Fseq j r) atTop (𝓝 (F r)) := by
    apply ae_of_all
    intro r
    exact (BoundedContinuousFunction.lipschitz_eval_const
      (projIcc 0 1 (by norm_num) r)).continuous.tendsto f |>.comp huniform
  have hcell' : ∀ᵐ r ∂volume.restrict A,∀ᶠ j in atTop,
      ∃i : Fin ((sampleClockSteps q 0 (as j)).length+1),i ∈ J j ∧ i.val < (as j).length ∧
        r ∈ Ioc
          (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i.val))
          (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) (i.val+1))) ∧
        Fseq j r ∈ Icc (x j (unit j i).val) (x j ((unit j i).val+1)) ∧
        x j ((unit j i).val+1)-x j (unit j i).val ≤ mesh j := by
    filter_upwards [hcell,ae_restrict_mem hA] with r hcr hrA
    have hr01 : r ∈ Icc (0:ℝ) 1 :=
      ⟨ha.le.trans (hAband hrA).1.le,(hAband hrA).2.le.trans hz⟩
    filter_upwards [hcr] with j hj
    obtain ⟨i,hi,hil,hr,hmeet⟩ := hj
    refine ⟨i,hi,hil,hr,?_,?_⟩
    · have hh := comparison_selected_cumulative_mem_unit_interval hc hk hkc hm hM
        q α (as j) (ho j) (hend j) (J j) (unit j) (x j) (hstart j) (hmass j)
        (horder j) i hi hr
      simpa only [Fseq,comparisonContactLimitCoordinate,projIcc_of_mem zero_le_one hr01,
        comparisonSelectedCumulativeMap,BoundedContinuousFunction.mkOfCompact_apply,
        ContinuousMap.coe_mk] using hh
    · rw [←hmass j (unit j i)]
      exact comparison_sampled_contact_geometry_unit_mass_le_mesh hc hk hkc hm hM
        q α (as j) (ho j) (hmesh j) H hopen hU hneg (J j) (unit j) (hpos j)
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
        exact comparisonNativeUnitColumnWeight_point_bound hc hk hkc hm hM q α
          (as j) (ho j) (J j) (unit j) (x j) hδ (hwidths j) (hx j) i hi hil hr hs hsm
      exact (tendsto_zero_iff_norm_tendsto_zero).mpr (by
        simpa only [Real.norm_eq_abs] using
          squeeze_zero' (Eventually.of_forall (fun _=>abs_nonneg _)) hb he)
    have hp := pointSideColumn_varying_tendsto hδ hw widths (fun j=>Fseq j r) (F r)
      hwidths hwlim hFr
    simpa only [sub_add_cancel,zero_add] using hclose.add hp
  have hAf : volume A ≠ ⊤ := ne_top_of_le_ne_top
    (by simp : volume (Icc (0:ℝ) 1) ≠ ⊤) (measure_mono (fun r hr=>
      ⟨ha.le.trans (hAband hr).1.le,(hAband hr).2.le.trans hz⟩))
  have hmb j : ∀ᵐ r ∂volume.restrict A,
      ‖deriv α.val.val r*moving j r‖ ≤ M 1*(2/δ) := by
    apply (ae_restrict_iff' hA).mpr
    exact ae_of_all _ (fun r hr=>by
      have hr01 : r ∈ Ioo (0:ℝ) 1 := ⟨ha.trans (hAband hr).1,(hAband hr).2.trans_le hz⟩
      have hd := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hr01.1 hr01.2)
        (inverseIntegralConstraints_lipschitz hm hM α.property)
      have hh := comparisonNativeUnitColumnWeight_side_bound hc hk hkc hm hM q α
        (as j) (ho j) (J j) (unit j) (x j) (hstart j) (show x j (K j)=widths j from rfl)
        hδ (hwidths j) (hx j) r
      change moving j r ∈ Icc (0:ℝ) (2/δ) at hh
      rw [norm_mul]
      exact mul_le_mul hd (by simpa only [Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2)
        (norm_nonneg _) hM)
  have hL1 := bounded_contact_weights_tendsto_L1 A hAf
    (fun j r=>deriv α.val.val r*moving j r) (fun r=>deriv α.val.val r*w r)
    (fun j=>((stronglyMeasurable_deriv α.val.val).mul
      (comparisonNativeUnitColumnWeight_measurable hc hk hkc hm hM q α (as j)
        (J j) (unit j) _).stronglyMeasurable).aestronglyMeasurable.restrict)
    hmb (hlim.mono (fun r hr=>hr.const_mul (deriv α.val.val r)))
  have hmasslim := comparisonNativeContactColumn_limit_mass hc hk hkc hm hM q α
    ha hz A hA hAband as ho hend K J unit x widths (fun j _=>mesh j)
    hδ hw hwidths hstart (fun _=>rfl) hx hmass hwlim
    (ae_of_all _ (fun _=>hmeshlim)) Fseq F hFlim hcell'
  exact ⟨hwlim,hw,hlim,hL1,hmasslim⟩

theorem comparisonNativeContactColumn_exists_convergent_subseq {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    {a z δ : ℝ} (ha : 0 < a) (hz : z ≤ 1) (hδ : 0 < δ)
    (A : Set ℝ) (hA : MeasurableSet A) (hAband : A⊆Ioo a z)
    (H : ℝ→ℝ) {U : Set ℝ} (hopen : IsOpen U) (hU : U⊆Ioo (0:ℝ) 1)
    (hneg : ∀r ∈ U,H r<0)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hmeshlim : Tendsto mesh atTop (𝓝 0)) (K : ℕ→ℕ)
    (J : ∀j,Finset (Fin ((sampleClockSteps q 0 (as j)).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps q 0 (as j)).length+1)→Fin (K j))
    (x : ℕ→ℕ→ℝ) (hstart : ∀j,x j 0=0)
    (hx : ∀j,∀u : Fin (K j),x j u.val < x j (u.val+1))
    (hmass : ∀j,∀u : Fin (K j),
      physicalSelectedUnitMass (sampleClockSteps q 0 (as j)) (J j) (unit j) u=
        x j (u.val+1)-x j u.val)
    (horder : ∀j,MonotoneOn (unit j) (J j:Set (Fin ((sampleClockSteps q 0 (as j)).length+1))))
    (hwidths : ∀j,2*δ ≤ x j (K j))
    (hpos : ∀j,∀i ∈ J j,0 < pathMassDifferences (sampleClockSteps q 0 (as j)) 0 i)
    (hclass : ∀m,∀i ∈ J m,∀j ∈ J m,unit m i=unit m j↔
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α
        (physicalCutMass 0 (sampleClockSteps q 0 (as m)) i.val))=
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α
        (physicalCutMass 0 (sampleClockSteps q 0 (as m)) j.val)))
    (hcell : ∀ᵐ r ∂volume.restrict A,∀ᶠ j in atTop,
      comparisonNativeContactCellWitness hc hk hkc hm hM q α (as j) (J j) (unit j) H U r) :
    ∃f : Icc (0:ℝ) 1 →ᵇ ℝ,∃φ : ℕ→ℕ,StrictMono φ ∧
      Tendsto (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM
        q α (as (φ j)) (ho (φ j)) (J (φ j))) atTop (𝓝 f) ∧
      (let width := f ⟨1,by simp⟩
       let w := fun r=>pointSideColumn δ width (comparisonContactLimitCoordinate f r)
       let moving := fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α
         (as (φ j)) (J (φ j)) (unit (φ j))
         (fun u=>sideSquareColumn (x (φ j)) δ (x (φ j) (K (φ j))) u.val)
       Tendsto (fun j=>x (φ j) (K (φ j))) atTop (𝓝 width) ∧ 2*δ ≤ width ∧
       (∀ᵐ r ∂volume.restrict A,Tendsto (fun j=>moving j r) atTop (𝓝 (w r))) ∧
       Tendsto (fun j=>∫r in A,|deriv α.val.val r*moving j r-deriv α.val.val r*w r|)
         atTop (𝓝 0) ∧
       (∫r in A,deriv α.val.val r*w r) ≤ 2*Real.log (width/δ)) := by
  obtain ⟨f,φ,hφ,huniform⟩ := comparisonSelectedCumulative_exists_uniform_subseq
    hc hk hkc hm hM q α as ho J
  refine ⟨f,φ,hφ,huniform,?_⟩
  exact comparisonNativeContactColumn_convergence_of_uniform_cumulative hc hk hkc hm hM
    q α ha hz hδ A hA hAband H hopen hU hneg (as∘φ) (mesh∘φ)
    (fun j=>ho (φ j)) (fun j=>hend (φ j)) (fun j=>hmesh (φ j))
    (hmeshlim.comp hφ.tendsto_atTop) (K∘φ) (fun j=>J (φ j))
    (fun j=>unit (φ j)) (fun j=>x (φ j)) (fun j=>hstart (φ j))
    (fun j=>hx (φ j)) (fun j=>hmass (φ j)) (fun j=>horder (φ j))
    (fun j=>hwidths (φ j)) (fun j=>hpos (φ j)) (fun j=>hclass (φ j))
    (hcell.mono (fun r hr=>hφ.tendsto_atTop.eventually hr)) f huniform

theorem comparisonPhysicalNativeContactColumnTrace_eventually
    {N d lam : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0 < d)
    (hnd : 1/N ≤ d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (H : ℝ→ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hzero : ∀ᵐ r,r∈Icc (0:ℝ) 1 → H r=0 →
      radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r=0)
    {a z δ : ℝ} (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1) (hδ : 0 < δ)
    {U : Set ℝ} (hopen : IsOpen U) (hU : U⊆Ioo (0:ℝ) 1) (hneg : ∀r ∈ U,H r<0)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hmeshlim : Tendsto mesh atTop (𝓝 0))
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc a z))
    (hfield : LipschitzOnWith Kh (fun r=>h (α.val.val r)) (Icc a z))
    (K : ℕ→ℕ)
    (J : ∀j,Finset (Fin ((sampleClockSteps
      (comparisonNativeClock hc hk hkc hm hM n b h α d lam) 0 (as j)).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps
      (comparisonNativeClock hc hk hkc hm hM n b h α d lam) 0 (as j)).length+1)→Fin (K j))
    (x : ℕ→ℕ→ℝ) (hstart : ∀j,x j 0=0)
    (hx : ∀j,∀u : Fin (K j),x j u.val < x j (u.val+1))
    (hmass : ∀j,∀u : Fin (K j),physicalSelectedUnitMass (sampleClockSteps
      (comparisonNativeClock hc hk hkc hm hM n b h α d lam) 0 (as j)) (J j) (unit j) u=
        x j (u.val+1)-x j u.val)
    (horder : ∀j,MonotoneOn (unit j) (J j:Set _))
    (hwidths : ∀j,2*δ ≤ x j (K j))
    (hpos : ∀j,∀i ∈ J j,0 < pathMassDifferences (sampleClockSteps
      (comparisonNativeClock hc hk hkc hm hM n b h α d lam) 0 (as j)) 0 i)
    (hclass : ∀m,∀i ∈ J m,∀j ∈ J m,unit m i=unit m j↔
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0
        (sampleClockSteps (comparisonNativeClock hc hk hkc hm hM n b h α d lam) 0 (as m)) i.val))=
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0
        (sampleClockSteps (comparisonNativeClock hc hk hkc hm hM n b h α d lam) 0 (as m)) j.val)))
    (hcell : ∀ᵐ r ∂volume.restrict {r | r∈Ioo a z ∧ H r=0},∀ᶠ j in atTop,
      comparisonNativeContactCellWitness hc hk hkc hm hM
        (comparisonNativeClock hc hk hkc hm hM n b h α d lam)
        α (as j) (J j) (unit j) H U r)
    (f : Icc (0:ℝ) 1 →ᵇ ℝ)
    (huniform : Tendsto (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM
      (comparisonNativeClock hc hk hkc hm hM n b h α d lam) α (as j) (ho j) (J j))
        atTop (𝓝 f))
    (selected bad : ℕ→Set ℝ) (hselected : ∀j,MeasurableSet (selected j))
    (hbad : ∀j,MeasurableSet (bad j))
    (hbadlim : Tendsto (fun j=>volume.real (Ioo a z∩bad j)) atTop (𝓝 0))
    (hcontain : ∀κ>0,∀ᶠ j in atTop,
      ∀r ∈ selected j,r∈Ioo a z → r∉bad j → |H r| ≤ κ)
    {ε : ℝ} (hε : 0 < ε) :
    let width := f ⟨1,by simp⟩
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,(∫r in Ioo a z∩selected j,deriv α.val.val r*
      comparisonNativeUnitColumnWeight hc hk hkc hm hM
        (comparisonNativeClock hc hk hkc hm hM n b h α d lam) α (as j) (J j) (unit j)
        (fun u=>sideSquareColumn (x j) δ (x j (K j)) u.val) r
      ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α (as j) (ho j)) ≤
        ((9*Real.log N)/F)*(2*Real.log (width/δ))+ε := by
  dsimp only
  let q := comparisonNativeClock hc hk hkc hm hM n b h α d lam
  let A := {r | r∈Ioo a z ∧ H r=0}
  let width := f ⟨1,by simp⟩
  let w := fun r=>pointSideColumn δ width (comparisonContactLimitCoordinate f r)
  let moving := fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α
    (as j) (J j) (unit j) (fun u=>sideSquareColumn (x j) δ (x j (K j)) u.val)
  have hHC : ContinuousOn H (Icc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hH.continuousOn
  let He := fun r : ℝ=>H (projIcc (0:ℝ) 1 zero_le_one r)
  have hHe : Continuous He := (continuousOn_iff_continuous_domRestrict.mp hHC).comp continuous_projIcc
  have hA : MeasurableSet A := by
    have heq : A=Ioo a z∩He ⁻¹' {0} := by
      ext r
      have hr01 (hr : r∈Ioo a z) : r∈Icc (0:ℝ) 1 :=
        ⟨ha.le.trans hr.1.le,hr.2.le.trans hz⟩
      constructor <;> intro hr <;> refine ⟨hr.1,?_⟩ <;>
        simpa only [He,projIcc_of_mem zero_le_one (hr01 hr.1),mem_preimage,mem_singleton_iff] using hr.2
    rw [heq]
    exact measurableSet_Ioo.inter (hHe.measurable (measurableSet_singleton 0))
  obtain ⟨_,hw,_,hL1,hmasslog⟩ := comparisonNativeContactColumn_convergence_of_uniform_cumulative
    hc hk hkc hm hM q α ha hz hδ A hA (fun _ hr=>hr.1) H hopen hU hneg
    as mesh ho hend hmesh hmeshlim K J unit x hstart hx hmass horder hwidths hpos hclass
    hcell f huniform
  let B := 2*(δ⁻¹)^2*(width-2*δ)+2/δ
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hwmeas : Measurable w :=
    ((pointSideColumn_continuous hδ hw).comp (comparisonContactLimitCoordinate_continuous f)).measurable
  have hw0 r : 0 ≤ w r := pointSideColumn_nonneg hw _
  have hwb r : ‖w r‖ ≤ B := (pointSideColumn_coarse_norm_bound hδ hw _).trans
    (le_add_of_nonneg_right (by positivity))
  have hmove j : Measurable (moving j) := comparisonNativeUnitColumnWeight_measurable
    hc hk hkc hm hM q α (as j) (J j) (unit j) _
  have hmb' j r : moving j r ∈ Icc (0:ℝ) (2/δ) :=
    comparisonNativeUnitColumnWeight_side_bound hc hk hkc hm hM q α (as j) (ho j)
      (J j) (unit j) (x j) (hstart j) rfl hδ (hwidths j) (hx j) r
  have hmb j r : ‖moving j r‖ ≤ B := by
    rw [Real.norm_eq_abs,abs_of_nonneg (hmb' j r).1]
    exact (hmb' j r).2.trans (by dsimp only [B];nlinarith [sq_nonneg (δ⁻¹)])
  have ht := comparisonPhysicalContactOnlyVaryingTrace_eventually hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α H hH hzero
    as mesh ho hend hmesh hmesh0 hmeshlim ha haz hz Kb Kh hparent hfield
    w hwmeas hw0 moving hmove hwb hmb hB (fun j r=>(hmb' j r).1)
    hL1 selected bad hselected hbad hbadlim hcontain hε
  have hFpos : 0 < (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z) := by
    have hlogpos : 0 < Real.log N := lt_of_lt_of_le zero_lt_one hlog
    have hstrength := laplaceComparisonStrength_pos d hlam z
    positivity
  have hcoef : 0 ≤ (9*Real.log N)/
      ((n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)) :=
    div_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans hlog)) hFpos.le
  filter_upwards [ht] with j hj
  exact hj.trans (add_le_add (mul_le_mul_of_nonneg_left hmasslog hcoef) le_rfl)

theorem comparisonPhysicalNativeContactColumnTrace_exists_subseq
    {N d lam : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0 < d)
    (hnd : 1/N ≤ d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (H : ℝ→ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hzero : ∀ᵐ r,r∈Icc (0:ℝ) 1 → H r=0 →
      radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r=0)
    {a z δ : ℝ} (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1) (hδ : 0 < δ)
    {U : Set ℝ} (hopen : IsOpen U) (hU : U⊆Ioo (0:ℝ) 1) (hneg : ∀r ∈ U,H r<0)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hmeshlim : Tendsto mesh atTop (𝓝 0))
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc a z))
    (hfield : LipschitzOnWith Kh (fun r=>h (α.val.val r)) (Icc a z))
    (K : ℕ→ℕ)
    (J : ∀j,Finset (Fin ((sampleClockSteps
      (comparisonNativeClock hc hk hkc hm hM n b h α d lam) 0 (as j)).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps
      (comparisonNativeClock hc hk hkc hm hM n b h α d lam) 0 (as j)).length+1)→Fin (K j))
    (x : ℕ→ℕ→ℝ) (hstart : ∀j,x j 0=0)
    (hx : ∀j,∀u : Fin (K j),x j u.val < x j (u.val+1))
    (hmass : ∀j,∀u : Fin (K j),physicalSelectedUnitMass (sampleClockSteps
      (comparisonNativeClock hc hk hkc hm hM n b h α d lam) 0 (as j)) (J j) (unit j) u=
        x j (u.val+1)-x j u.val)
    (horder : ∀j,MonotoneOn (unit j) (J j:Set _))
    (hwidths : ∀j,2*δ ≤ x j (K j))
    (hpos : ∀j,∀i ∈ J j,0 < pathMassDifferences (sampleClockSteps
      (comparisonNativeClock hc hk hkc hm hM n b h α d lam) 0 (as j)) 0 i)
    (hclass : ∀m,∀i ∈ J m,∀j ∈ J m,unit m i=unit m j↔
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0
        (sampleClockSteps (comparisonNativeClock hc hk hkc hm hM n b h α d lam) 0 (as m)) i.val))=
      wholeUnit U (comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0
        (sampleClockSteps (comparisonNativeClock hc hk hkc hm hM n b h α d lam) 0 (as m)) j.val)))
    (hcell : ∀ᵐ r ∂volume.restrict {r | r∈Ioo a z ∧ H r=0},∀ᶠ j in atTop,
      comparisonNativeContactCellWitness hc hk hkc hm hM
        (comparisonNativeClock hc hk hkc hm hM n b h α d lam)
        α (as j) (J j) (unit j) H U r)
    (selected bad : ℕ→Set ℝ) (hselected : ∀j,MeasurableSet (selected j))
    (hbad : ∀j,MeasurableSet (bad j))
    (hbadlim : Tendsto (fun j=>volume.real (Ioo a z∩bad j)) atTop (𝓝 0))
    (hcontain : ∀κ>0,∀ᶠ j in atTop,
      ∀r ∈ selected j,r∈Ioo a z → r∉bad j → |H r| ≤ κ)
 :
    ∃f : Icc (0:ℝ) 1 →ᵇ ℝ,∃φ : ℕ→ℕ,StrictMono φ ∧
      Tendsto (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM
        (comparisonNativeClock hc hk hkc hm hM n b h α d lam)
        α (as (φ j)) (ho (φ j)) (J (φ j))) atTop (𝓝 f) ∧
      (∀ε>0,
        let width := f ⟨1,by simp⟩
        let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
        ∀ᶠ j in atTop,(∫r in Ioo a z∩selected (φ j),deriv α.val.val r*
          comparisonNativeUnitColumnWeight hc hk hkc hm hM
            (comparisonNativeClock hc hk hkc hm hM n b h α d lam)
            α (as (φ j)) (J (φ j)) (unit (φ j))
            (fun u=>sideSquareColumn (x (φ j)) δ (x (φ j) (K (φ j))) u.val) r
          ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h
            α (as (φ j)) (ho (φ j))) ≤
            ((9*Real.log N)/F)*(2*Real.log (width/δ))+ε) := by
  let q := comparisonNativeClock hc hk hkc hm hM n b h α d lam
  obtain ⟨f,φ,hφ,huniform⟩ := comparisonSelectedCumulative_exists_uniform_subseq
    hc hk hkc hm hM q α as ho J
  refine ⟨f,φ,hφ,huniform,?_⟩
  intro ε hε
  exact comparisonPhysicalNativeContactColumnTrace_eventually hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α H hH hzero
    ha haz hz hδ hopen hU hneg (as∘φ) (mesh∘φ)
    (fun j=>ho (φ j)) (fun j=>hend (φ j)) (fun j=>hmesh (φ j))
    (fun j=>hmesh0 (φ j)) (hmeshlim.comp hφ.tendsto_atTop)
    Kb Kh hparent hfield (K∘φ) (fun j=>J (φ j)) (fun j=>unit (φ j))
    (fun j=>x (φ j)) (fun j=>hstart (φ j)) (fun j=>hx (φ j))
    (fun j=>hmass (φ j)) (fun j=>horder (φ j)) (fun j=>hwidths (φ j))
    (fun j=>hpos (φ j)) (fun j=>hclass (φ j))
    (hcell.mono (fun r hr=>hφ.tendsto_atTop.eventually hr)) f huniform
    (selected∘φ) (bad∘φ) (fun j=>hselected (φ j)) (fun j=>hbad (φ j))
    (hbadlim.comp hφ.tendsto_atTop)
    (fun κ hκ=>hφ.tendsto_atTop.eventually (hcontain κ hκ)) hε

end
end OAI.SKFluctuations.LaplaceWindowFormalization
