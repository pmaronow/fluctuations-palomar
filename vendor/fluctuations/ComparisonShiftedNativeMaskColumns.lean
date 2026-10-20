module

public import ComparisonShiftedNativeMovingWeights
public import ComparisonShiftedNativeColumns
public import ComparisonNativeKeptUnionMass
public import ComparisonNativeConstructedBandFrame

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
attribute [local instance] Classical.propDecidable
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem unitColumn_on_original_cell (as : List PositiveMass) (ho : MassOrdered 0 as)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K) (col : Fin K→ℝ)
    (i : Fin ((sampleClockSteps m.q 0 as).length+1)) (hi : i.val< as.length)
    {r : ℝ} (hr : r∈Ioc (m.R (partitionPoint 0 as i.val))
      (m.R (partitionPoint 0 as (i.val+1)))) :
    m.unitColumn as J unit col r=if i∈J then col (unit i) else 0 := by
  rw [unitColumn,radiusCellEnergyDensity_on_original_cell _ m.R_monotone as ho _ hi hr,
    nativeSelectedColumn_atIndex]

theorem unitColumn_zero_of_not_support (as : List PositiveMass) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K) (col : Fin K→ℝ)
    {r : ℝ} (hr : r∉NativeSelectedMask.finiteSupport
      (fun i=>m.R (partitionPoint 0 as i)) J) : m.unitColumn as J unit col r=0 := by
  rw [unitColumn,radiusCellEnergyDensity_eq_finite_sum]
  unfold finiteRadiusCellDensity
  apply Finset.sum_eq_zero
  intro i hi
  have hil : i< as.length:=Finset.mem_range.mp hi
  let ii : Fin ((sampleClockSteps m.q 0 as).length+1):=
    ⟨i,by simpa only [sampleClockSteps_length] using Nat.lt_succ_of_lt hil⟩
  have he : nativeSelectedColumn J unit col i=if ii∈J then col (unit ii) else 0:=
    nativeSelectedColumn_atIndex J unit col ii
  by_cases hsel : ii∈J
  · have hn : r∉Ioc (m.R (partitionPoint 0 as i)) (m.R (partitionPoint 0 as (i+1))):=
      fun h=>hr ⟨ii,hsel,h⟩
    rw [indicator_of_notMem hn]
  · simp [he,hsel,Set.indicator_apply]

theorem unitColumn_binary_eq_support (as : List PositiveMass) (ho : MassOrdered 0 as)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K)
    (hJ : ∀i∈J,i.val< as.length) (r : ℝ) :
    m.unitColumn as J unit (fun _=>1) r=
      (NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 as i)) J).indicator
        (fun _=>1) r := by
  by_cases hs : r∈NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 as i)) J
  · obtain ⟨i,hi,hri⟩:=hs
    rw [m.unitColumn_on_original_cell as ho J unit (fun _=>1) i (hJ i hi) hri,
      ite_eq_left hi,indicator_of_mem (show r∈NativeSelectedMask.finiteSupport
        (fun i=>m.R (partitionPoint 0 as i)) J from ⟨i,hi,hri⟩)]
  · rw [m.unitColumn_zero_of_not_support as J unit (fun _=>1) hs,indicator_of_notMem hs]

theorem unitColumn_support_band (as : List PositiveMass) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K) (col : Fin K→ℝ)
    {ag zg : ℝ}
    (hleft : ∀i∈J,ag≤ m.R (partitionPoint 0 as i.val))
    (hright : ∀i∈J,m.R (partitionPoint 0 as (i.val+1))≤ zg) :
    ∀ᵐr,r∉Ioo ag zg→m.unitColumn as J unit col r=0 := by
  filter_upwards [volume.ae_ne zg] with r hrzg hr
  apply m.unitColumn_zero_of_not_support
  rintro ⟨i,hi,hri⟩
  exact hr ⟨(hleft i hi).trans_lt hri.1,
    lt_of_le_of_ne (hri.2.trans (hright i hi)) hrzg⟩

theorem binary_column_L1_of_support_eventually
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (Ks : ℕ→ℕ)
    (J : (j : ℕ)→Finset (Fin ((sampleClockSteps m.q 0 (as j)).length+1)))
    (unit : (j : ℕ)→Fin ((sampleClockSteps m.q 0 (as j)).length+1)→Fin (Ks j))
    (hJ : ∀j,∀i∈J j,i.val<(as j).length)
    {ag zg : ℝ} (F : Set ℝ)
    (hmem : ∀ᵐr∂volume.restrict (Ioo ag zg),∀ᶠj in atTop,
      (r∈NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 (as j) i)) (J j) ↔r∈F)) :
    (∀ᵐr∂volume.restrict (Ioo ag zg),Tendsto
      (fun j=>m.unitColumn (as j) (J j) (unit j) (fun _=>1) r) atTop
        (𝓝 (F.indicator (fun _=>1) r))) ∧
    Tendsto (fun j=>∫r in Ioo ag zg,
      |m.unitColumn (as j) (J j) (unit j) (fun _=>1) r-F.indicator (fun _=>1) r|)
      atTop (𝓝 0) := by
  have hp : ∀ᵐr∂volume.restrict (Ioo ag zg),Tendsto
      (fun j=>m.unitColumn (as j) (J j) (unit j) (fun _=>1) r) atTop
        (𝓝 (F.indicator (fun _=>1) r)):=by
    filter_upwards [hmem] with r hr
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [hr] with j hj
    rw [m.unitColumn_binary_eq_support (as j) (ho j) (J j) (unit j) (hJ j) r]
    simp only [Set.indicator_apply,hj]
  refine ⟨hp,?_⟩
  apply bounded_contact_weights_tendsto_L1 (B:=1) (Ioo ag zg) (by simp)
    _ _ (fun j=>(m.unitColumn_measurable _ _ _ _).aestronglyMeasurable.restrict) _ hp
  intro j
  apply ae_of_all
  intro r
  rw [m.unitColumn_binary_eq_support (as j) (ho j) (J j) (unit j) (hJ j) r]
  simp only [Set.indicator_apply]
  split_ifs <;> norm_num

theorem binary_density_L1_of_support_eventually
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (Ks : ℕ→ℕ)
    (J : (j : ℕ)→Finset (Fin ((sampleClockSteps m.q 0 (as j)).length+1)))
    (unit : (j : ℕ)→Fin ((sampleClockSteps m.q 0 (as j)).length+1)→Fin (Ks j))
    (hJ : ∀j,∀i∈J j,i.val<(as j).length)
    {ag zg : ℝ} (hag : m.rmin< ag) (hzg : zg≤1) (F : Set ℝ) (hF : MeasurableSet F)
    (hmem : ∀ᵐr∂volume.restrict (Ioo ag zg),∀ᶠj in atTop,
      (r∈NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 (as j) i)) (J j) ↔r∈F)) :
    Tendsto (fun j=>∫r in Ioo ag zg,
      |deriv m.alpha.val.val r*m.unitColumn (as j) (J j) (unit j) (fun _=>1) r-
        deriv m.alpha.val.val r*F.indicator (fun _=>1) r|) atTop (𝓝 0) := by
  apply m.inverse_weight_L1_tendsto hag hzg (F.indicator (fun _=>1))
    (measurable_const.indicator hF)
    (fun j=>m.unitColumn (as j) (J j) (unit j) (fun _=>1))
    (fun j=>m.unitColumn_measurable _ _ _ _) (B:=1)
  · intro r
    simp only [Set.indicator_apply]
    split_ifs <;> norm_num
  · intro j r
    rw [m.unitColumn_binary_eq_support (as j) (ho j) (J j) (unit j) (hJ j) r]
    simp only [Set.indicator_apply]
    split_ifs <;> norm_num
  · exact (m.binary_column_L1_of_support_eventually as ho Ks J unit hJ F hmem).2

theorem binary_mass_tendsto_of_support_eventually
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1)
    (J : (j : ℕ)→Finset (Fin ((sampleClockSteps m.q 0 (as j)).length+1)))
    (hJ : ∀j,∀i∈J j,i.val<(as j).length)
    (hhigh : ∀j,∀i∈J j,m.u0≤ partitionPoint 0 (as j) i.val)
    {ag zg : ℝ} (hag : m.rmin< ag) (hzg : zg≤1)
    (hleft : ∀j,∀i∈J j,ag≤ m.R (partitionPoint 0 (as j) i.val))
    (hright : ∀j,∀i∈J j,m.R (partitionPoint 0 (as j) (i.val+1))≤ zg)
    (F : Set ℝ) (hF : MeasurableSet F) (hFD : F⊆Ioo ag zg)
    (hmem : ∀ᵐr∂volume.restrict (Ioo ag zg),∀ᶠj in atTop,
      (r∈NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 (as j) i)) (J j) ↔r∈F)) :
    Tendsto (fun j=>physicalWindowMass (sampleClockSteps m.q 0 (as j)) 0 (J j))
      atTop (𝓝 (∫r in F,deriv m.alpha.val.val r)) := by
  let moving:=fun j=>m.unitColumn (as j) (J j) (fun _=>(0:Fin 1)) (fun _=>1)
  let fixed : ℝ→ℝ:=F.indicator (fun _ : ℝ=>(1:ℝ))
  have hfixedB r : ‖fixed r‖≤(1:ℝ):=by
    simp only [fixed,Set.indicator_apply]
    split_ifs <;> norm_num
  have hmoveB j r : ‖moving j r‖≤(1:ℝ):=by
    dsimp only [moving]
    rw [m.unitColumn_binary_eq_support (as j) (ho j) (J j) _ (hJ j) r]
    simp only [Set.indicator_apply]
    split_ifs <;> norm_num
  have hfI:=m.radiusWeight_integrableOn hag hzg (Ioo ag zg) measurableSet_Ioo
    (Subset.refl _) fixed (measurable_const.indicator hF) hfixedB
  have hmI j:=m.radiusWeight_integrableOn hag hzg (Ioo ag zg) measurableSet_Ioo
    (Subset.refl _) (moving j) (m.unitColumn_measurable _ _ _ _) (hmoveB j)
  have ht:=m.binary_density_L1_of_support_eventually as ho (fun _=>1) J
    (fun _ _=>(0:Fin 1)) hJ hag hzg F hF hmem
  have hglobal j : (∫r in Ioo ag zg,deriv m.alpha.val.val r*moving j r)=
      ∫r,deriv m.alpha.val.val r*moving j r:=by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [m.unitColumn_support_band (as j) (J j) (fun _=>(0:Fin 1))
      (fun _=>1) (hleft j) (hright j)] with r hr hrd
    dsimp only [moving]
    rw [hr hrd,mul_zero]
  have hmass j : (∫r in Ioo ag zg,deriv m.alpha.val.val r*moving j r)=
      physicalWindowMass (sampleClockSteps m.q 0 (as j)) 0 (J j):=by
    rw [hglobal j,m.unitColumn_mass (as j) (ho j) (he j) (J j) _ _ (hhigh j),Fin.sum_univ_one]
    simp only [mul_one,physicalSelectedUnitMass,and_true]
    exact sum_physicalSelectedCellMass_eq_window _ _
  have hfixedEq : (∫r in Ioo ag zg,deriv m.alpha.val.val r*fixed r)=
      ∫r in F,deriv m.alpha.val.val r:=by
    have HE : (fun r=>deriv m.alpha.val.val r*fixed r)=F.indicator (deriv m.alpha.val.val):=by
      funext r
      by_cases hr : r∈F <;> simp [fixed,hr]
    rw [HE,integral_indicator hF,Measure.restrict_restrict hF,inter_eq_left.mpr hFD]
  apply (tendsto_iff_dist_tendsto_zero).mpr
  change Tendsto (fun j=>|physicalWindowMass (sampleClockSteps m.q 0 (as j)) 0 (J j)-
    (∫r in F,deriv m.alpha.val.val r)|) atTop (𝓝 0)
  apply squeeze_zero (fun _=>abs_nonneg _) _ ht
  intro j
  rw [←hmass j,←hfixedEq,←integral_sub (hmI j) hfI]
  exact abs_integral_le_integral_abs

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
