module

public import ComparisonNativeWholeCapGroupAssignment

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3800000
attribute [local instance] Classical.propDecidable

abbrev nativeActualContactSet (m : NativeBandModel) : Set ℝ :=
  Icc (0:ℝ) 1 ∩ m.H ⁻¹' {0}

theorem nativeActualContactSet_measurable (m : NativeBandModel) : MeasurableSet (nativeActualContactSet m) := by
  have hc : ContinuousOn m.H (Icc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using m.hH.continuousOn
  exact (hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton).measurableSet

theorem nativeActualThermal_mask_integrable (m : NativeBandModel) (A : Set ℝ)
    (hA : MeasurableSet A) :
    IntervalIntegrable (fun u=>A.indicator (fun _=>1) (m.R u)*m.thermal u) volume 0 1 := by
  have had := comparisonVariableEndpoint_clocks_admissible m.hc m.hk m.hkc m.hm m.hM
    m.b m.h m.hd.ne' m.hlam.le m.hlb m.hb m.hh m.hh0 m.alpha
  have hthermal := physicalOrderedThermal_intervalIntegrable m.n m.bf m.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
  apply intervalIntegrable_bounded_measurable_mul
    ((measurable_const.indicator hA).comp
      (comparisonSweepQuantile_continuous m.hc m.hk m.hkc m.hm m.hM m.alpha).measurable)
    (show (0:ℝ)≤1 by norm_num) _ hthermal
  intro u hu
  by_cases hs:m.R u∈A <;> simp [hs]

theorem nativeActualThermal_nonneg (m : NativeBandModel) {u:ℝ}
    (hu:u∈Ioc (0:ℝ) 1) : 0≤ m.thermal u := by
  have had := comparisonVariableEndpoint_clocks_admissible m.hc m.hk m.hkc m.hm m.hM
    m.b m.h m.hd.ne' m.hlam.le m.hlb m.hb m.hh m.hh0 m.alpha
  have hp := orderedPath_SK_bounds (m.n+1) (by omega) m.bf m.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) hu
  exact sub_nonneg.mpr hp.2.2.1

private theorem indicator_cover_four (A B C D E : Set ℝ) (r:ℝ)
    (h : r ∈ A → r ∈ B ∨ r ∈ C ∨ r ∈ D ∨ r ∈ E) :
    A.indicator (fun _=>(1:ℝ)) r≤ B.indicator (fun _=>1) r+C.indicator (fun _=>1) r+
      D.indicator (fun _=>1) r+E.indicator (fun _=>1) r := by
  by_cases ha:r∈A <;> by_cases hb:r∈B <;> by_cases hc:r∈C <;>
    by_cases hd:r∈D <;> by_cases he:r∈E <;> simp_all [Set.indicator_apply] <;> norm_num

theorem actual_native_finite_cap_thermal_cover {ι : Type*} [Fintype ι]
    (m : NativeBandModel) (c : ι→NativeActualCapInterval m)
    (hd : Pairwise (fun i j=>Disjoint (Ioo (c i).a (c i).z) (Ioo (c j).a (c j).z)))
    (A : Set ℝ) (hA : MeasurableSet A) :
    (∫u in 0..1,(A∩((⋃i,Ioo (c i).a (c i).z)∪nativeActualContactSet m)).indicator
      (fun _=>1) (m.R u)*m.thermal u)≤
      (∫u in 0..1,(A∩nativeActualContactSet m).indicator (fun _=>1) (m.R u)*m.thermal u)+
      (∫u in 0..1,(nativeActualComparableCapUnion m c).indicator (fun _=>1) (m.R u)*m.thermal u)+
      (∑p:nativeActualBroadSliceIndex m c,
        ∫u in 0..1,(nativeActualBroadSlice m c p).indicator (fun _=>1) (m.R u)*m.thermal u)+
      (∫u in 0..min (8*m.U) 1,m.thermal u) := by
  let full := A∩((⋃i,Ioo (c i).a (c i).z)∪nativeActualContactSet m)
  let contact := A∩nativeActualContactSet m
  let comp := nativeActualComparableCapUnion m c
  let broad := ⋃p:nativeActualBroadSliceIndex m c,nativeActualBroadSlice m c p
  let low := nativeBroadNearZero m
  have hcontact : MeasurableSet contact := hA.inter (nativeActualContactSet_measurable m)
  have hcomp : MeasurableSet comp := MeasurableSet.iUnion (fun _=>measurableSet_Ioo)
  have hbroad : MeasurableSet broad := MeasurableSet.iUnion (fun _=>measurableSet_Ioo)
  have hlow : MeasurableSet low := measurableSet_Ioo
  have hfull : MeasurableSet full := hA.inter ((MeasurableSet.iUnion (fun _=>measurableSet_Ioo)).union
    (nativeActualContactSet_measurable m))
  have hiF := nativeActualThermal_mask_integrable m full hfull
  have hiC := nativeActualThermal_mask_integrable m contact hcontact
  have hiComp := nativeActualThermal_mask_integrable m comp hcomp
  have hiB := nativeActualThermal_mask_integrable m broad hbroad
  have hiL := nativeActualThermal_mask_integrable m low hlow
  have hpoint : ∀ᵐ u∂volume.restrict (Ioc (0:ℝ) 1),
      full.indicator (fun _=>1) (m.R u)*m.thermal u≤
      contact.indicator (fun _=>1) (m.R u)*m.thermal u+
      comp.indicator (fun _=>1) (m.R u)*m.thermal u+
      broad.indicator (fun _=>1) (m.R u)*m.thermal u+
      low.indicator (fun _=>1) (m.R u)*m.thermal u := by
    have hc := actual_native_finite_cap_cover_ae m c
    rw [←restrict_Ioc_eq_restrict_Icc] at hc
    filter_upwards [ae_restrict_mem measurableSet_Ioc,hc] with u hu hcover
    have hg : m.R u∈full→m.R u∈contact ∨ m.R u∈comp ∨ m.R u∈broad ∨ m.R u∈low := by
      rintro ⟨ha,hcap|hzero⟩
      · rcases hcover hcap with hl|hcomp|⟨p,hp⟩
        · exact Or.inr (Or.inr (Or.inr hl))
        · exact Or.inr (Or.inl hcomp)
        · exact Or.inr (Or.inr (Or.inl (mem_iUnion.mpr ⟨p,hp⟩)))
      · exact Or.inl ⟨ha,hzero⟩
    have hs := mul_le_mul_of_nonneg_right (indicator_cover_four full contact comp broad low (m.R u) hg)
      (nativeActualThermal_nonneg m hu)
    simpa only [add_mul] using hs
  have hbudget : (∫u in 0..1,full.indicator (fun _=>1) (m.R u)*m.thermal u)≤
      (∫u in 0..1,contact.indicator (fun _=>1) (m.R u)*m.thermal u)+
      (∫u in 0..1,comp.indicator (fun _=>1) (m.R u)*m.thermal u)+
      (∫u in 0..1,broad.indicator (fun _=>1) (m.R u)*m.thermal u)+
      (∫u in 0..1,low.indicator (fun _=>1) (m.R u)*m.thermal u) := by
    rw [←intervalIntegral.integral_add hiC hiComp,←intervalIntegral.integral_add (hiC.add hiComp) hiB,
      ←intervalIntegral.integral_add ((hiC.add hiComp).add hiB) hiL]
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact integral_mono_ae ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hiF)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (((hiC.add hiComp).add hiB).add hiL)) hpoint
  have heq : (∫u in 0..1,broad.indicator (fun _=>1) (m.R u)*m.thermal u)=
      ∑p:nativeActualBroadSliceIndex m c,
        ∫u in 0..1,(nativeActualBroadSlice m c p).indicator (fun _=>1) (m.R u)*m.thermal u :=
    nativeActualThermal_disjoint_union m (nativeActualBroadSlice m c) (fun _=>measurableSet_Ioo)
      (nativeActualBroadSlice_disjoint m c hd)
  rw [heq] at hbudget
  simpa only [full,contact,comp,low,nativeBroadNearZero_thermal_eq_initial_mass] using hbudget

end OAI.SKFluctuations.LaplaceWindowFormalization
