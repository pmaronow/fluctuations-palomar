module

public import ComparisonNativeBroadError
public import ComparisonNativeNegativeCapFamily

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4200000
attribute [local instance] Classical.propDecidable

theorem nativeActualError_intervalIntegrable (m:NativeBandModel) :
    IntervalIntegrable m.comparisonErrorDensity volume 0 1 := by
  have had := comparisonVariableEndpoint_clocks_admissible m.hc m.hk m.hkc m.hm m.hM
    m.b m.h m.hd.ne' m.hlam.le m.hlb m.hb m.hh m.hh0 m.alpha
  have hquad := actual_quadratic_integrable (m.n+1) (by omega) m.bf m.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) m.R
    ((comparisonSweepQuantile_monotone m.hc m.hk m.hkc m.hm m.hM m.alpha).monotoneOn _)
    (fun u _=>(comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha u).1)
  have he : Measurable (fun u=>laplaceComparisonStrength m.d m.lam (m.R u)) :=
    (laplaceComparisonStrength_contDiff m.d m.lam).continuous.measurable.comp
      (comparisonSweepQuantile_continuous m.hc m.hk m.hkc m.hm m.hM m.alpha).measurable
  exact intervalIntegrable_bounded_measurable_mul he m.hlam.le
    (fun u _=>⟨(laplaceComparisonStrength_pos m.d m.hlam _).le,
      laplaceComparisonStrength_le m.d m.hlam.le _⟩) (hquad.1.add hquad.2)

 theorem nativeActualError_mask_integrable (m:NativeBandModel) (A:Set ℝ) (hA:MeasurableSet A) :
    IntervalIntegrable (fun u=>A.indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u) volume 0 1 := by
  apply intervalIntegrable_bounded_measurable_mul
    ((measurable_const.indicator hA).comp
      (comparisonSweepQuantile_continuous m.hc m.hk m.hkc m.hm m.hM m.alpha).measurable)
    zero_le_one _ (nativeActualError_intervalIntegrable m)
  intro u hu
  by_cases hs:m.R u∈A <;> simp [hs]

theorem nativeActualError_nonneg (m:NativeBandModel) {u:ℝ} (hu:u∈Ioc (0:ℝ) 1) :
    0≤ m.comparisonErrorDensity u :=
  mul_nonneg (laplaceComparisonStrength_pos m.d m.hlam _).le
    (add_nonneg (nativeActualThermal_nonneg m hu) (sq_nonneg _))

theorem nativeActualIntegral_disjoint_union {ι:Type*} [Fintype ι]
    (m:NativeBandModel) (A:ι→Set ℝ) (hA:∀i,MeasurableSet (A i))
    (hd:Pairwise (fun i j=>Disjoint (A i) (A j))) (T:ℝ→ℝ)
    (hT:IntervalIntegrable T volume 0 1) :
    (∫u in 0..1,(⋃i,A i).indicator (fun _=>1) (m.R u)*T u)=
      ∑i,∫u in 0..1,(A i).indicator (fun _=>1) (m.R u)*T u := by
  have hi i : IntervalIntegrable (fun u=>(A i).indicator (fun _=>1) (m.R u)*T u) volume 0 1 := by
    apply intervalIntegrable_bounded_measurable_mul
      ((measurable_const.indicator (hA i)).comp
        (comparisonSweepQuantile_continuous m.hc m.hk m.hkc m.hm m.hM m.alpha).measurable)
      zero_le_one _ hT
    intro u hu
    by_cases hs:m.R u∈A i <;> simp [hs]
  simp_rw [native_indicator_iUnion_eq_sum A hd,Finset.sum_mul]
  exact intervalIntegral.integral_finset_sum (fun i _=>hi i)

theorem nativeBroadNearZero_integral_eq_initial_mass (m : NativeBandModel) (T : ℝ→ℝ) :
    (∫u in 0..1,(nativeBroadNearZero m).indicator (fun _=>1) (m.R u)*T u)=
      ∫u in 0..min (8*m.U) 1,T u := by
  let v := min (8*m.U) 1
  have hv : v∈Icc (0:ℝ) 1 := ⟨(lt_min (mul_pos (by norm_num) m.hU) zero_lt_one).le,min_le_right _ _⟩
  rw [←intervalIntegral.integral_indicator hv]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne v] with u huv hu
  have hu : u∈Ioc (0:ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using hu
  have hu01 : u∈Icc (0:ℝ) 1 := Ioc_subset_Icc_self hu
  have hm := native_mass_slice_quantile_mem m (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) hv hu01
  change (m.R u∈nativeBroadNearZero m)↔u∈Ioo (0:ℝ) v at hm
  by_cases hle:u≤ v
  · have hmem := hm.mpr ⟨hu.1,lt_of_le_of_ne hle huv⟩
    simp only [indicator_of_mem hmem,one_mul,indicator_of_mem (show u∈{x | x≤ v} from hle)]
  · have hnot : m.R u∉nativeBroadNearZero m := fun hh=>hle (hm.mp hh).2.le
    simp only [indicator_of_notMem hnot,zero_mul,indicator_of_notMem (show u∉{x | x≤ v} from hle)]

private theorem error_indicator_cover_four (A B C D E : Set ℝ) (r:ℝ)
    (h : r ∈ A → r ∈ B ∨ r ∈ C ∨ r ∈ D ∨ r ∈ E) :
    A.indicator (fun _=>(1:ℝ)) r≤ B.indicator (fun _=>1) r+C.indicator (fun _=>1) r+
      D.indicator (fun _=>1) r+E.indicator (fun _=>1) r := by
  by_cases ha:r∈A <;> by_cases hb:r∈B <;> by_cases hc:r∈C <;>
    by_cases hd:r∈D <;> by_cases he:r∈E <;> simp_all [Set.indicator_apply] <;> norm_num

theorem actual_native_finite_cap_error_cover {ι : Type*} [Fintype ι]
    (m : NativeBandModel) (c : ι→NativeActualCapInterval m)
    (hd : Pairwise (fun i j=>Disjoint (Ioo (c i).a (c i).z) (Ioo (c j).a (c j).z)))
    (A : Set ℝ) (hA : MeasurableSet A) :
    (∫u in 0..1,(A∩((⋃i,Ioo (c i).a (c i).z)∪nativeActualContactSet m)).indicator
      (fun _=>1) (m.R u)*m.comparisonErrorDensity u)≤
      (∫u in 0..1,(A∩nativeActualContactSet m).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u)+
      (∫u in 0..1,(nativeActualComparableCapUnion m c).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u)+
      (∑p:nativeActualBroadSliceIndex m c,
        ∫u in 0..1,(nativeActualBroadSlice m c p).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u)+
      (∫u in 0..min (8*m.U) 1,m.comparisonErrorDensity u) := by
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
  have hiF := nativeActualError_mask_integrable m full hfull
  have hiC := nativeActualError_mask_integrable m contact hcontact
  have hiComp := nativeActualError_mask_integrable m comp hcomp
  have hiB := nativeActualError_mask_integrable m broad hbroad
  have hiL := nativeActualError_mask_integrable m low hlow
  have hpoint : ∀ᵐ u∂volume.restrict (Ioc (0:ℝ) 1),
      full.indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u≤
      contact.indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u+
      comp.indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u+
      broad.indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u+
      low.indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u := by
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
    have hs := mul_le_mul_of_nonneg_right (error_indicator_cover_four full contact comp broad low (m.R u) hg)
      (nativeActualError_nonneg m hu)
    simpa only [add_mul] using hs
  have hbudget : (∫u in 0..1,full.indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u)≤
      (∫u in 0..1,contact.indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u)+
      (∫u in 0..1,comp.indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u)+
      (∫u in 0..1,broad.indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u)+
      (∫u in 0..1,low.indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u) := by
    rw [←intervalIntegral.integral_add hiC hiComp,←intervalIntegral.integral_add (hiC.add hiComp) hiB,
      ←intervalIntegral.integral_add ((hiC.add hiComp).add hiB) hiL]
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact integral_mono_ae ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hiF)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (((hiC.add hiComp).add hiB).add hiL)) hpoint
  have heq : (∫u in 0..1,broad.indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u)=
      ∑p:nativeActualBroadSliceIndex m c,
        ∫u in 0..1,(nativeActualBroadSlice m c p).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u :=
    nativeActualIntegral_disjoint_union m (nativeActualBroadSlice m c) (fun _=>measurableSet_Ioo)
      (nativeActualBroadSlice_disjoint m c hd) m.comparisonErrorDensity (nativeActualError_intervalIntegrable m)
  rw [heq] at hbudget
  simpa only [full,contact,comp,low,nativeBroadNearZero_integral_eq_initial_mass m m.comparisonErrorDensity] using hbudget

theorem actual_native_negative_cap_family_error_cover (m : NativeBandModel)
    (F : Finset (ordConnectedSection (nativeNegativeSet m))) (hshort : nativeCapTravel m<1) :
    ∃c:F→NativeActualCapInterval m,
      (∀i,(m.H (c i).a=0 ∧ m.H (c i).z=0) ∨ ((c i).a=0 ∧ m.H (c i).z=0) ∨
        (m.H (c i).a=0 ∧ (c i).z=1)) ∧
      (⋃i,Ioo (c i).a (c i).z)=wholeCapFiniteUnion (nativeNegativeSet m) F ∧
      Pairwise (fun i j=>Disjoint (Ioo (c i).a (c i).z) (Ioo (c j).a (c j).z)) ∧
      (∀A: Set ℝ,MeasurableSet A→
        (∫u in 0..1,(A∩(wholeCapFiniteUnion (nativeNegativeSet m) F∪nativeActualContactSet m)).indicator
          (fun _=>1) (m.R u)*m.comparisonErrorDensity u)≤
        (∫u in 0..1,(A∩nativeActualContactSet m).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u)+
        (∫u in 0..1,(nativeActualComparableCapUnion m c).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u)+
        (∑p:nativeActualBroadSliceIndex m c,
          ∫u in 0..1,(nativeActualBroadSlice m c p).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u)+
        (∫u in 0..min (8*m.U) 1,m.comparisonErrorDensity u)) := by
  obtain ⟨c,hcase,hunion,hd⟩ := exists_actual_native_negative_cap_family m F hshort
  refine ⟨c,hcase,hunion,hd,?_⟩
  intro A hA
  rw [←hunion]
  exact actual_native_finite_cap_error_cover m c hd A hA

end OAI.SKFluctuations.LaplaceWindowFormalization
