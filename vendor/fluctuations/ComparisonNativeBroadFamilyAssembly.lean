module

public import ComparisonNativeBroadFrameConstruction
public import ComparisonNativeThermalOmission

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4800000
attribute [local instance] Classical.propDecidable

def nativeBroadSliceBudgetCore (m : NativeBandModel) (g : NativeBroadSliceGeometry m) (cut : ℝ) : ℝ :=
  let width := ∫r in Ioo g.a g.b,deriv m.alpha.val.val r
  let loss := m.Ko^2+25*(1+g.scale/m.U)*Real.log ((1+m.U)/m.U)+1
  48*(108*loss*(Real.log m.N)^2/(m.P*m.rho)*Real.log (width/cut))+
    (76+64*m.Lside)*width*m.D0^2+32*width*m.reverse m.D0+
    (66+64*m.Lside+65536*(1+m.Lside)^2)*
      (54*loss*(Real.log m.N)^2*width/(m.P*m.rho^2))

theorem native_inverse_derivative_unit_mass (m : NativeBandModel) :
    IntegrableOn (deriv m.alpha.val.val) (Icc (0:ℝ) 1) ∧
      (∫r in Icc (0:ℝ) 1,deriv m.alpha.val.val r)=1 := by
  have hac : AbsolutelyContinuousOnInterval m.alpha.val.val 0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le zero_le_one] using
      inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hac.intervalIntegrable_deriv,?_⟩
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one]
  simpa only [m.alpha.property.1,m.alpha.property.2.1,sub_zero] using hac.integral_deriv_eq_sub

theorem nativeBroadSliceFamily_mass_le_one {ι : Type*} [Fintype ι]
    (m : NativeBandModel) (g : ι→NativeBroadSliceGeometry m)
    (hdisjoint : Pairwise (fun i j=>Disjoint (Ioo (g i).a (g i).b) (Ioo (g j).a (g j).b))) :
    (∑i,∫r in Ioo (g i).a (g i).b,deriv m.alpha.val.val r)≤1 := by
  have hi := (native_inverse_derivative_unit_mass m).1
  have hsub i : Ioo (g i).a (g i).b⊆Icc (0:ℝ) 1 :=
    Ioo_subset_Icc_self.trans (Icc_subset_Icc (m.hag.le.trans (g i).haGroup) ((g i).hbGroup.trans m.hzg))
  rw [←integral_iUnion_fintype (fun _=>measurableSet_Ioo) hdisjoint (fun i=>hi.mono_set (hsub i))]
  have hb := setIntegral_mono_set hi (ae_of_all _ (fun r=>m.alpha.val.property.2.deriv_nonneg))
    (ae_of_all _ (fun r hr=>by obtain ⟨i,hi⟩:=mem_iUnion.mp hr;exact hsub i hi))
  exact hb.trans_eq (native_inverse_derivative_unit_mass m).2

theorem nativeBroadSliceFamily_card_le_inv_U {ι : Type*} [Fintype ι]
    (m : NativeBandModel) (g : ι→NativeBroadSliceGeometry m)
    (hdisjoint : Pairwise (fun i j=>Disjoint (Ioo (g i).a (g i).b) (Ioo (g j).a (g j).b))) :
    (Fintype.card ι:ℝ)≤1/m.U := by
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>(g i).hscale.trans (g i).hmass)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hh
  exact (le_div_iff₀ m.hU).mpr (hh.trans (nativeBroadSliceFamily_mass_le_one m g hdisjoint))

theorem native_indicator_iUnion_eq_sum {ι : Type*} [Fintype ι] (A : ι→Set ℝ)
    (hd : Pairwise (fun i j=>Disjoint (A i) (A j))) (r : ℝ) :
    (⋃i,A i).indicator (fun _ : ℝ=>(1:ℝ)) r=∑i,(A i).indicator (fun _=>1) r := by
  by_cases hr:r∈⋃i,A i
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hr
    rw [indicator_of_mem hr,Finset.sum_eq_single i,indicator_of_mem hi]
    · intro j hj hji
      exact indicator_of_notMem (fun h=>Set.disjoint_left.mp (hd hji) h hi) _
    · simp
  · have hn i : r∉A i := fun hi=>hr (mem_iUnion.mpr ⟨i,hi⟩)
    simp only [indicator_of_notMem hr,indicator_of_notMem (hn _),Finset.sum_const_zero]

theorem nativeActualThermal_disjoint_union {ι : Type*} [Fintype ι]
    (m : NativeBandModel) (A : ι→Set ℝ) (hA : ∀i,MeasurableSet (A i))
    (hd : Pairwise (fun i j=>Disjoint (A i) (A j))) :
    (∫u in 0..1,(⋃i,A i).indicator (fun _=>1) (m.R u)*m.thermal u)=
      ∑i,∫u in 0..1,(A i).indicator (fun _=>1) (m.R u)*m.thermal u := by
  have had := comparisonVariableEndpoint_clocks_admissible m.hc m.hk m.hkc m.hm m.hM
    m.b m.h m.hd.ne' m.hlam.le m.hlb m.hb m.hh m.hh0 m.alpha
  have hthermal := physicalOrderedThermal_intervalIntegrable m.n m.bf m.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
  have hi i : IntervalIntegrable (fun u=>(A i).indicator (fun _=>1) (m.R u)*m.thermal u) volume 0 1 := by
    apply intervalIntegrable_bounded_measurable_mul
      ((measurable_const.indicator (hA i)).comp
        (comparisonSweepQuantile_continuous m.hc m.hk m.hkc m.hm m.hM m.alpha).measurable)
      (show (0:ℝ)≤1 by norm_num) _ hthermal
    intro u hu
    by_cases hs:m.R u∈A i <;> simp [hs]
  simp_rw [native_indicator_iUnion_eq_sum A hd,Finset.sum_mul]
  exact intervalIntegral.integral_finset_sum (fun i _=>hi i)

theorem actual_native_broad_family_comparison {ι : Type*} [Fintype ι]
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : ι→NativeBroadSliceGeometry m)
    (hdisjoint : Pairwise (fun i j=>Disjoint (Ioo (g i).a (g i).b) (Ioo (g j).a (g j).b)))
    (hstrict : ∀j,∀i<(s.as j).length,
      partitionPoint 0 (s.as j) i< partitionPoint 0 (s.as j) (i+1))
    {cut : ℝ} (hcut : 0< cut) (hsmall : 2*cut< m.U)
    (hleft : m.cutRadius≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg≤ m.y)
    (hlog : Real.log (1/cut)≤ m.Lside)
    (hraw : ∀ᶠ j in atTop,physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>ProbabilityTheory.gaussianReal 0 (m.q 0 a)) id measurable_id≤ m.Q) :
    (∫u in 0..1,(⋃i,Ioo (g i).a (g i).b).indicator (fun _=>1) (m.R u)*m.thermal u)≤
      (∑i,nativeBroadSliceBudgetCore m (g i) cut)+16*cut/m.U := by
  rw [nativeActualThermal_disjoint_union m _ (fun _=>measurableSet_Ioo) hdisjoint]
  have hpoint i := actual_native_calibrated_broad_slice_comparison_of_eventual_raw m s (g i) hstrict hcut
    hsmall hleft hupper hlog hraw
  have hbudget i : (∫u in 0..1,(Ioo (g i).a (g i).b).indicator (fun _=>1) (m.R u)*m.thermal u)≤
      nativeBroadSliceBudgetCore m (g i) cut+16*cut := by
    simpa only [nativeBroadSliceBudgetCore,nativeConditionalLedgerBudget,Nat.cast_one,mul_one]
      using hpoint i
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>hbudget i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  have hcount := mul_le_mul_of_nonneg_right (nativeBroadSliceFamily_card_le_inv_U m g hdisjoint)
    (mul_nonneg (by norm_num : (0:ℝ)≤16) hcut.le)
  have heq : (1/m.U)*(16*cut)=16*cut/m.U := by ring
  rw [heq] at hcount
  exact hs.trans (add_le_add le_rfl hcount)

theorem nativeActual_radius_mask_mass (m : NativeBandModel) (A : Set ℝ)
    (hA : MeasurableSet A) (hsub : A⊆Icc (0:ℝ) 1) :
    (∫u in 0..1,A.indicator (fun _=>1) (m.R u))=∫r in A,deriv m.alpha.val.val r := by
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc,
    comparison_quantile_weighted_integral m.hc m.hk m.hkc m.hm m.hM m.alpha]
  simp_rw [←indicator_mul_right,mul_one]
  rw [setIntegral_indicator hA,inter_eq_right.mpr hsub]

def nativeBroadNearZero (m : NativeBandModel) : Set ℝ :=
  nativeBroadMassSlice m.hc m.hk m.hkc m.hm m.hM m.alpha 0 (min (8*m.U) 1)

theorem nativeBroadNearZero_mass_le (m : NativeBandModel) :
    (∫u in 0..1,(nativeBroadNearZero m).indicator (fun _=>1) (m.R u))≤8*m.U := by
  unfold nativeBroadNearZero nativeBroadMassSlice
  rw [nativeActual_radius_mask_mass m _ measurableSet_Ioo]
  · exact native_broad_near_zero_discard_mass m.hc m.hk m.hkc m.hm m.hM m.alpha m.hU
  · exact Ioo_subset_Icc_self.trans (Icc_subset_Icc
      (comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha 0).1
      (comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha _).2)

theorem nativeBroadNearZero_thermal_le (m : NativeBandModel) :
    (∫u in 0..1,(nativeBroadNearZero m).indicator (fun _=>1) (m.R u)*m.thermal u)≤8*m.U := by
  have hv : Measurable (fun u=>(nativeBroadNearZero m).indicator (fun _ : ℝ=>(1:ℝ)) (m.R u)) :=
    (measurable_const.indicator measurableSet_Ioo).comp
      (comparisonSweepQuantile_continuous m.hc m.hk m.hkc m.hm m.hM m.alpha).measurable
  have hh := actual_comparison_thermal_removed_mask_budget m.hc m.hk m.hkc m.hm m.hM
    m.n m.hd.ne' m.hlam.le m.b m.h m.hb m.hlb m.hh m.hh0 m.alpha
    (fun u=>(nativeBroadNearZero m).indicator (fun _=>1) (m.R u)) (fun _=>0) hv measurable_const
    (fun u _=>by simp only [indicator_apply];split_ifs <;> norm_num)
    (fun _ _=>by norm_num) (fun u _=>indicator_nonneg (fun _ _=>zero_le_one) _)
  have hb := hh.2
  simp only [zero_mul,intervalIntegral.integral_zero,sub_zero] at hb
  exact hb.trans (nativeBroadNearZero_mass_le m)

theorem actual_native_full_broad_comparison {ι : Type*} [Fintype ι]
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : ι→NativeBroadSliceGeometry m)
    (hdisjoint : Pairwise (fun i j=>Disjoint (Ioo (g i).a (g i).b) (Ioo (g j).a (g j).b)))
    (B : Set ℝ) (hB : MeasurableSet B)
    (hselected : (⋃i,Ioo (g i).a (g i).b)⊆B)
    (hcover : B⊆(⋃i,Ioo (g i).a (g i).b)∪(nativeBroadNearZero m))
    (hstrict : ∀j,∀i<(s.as j).length,
      partitionPoint 0 (s.as j) i< partitionPoint 0 (s.as j) (i+1))
    {cut : ℝ} (hcut : 0< cut) (hsmall : 2*cut< m.U)
    (hleft : m.cutRadius≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg≤ m.y)
    (hlog : Real.log (1/cut)≤ m.Lside)
    (hraw : ∀ᶠ j in atTop,physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>ProbabilityTheory.gaussianReal 0 (m.q 0 a)) id measurable_id≤ m.Q) :
    (∫u in 0..1,B.indicator (fun _=>1) (m.R u)*m.thermal u)≤
      (∑i,nativeBroadSliceBudgetCore m (g i) cut)+16*cut/m.U+8*m.U := by
  let A := ⋃i,Ioo (g i).a (g i).b
  have hA : MeasurableSet A := MeasurableSet.iUnion (fun _=>measurableSet_Ioo)
  let v : ℝ→ℝ := fun u=>B.indicator (fun _=>1) (m.R u)
  let w : ℝ→ℝ := fun u=>A.indicator (fun _=>1) (m.R u)
  let low : ℝ→ℝ := fun u=>(nativeBroadNearZero m).indicator (fun _=>1) (m.R u)
  have hR := (comparisonSweepQuantile_continuous m.hc m.hk m.hkc m.hm m.hM m.alpha).measurable
  have hv : Measurable v := (measurable_const.indicator hB).comp hR
  have hw : Measurable w := (measurable_const.indicator hA).comp hR
  have hlow : Measurable low := (measurable_const.indicator measurableSet_Ioo).comp hR
  have hvb : ∀u∈Ioc (0:ℝ) 1,v u∈Icc (0:ℝ) 1 := by
    intro u hu
    simp only [v,indicator_apply]
    split_ifs <;> norm_num
  have hwb : ∀u∈Ioc (0:ℝ) 1,w u∈Icc (0:ℝ) 1 := by
    intro u hu
    simp only [w,indicator_apply]
    split_ifs <;> norm_num
  have hlowb : ∀u∈Ioc (0:ℝ) 1,low u∈Icc (0:ℝ) 1 := by
    intro u hu
    simp only [low,indicator_apply]
    split_ifs <;> norm_num
  have hsub : ∀u∈Ioc (0:ℝ) 1,w u≤ v u := by
    intro u hu
    by_cases hs:m.R u∈A
    · simp [w,v,hs,hselected hs]
    · simp [w,hs];exact (hvb u hu).1
  have hpoint : ∀u∈Icc (0:ℝ) 1,v u-w u≤ low u := by
    intro u hu
    by_cases hb:m.R u∈B
    · by_cases ha:m.R u∈A
      · simp [v,w,low,hb,ha];exact indicator_nonneg (fun _ _=>zero_le_one) _
      · have hl := (hcover hb).resolve_left ha
        simp [v,w,low,hb,ha,hl]
    · have ha : m.R u∉A := fun ha=>hb (hselected ha)
      simp [v,w,low,hb,ha];exact indicator_nonneg (fun _ _=>zero_le_one) _
  have hiV : IntervalIntegrable v volume 0 1 := by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hv zero_le_one hvb
      (intervalIntegrable_const (c:=(1:ℝ)))
  have hiW : IntervalIntegrable w volume 0 1 := by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hw zero_le_one hwb
      (intervalIntegrable_const (c:=(1:ℝ)))
  have hiLow : IntervalIntegrable low volume 0 1 := by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hlow zero_le_one hlowb
      (intervalIntegrable_const (c:=(1:ℝ)))
  have hgap : (∫u in 0..1,v u)-(∫u in 0..1,w u)≤8*m.U := by
    rw [←intervalIntegral.integral_sub hiV hiW]
    exact (intervalIntegral.integral_mono_on zero_le_one (hiV.sub hiW) hiLow hpoint).trans
      (nativeBroadNearZero_mass_le m)
  have hthermal := actual_comparison_thermal_removed_mask_budget m.hc m.hk m.hkc m.hm m.hM
    m.n m.hd.ne' m.hlam.le m.b m.h m.hb m.hlb m.hh m.hh0 m.alpha v w hv hw hvb hwb hsub
  have hretained := actual_native_broad_family_comparison m s g hdisjoint hstrict hcut hsmall
    hleft hupper hlog hraw
  have hh := hthermal.2
  change (∫u in 0..1,v u*m.thermal u)-(∫u in 0..1,w u*m.thermal u)≤
    (∫u in 0..1,v u)-(∫u in 0..1,w u) at hh
  change (∫u in 0..1,v u*m.thermal u)≤_
  change (∫u in 0..1,w u*m.thermal u)≤_ at hretained
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
