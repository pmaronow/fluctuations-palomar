module

public import ComparisonNativeWholeCapErrorCover
public import ComparisonNativeCapExhaustionLocal
public import ComparisonNativeMinimumBandModel
public import ComparisonNativeFloorRawEnvelope

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4300000
attribute [local instance] Classical.propDecidable

structure NativeFiniteBandConsumers (m:NativeBandModel) where
  budget : ℝ
  consume : ∀F:Finset (ordConnectedSection (nativeNegativeSet m)),
    ∀c:F→NativeActualCapInterval m,
    (∀i,(m.H (c i).a=0 ∧ m.H (c i).z=0) ∨ ((c i).a=0 ∧ m.H (c i).z=0) ∨
      (m.H (c i).a=0 ∧ (c i).z=1))→
    (⋃i,Ioo (c i).a (c i).z)=wholeCapFiniteUnion (nativeNegativeSet m) F→
    Pairwise (fun i j=>Disjoint (Ioo (c i).a (c i).z) (Ioo (c j).a (c j).z))→
    (∫u in 0..1,(nativeActualContactSet m).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u)+
    (∫u in 0..1,(nativeActualComparableCapUnion m c).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u)+
    (∑p:nativeActualBroadSliceIndex m c,
      ∫u in 0..1,(nativeActualBroadSlice m c p).indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u)≤ budget

theorem actual_full_native_nonpositive_error_le_of_finite_band_consumers
    (m:NativeBandModel) (bands:NativeFiniteBandConsumers m) (hshort:nativeCapTravel m<1) :
    (∫u in 0..1,(nativeNegativeSet m∪nativeActualContactSet m).indicator
      (fun _=>1) (m.R u)*m.comparisonErrorDensity u)≤
      bands.budget+(∫u in 0..min (8*m.U) 1,m.comparisonErrorDensity u) := by
  have hfinite (F:Finset (ordConnectedSection (nativeNegativeSet m))) :
      (∫u in 0..1,(wholeCapFiniteUnion (nativeNegativeSet m) F∪nativeActualContactSet m).indicator
        (fun _=>1) (m.R u)*m.comparisonErrorDensity u)≤
        bands.budget+(∫u in 0..min (8*m.U) 1,m.comparisonErrorDensity u) := by
    obtain ⟨c,hcase,hunion,hd,hcover⟩ := actual_native_negative_cap_family_error_cover m F hshort
    have hn := hcover univ MeasurableSet.univ
    simp only [univ_inter] at hn
    exact hn.trans (add_le_add (bands.consume F c hcase hunion hd) le_rfl)
  have hmaskFinite (F:Finset (ordConnectedSection (nativeNegativeSet m))) (u:ℝ) :
      (NativeSelectedMask.fixedSupport (NativeCapExhaustion.left (nativeNegativeSet m) F)
        (NativeCapExhaustion.right (nativeNegativeSet m) F) m.H).indicator (fun _=>(1:ℝ)) (m.R u)=
      (wholeCapFiniteUnion (nativeNegativeSet m) F∪nativeActualContactSet m).indicator (fun _=>1) (m.R u) := by
    rw [NativeCapExhaustion.fixedSupport_eq (nativeNegativeSet_open m) (nativeNegativeSet_subset m)]
    have hr := comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha u
    simp only [indicator_apply,mem_union,mem_setOf_eq,nativeActualContactSet,mem_inter_iff,
      mem_preimage,mem_singleton_iff,hr,true_and]
  have hmaskFull (u:ℝ) :
      (nativeNegativeSet m∪{r | m.H r=0}).indicator (fun _=>(1:ℝ)) (m.R u)=
      (nativeNegativeSet m∪nativeActualContactSet m).indicator (fun _=>1) (m.R u) := by
    have hr := comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha u
    simp only [indicator_apply,mem_union,mem_setOf_eq,nativeActualContactSet,mem_inter_iff,
      mem_preimage,mem_singleton_iff,hr,true_and]
  have hH : ContinuousOn m.H (Icc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using m.hH.continuousOn
  have hT := (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
    (nativeActualError_intervalIntegrable m)
  have hfull : (∫u in Icc (0:ℝ) 1,(univ∩(nativeNegativeSet m∪{r | m.H r=0})).indicator
      (fun _=>(1:ℝ)) (m.R u)*m.comparisonErrorDensity u)≤
      bands.budget+(∫u in 0..min (8*m.U) 1,m.comparisonErrorDensity u) := by
    apply NativeCapExhaustion.actual_local_full_thermal_le_of_finite_caps
      m.hc m.hk m.hkc m.hm m.hM m.alpha (nativeNegativeSet_open m)
      (nativeNegativeSet_subset m) m.H hH univ MeasurableSet.univ m.comparisonErrorDensity hT
    intro F
    simp only [univ_inter]
    simp_rw [hmaskFinite]
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one]
    exact hfinite F
  simp only [univ_inter] at hfull
  simp_rw [hmaskFull] at hfull
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one] at hfull
  exact hfull

namespace NativeOverlapMinimum
variable {n:ℕ} {margin delta cl cu Az C0 Ct D Bclock:ℝ}

def FullErrorAssemblyTarget
    (a:NativeOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (finiteBudget K:ℝ) : Prop :=
  let C := 1+cu*(Az+1)
  let floorCost := (K*C^2+1)*(2*a.lam*a.xs^2*a.context.N^(-delta)*a.context.U+
    4*a.context.d^3*Real.log a.context.N*a.context.N^delta*a.context.U^2*
      Real.log ((1+a.context.N^(2*delta)*a.context.U)/(a.context.N^(2*delta)*a.context.U)))
  let initialCost := 8*a.lam*a.context.U*
    (K*(a.xs+8*a.context.U)^2+(Az*a.xs+8*a.context.U/cl)^2)
  (∫u in 0..1,laplaceComparisonStrength a.context.d a.lam (a.R u)*
    ((orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)+
      (orderedPathS (n+1) a.bf a.hf u-a.R u)^2))≤ finiteBudget+initialCost+floorCost

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
