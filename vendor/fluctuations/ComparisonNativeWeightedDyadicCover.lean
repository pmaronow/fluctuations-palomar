module

public import ComparisonNativeContactDyadicLocalCover
public import ComparisonNativeGlobalErrorAssemblyDraft
public import ComparisonNativeBroadDyadicTotal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
attribute [local instance] Classical.propDecidable

theorem native_error_mask_le_finite_ordinary_cover
    {ι : Type*} [Fintype ι] (m : NativeBandModel) (b : ι → NativeBandModel)
    (hq : ∀i,(b i).R=m.R) (ht : ∀i,(b i).comparisonErrorDensity=m.comparisonErrorDensity)
    (A : Set ℝ) (hA : MeasurableSet A)
    (hcover : ∀ᵐu ∂volume.restrict (Ioc (0:ℝ) 1),
      m.R u∈A → ∃i,m.R u∈(b i).ordinarySupport) :
    (∫u in 0..1,A.indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u) ≤
      ∑i,∫u in 0..1,(b i).ordinaryMask ((b i).R u)*(b i).comparisonErrorDensity u := by
  let f := fun i u => (b i).ordinaryMask ((b i).R u)*(b i).comparisonErrorDensity u
  have hi i : IntervalIntegrable (f i) volume 0 1 := by
    have hT : IntervalIntegrable (b i).comparisonErrorDensity volume 0 1 := by
      simpa only [indicator_univ,one_mul] using
        nativeActualError_mask_integrable (b i) univ MeasurableSet.univ
    exact intervalIntegrable_bounded_measurable_mul (b i).ordinaryMask_composed_measurable
      zero_le_one (fun u _ => by
        unfold NativeBandModel.ordinaryMask
        by_cases h : (b i).R u∈(b i).ordinarySupport <;> simp [h]) hT
  have hiSum : IntervalIntegrable (fun u=>∑i,f i u) volume 0 1 := by
    have he : (fun u=>∑i,f i u)=∑i,f i := by funext u; simp only [Finset.sum_apply]
    rw [he]
    exact IntervalIntegrable.sum Finset.univ (fun i _=>hi i)
  have hiA := nativeActualError_mask_integrable m A hA
  have hp : ∀ᵐu ∂volume.restrict (Ioc (0:ℝ) 1),
      A.indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u ≤ ∑i,f i u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,hcover] with u hu hc
    have hn i : 0 ≤ f i u := by
      dsimp [f]
      rw [hq,ht]
      exact mul_nonneg (indicator_nonneg (fun _ _=>zero_le_one) _)
        (nativeActualError_nonneg m hu)
    by_cases hmem : m.R u∈A
    · obtain ⟨i,hi⟩ := hc hmem
      have he : f i u=m.comparisonErrorDensity u := by
        dsimp [f]
        rw [hq,ht]
        simp only [NativeBandModel.ordinaryMask,indicator_of_mem hi,one_mul]
      have hs := Finset.single_le_sum (s:=Finset.univ) (f:=fun i=>f i u)
        (fun i _=>hn i) (Finset.mem_univ i)
      rw [he] at hs
      simpa only [indicator_of_mem hmem,one_mul] using hs
    · simp only [indicator_of_notMem hmem,zero_mul]
      exact Finset.sum_nonneg (fun i _=>hn i)
  have hb : (∫u in 0..1,A.indicator (fun _=>1) (m.R u)*m.comparisonErrorDensity u) ≤ ∫u in 0..1,∑i,f i u := by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact integral_mono_ae ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hiA)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hiSum) hp
  rw [intervalIntegral.integral_finsetSum (fun i _=>hi i)] at hb
  exact hb

namespace NativeContactDyadicBandFamily

theorem comparable_error_le_sum {ι : Type*} [Fintype ι]
    {m : NativeBandModel} (g : NativeContactDyadicBandFamily m)
    (c : ι → NativeActualCapInterval m)
    (hcase : ∀i,(m.H (c i).a=0 ∧ m.H (c i).z=0) ∨
      ((c i).a=0 ∧ m.H (c i).z=0) ∨ (m.H (c i).a=0 ∧ (c i).z=1)) :
    (∫u in 0..1,(nativeActualComparableCapUnion m c).indicator
      (fun _=>1) (m.R u)*m.comparisonErrorDensity u) ≤
      ∑j : comparisonMassDyadicIndices m.U,
        ∫u in 0..1,(g.model j).ordinaryMask ((g.model j).R u)*
          (g.model j).comparisonErrorDensity u := by
  apply native_error_mask_le_finite_ordinary_cover m g.model g.quantile g.error
    _ (MeasurableSet.iUnion (fun _=>measurableSet_Ioo))
  apply Eventually.of_forall
  intro u hu
  obtain ⟨i,hi⟩ := mem_iUnion.mp hu
  obtain ⟨k,_,hka,hkz,_⟩ := actual_native_comparable_cap_enlargement m c i
  have hk1 : m.U*(2:ℝ)^k ≤ 1 := hka.trans (m.alpha.val.property.1 (c i.val).a).2
  let j : comparisonMassDyadicIndices m.U := ⟨k,comparison_mass_dyadic_mem m.hU hk1⟩
  have hright : m.alpha.val.val (c i.val).z ≤ min (16*(m.U*(2:ℝ)^(j:ℕ))) 1 :=
    le_min hkz (m.alpha.val.property.1 (c i.val).z).2
  exact ⟨j,g.comparable_cap_mem_group (j:=j) (c i.val) (hcase i.val) hka hright hi⟩

theorem contact_comparable_error_le_sum {ι : Type*} [Fintype ι]
    {m : NativeBandModel} (g : NativeContactDyadicBandFamily m)
    (c : ι → NativeActualCapInterval m)
    (hcase : ∀i,(m.H (c i).a=0 ∧ m.H (c i).z=0) ∨
      ((c i).a=0 ∧ m.H (c i).z=0) ∨ (m.H (c i).a=0 ∧ (c i).z=1)) :
    (∫u in 0..1,(nativeActualContactSet m).indicator
      (fun _=>1) (m.R u)*m.comparisonErrorDensity u)+
    (∫u in 0..1,(nativeActualComparableCapUnion m c).indicator
      (fun _=>1) (m.R u)*m.comparisonErrorDensity u) ≤
      2*(∑j : comparisonMassDyadicIndices m.U,
        ∫u in 0..1,(g.model j).ordinaryMask ((g.model j).R u)*
          (g.model j).comparisonErrorDensity u)+
      (∫u in 0..1,(nativeBroadNearZero m).indicator
        (fun _=>1) (m.R u)*m.comparisonErrorDensity u) := by
  have hc := g.toNativeDyadicBandFamily.contact_error_le_sum
  have hp := g.comparable_error_le_sum c hcase
  linarith

end NativeContactDyadicBandFamily
end OAI.SKFluctuations.LaplaceWindowFormalization
