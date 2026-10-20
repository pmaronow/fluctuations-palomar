module

public import ComparisonNativeContactDyadicLocalCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000
attribute [local instance] Classical.propDecidable

abbrev NativeLocalMassDyad (m : NativeBandModel) (lo hi : ℝ) :=
  {j : comparisonMassDyadicIndices m.U //
    lo/16 ≤ m.U*(2:ℝ)^(j.val:ℕ) ∧ m.U*(2:ℝ)^(j.val:ℕ) ≤ hi}

private theorem native_thermal_mask_le_finite_ordinary_cover
    {ι : Type*} [Fintype ι] (m : NativeBandModel) (b : ι → NativeBandModel)
    (hq : ∀i,(b i).R=m.R) (ht : ∀i,(b i).thermal=m.thermal)
    (A : Set ℝ) (hA : MeasurableSet A)
    (hcover : ∀ᵐu ∂volume.restrict (Ioc (0:ℝ) 1),
      m.R u∈A → ∃i,m.R u∈(b i).ordinarySupport) :
    (∫u in 0..1,A.indicator (fun _=>1) (m.R u)*m.thermal u) ≤
      ∑i,∫u in 0..1,(b i).ordinaryMask ((b i).R u)*(b i).thermal u := by
  let f := fun i u => (b i).ordinaryMask ((b i).R u)*(b i).thermal u
  have hi i : IntervalIntegrable (f i) volume 0 1 := by
    have hT : IntervalIntegrable (b i).thermal volume 0 1 := by
      simpa only [indicator_univ,one_mul] using
        nativeActualThermal_mask_integrable (b i) univ MeasurableSet.univ
    exact intervalIntegrable_bounded_measurable_mul (b i).ordinaryMask_composed_measurable
      zero_le_one (fun u _ => by
        unfold NativeBandModel.ordinaryMask
        by_cases h : (b i).R u∈(b i).ordinarySupport <;> simp [h]) hT
  have hiSum : IntervalIntegrable (fun u=>∑i,f i u) volume 0 1 := by
    have he : (fun u=>∑i,f i u)=∑i,f i := by funext u; simp only [Finset.sum_apply]
    rw [he]
    exact IntervalIntegrable.sum Finset.univ (fun i _=>hi i)
  have hiA := nativeActualThermal_mask_integrable m A hA
  have hp : ∀ᵐu ∂volume.restrict (Ioc (0:ℝ) 1),
      A.indicator (fun _=>1) (m.R u)*m.thermal u ≤ ∑i,f i u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,hcover] with u hu hc
    have hn i : 0 ≤ f i u := by
      dsimp [f]
      rw [hq,ht]
      exact mul_nonneg (indicator_nonneg (fun _ _=>zero_le_one) _)
        (nativeActualThermal_nonneg m hu)
    by_cases hmem : m.R u∈A
    · obtain ⟨i,hi⟩ := hc hmem
      have he : f i u=m.thermal u := by
        dsimp [f]
        rw [hq,ht]
        simp only [NativeBandModel.ordinaryMask,indicator_of_mem hi,one_mul]
      have hs := Finset.single_le_sum (s:=Finset.univ) (f:=fun i=>f i u)
        (fun i _=>hn i) (Finset.mem_univ i)
      rw [he] at hs
      simpa only [indicator_of_mem hmem,one_mul] using hs
    · simp only [indicator_of_notMem hmem,zero_mul]
      exact Finset.sum_nonneg (fun i _=>hn i)
  have hb : (∫u in 0..1,A.indicator (fun _=>1) (m.R u)*m.thermal u) ≤ ∫u in 0..1,∑i,f i u := by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    exact integral_mono_ae ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hiA)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hiSum) hp
  rw [intervalIntegral.integral_finsetSum (fun i _=>hi i)] at hb
  exact hb

namespace NativeContactDyadicBandFamily

theorem contact_mem_local_group {m : NativeBandModel} (g : NativeContactDyadicBandFamily m)
    {lo hi u : ℝ} (hu : u∈Ioo (0:ℝ) 1) (hU : m.U ≤ lo)
    (hlo : lo ≤ u) (hhi : u ≤ hi) (hzero : m.H (m.R u)=0) :
    ∃j : NativeLocalMassDyad m lo hi, m.R u∈(g.model j.val).ordinarySupport := by
  obtain ⟨j,hj,hj'⟩ := comparison_mass_dyadic_cover m.hU (hU.trans hlo) hu.2.le
  have hv := comparison_mass_dyadic_scale m.hU j
  let v := m.U*(2:ℝ)^(j:ℕ)
  have hlow : v/2∈Icc (0:ℝ) 1 := ⟨by dsimp [v] at *; linarith,by dsimp [v] at *; linarith⟩
  have hhigh : min (16*v) 1∈Icc (0:ℝ) 1 :=
    ⟨(lt_min (by dsimp [v] at *; linarith) zero_lt_one).le,min_le_right _ _⟩
  have hs := comparisonSweepQuantile_strictMono_native_geometry m.hc m.hk m.hkc m.hm m.hM m.alpha
  refine ⟨⟨j,by dsimp [v] at *; linarith,hj.trans hhi⟩,?_,?_⟩
  · rw [g.left,g.right]
    exact ⟨hs hlow (Ioo_subset_Icc_self hu) (by dsimp [v] at *; linarith),
      hs (Ioo_subset_Icc_self hu) hhigh (lt_min (by dsimp [v] at *; linarith) hu.2)⟩
  · right
    rw [g.potential]
    exact hzero

theorem relevant_comparable_thermal_le_local_sum {ι : Type*} [Fintype ι]
    {m : NativeBandModel} (g : NativeContactDyadicBandFamily m)
    (c : ι→NativeActualCapInterval m) (A : Set ℝ)
    (hcase : ∀i,(m.H (c i).a=0 ∧ m.H (c i).z=0) ∨
      ((c i).a=0 ∧ m.H (c i).z=0) ∨ (m.H (c i).a=0 ∧ (c i).z=1))
    {lo hi : ℝ} (hA : ∀r∈A,lo ≤ m.alpha.val.val r ∧ m.alpha.val.val r ≤ hi) :
    (∫u in 0..1,(nativeRelevantComparableCapUnion m c A).indicator
      (fun _=>1) (m.R u)*m.thermal u) ≤
      ∑j : NativeLocalMassDyad m lo hi,
        ∫u in 0..1,(g.model j.val).ordinaryMask ((g.model j.val).R u)*(g.model j.val).thermal u := by
  apply native_thermal_mask_le_finite_ordinary_cover m (fun j : NativeLocalMassDyad m lo hi=>g.model j.val)
    (fun j=>g.quantile j.val) (fun j=>g.thermal j.val)
    _ (MeasurableSet.iUnion (fun _=>measurableSet_Ioo))
  apply Eventually.of_forall
  intro u hu
  obtain ⟨i,hi⟩ := mem_iUnion.mp hu
  obtain ⟨j,hlo,hhi,hgroup⟩ := g.relevant_comparable_cap_mem_group c A hcase hA i
  exact ⟨⟨j,hlo,hhi⟩,hgroup hi⟩

theorem contact_thermal_le_local_sum {m : NativeBandModel} (g : NativeContactDyadicBandFamily m)
    (A : Set ℝ) (hA : MeasurableSet A) {lo hi : ℝ} (hU : m.U ≤ lo)
    (hscale : ∀r∈A,lo ≤ m.alpha.val.val r ∧ m.alpha.val.val r ≤ hi) :
    (∫u in 0..1,(A∩nativeActualContactSet m).indicator (fun _=>1) (m.R u)*m.thermal u) ≤
      ∑j : NativeLocalMassDyad m lo hi,
        ∫u in 0..1,(g.model j.val).ordinaryMask ((g.model j.val).R u)*(g.model j.val).thermal u := by
  apply native_thermal_mask_le_finite_ordinary_cover m (fun j : NativeLocalMassDyad m lo hi=>g.model j.val)
    (fun j=>g.quantile j.val) (fun j=>g.thermal j.val)
    _ (hA.inter (nativeActualContactSet_measurable m))
  filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (1:ℝ))]
    with u hu hune hmem
  have hs := hscale (m.R u) hmem.1
  rw [comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha (Ioc_subset_Icc_self hu)] at hs
  exact g.contact_mem_local_group ⟨hu.1,lt_of_le_of_ne hu.2 hune⟩ hU hs.1 hs.2 hmem.2.2

end NativeContactDyadicBandFamily
end OAI.SKFluctuations.LaplaceWindowFormalization
