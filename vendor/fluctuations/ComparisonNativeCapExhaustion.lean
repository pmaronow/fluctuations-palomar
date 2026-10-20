module

public import ComparisonNativeSelectedMaskGeometry
public import ComparisonNativeMaskMassTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology ENNReal NNReal
set_option maxHeartbeats 2200000
attribute [local instance] Classical.propDecidable

namespace NativeCapExhaustion

def left (U : Set ℝ) (F : Finset (ordConnectedSection U)) (t : F) : ℝ :=
  sInf (ordConnectedComponent U t.val.val)

def right (U : Set ℝ) (F : Finset (ordConnectedSection U)) (t : F) : ℝ :=
  sSup (ordConnectedComponent U t.val.val)

theorem fixedSupport_eq {U : Set ℝ} (hU : IsOpen U) {a b : ℝ}
    (hUb : U⊆Icc a b) (F : Finset (ordConnectedSection U)) (H : ℝ→ℝ) :
    NativeSelectedMask.fixedSupport (left U F) (right U F) H=
      wholeCapFiniteUnion U F∪{r | H r=0} := by
  have hcomp (t:ordConnectedSection U) : ordConnectedComponent U t.val=
      Ioo (sInf (ordConnectedComponent U t.val)) (sSup (ordConnectedComponent U t.val)) :=
    (wholeCap_component_endpoints hU hUb (ordConnectedSection_subset t.property)).2.2.2.2.1
  ext r
  constructor
  · rintro (⟨t,ht⟩|hr)
    · apply Or.inl
      exact mem_iUnion₂.mpr ⟨t.val,t.property,by rw [hcomp t.val];exact ht⟩
    · exact Or.inr hr
  · rintro (hr|hr)
    · obtain ⟨t,ht,hr⟩ := mem_iUnion₂.mp hr
      exact Or.inl ⟨⟨t,ht⟩,by change r∈Ioo (sInf _) (sSup _);rw [←hcomp t];exact hr⟩
    · exact Or.inr hr

theorem endpoints {U : Set ℝ} (hU : IsOpen U) {a b : ℝ}
    (hUb : U⊆Icc a b) (F : Finset (ordConnectedSection U)) :
    (∀t:F,a≤left U F t ∧ left U F t<right U F t ∧ right U F t≤b) ∧
      Pairwise (fun s t:F=>Disjoint (Ioo (left U F s) (right U F s))
        (Ioo (left U F t) (right U F t))) := by
  constructor
  · intro t
    have hh := wholeCap_component_endpoints hU hUb (ordConnectedSection_subset t.val.property)
    exact ⟨hh.1,hh.2.1.trans hh.2.2.1,hh.2.2.2.1⟩
  · intro s t hst
    have hs := wholeCap_component_endpoints hU hUb (ordConnectedSection_subset s.val.property)
    have ht := wholeCap_component_endpoints hU hUb (ordConnectedSection_subset t.val.property)
    change Disjoint (Ioo (sInf _) (sSup _)) (Ioo (sInf _) (sSup _))
    rw [←hs.2.2.2.2.1,←ht.2.2.2.2.1]
    apply wholeCap_representatives_pairwiseDisjoint U s.val.property t.val.property
    intro heq
    apply hst
    exact Subtype.ext (Subtype.ext heq)

theorem support_eventually_eq {U : Set ℝ} (hU : IsOpen U) {a b : ℝ}
    (hUb : U⊆Icc a b) (H : ℝ→ℝ)
    (F : ℕ→Finset (ordConnectedSection U)) (hF : Monotone F)
    (hcover : ∀t:ordConnectedSection U,∃n,t∈F n) (r : ℝ) :
    ∀ᶠ n in atTop,
      (r∈NativeSelectedMask.fixedSupport (left U (F n)) (right U (F n)) H ↔
        r∈U∪{r | H r=0}) := by
  simp_rw [fixedSupport_eq hU hUb]
  by_cases hrH : H r=0
  · exact Eventually.of_forall (fun _=>by simp [hrH])
  by_cases hrU : r∈U
  · obtain ⟨t,ht,hrt⟩ := mem_iUnion₂.mp ((wholeCap_representatives_union U).symm ▸ hrU)
    obtain ⟨n,hn⟩ := hcover ⟨t,ht⟩
    filter_upwards [eventually_ge_atTop n] with j hj
    have hret : r∈wholeCapFiniteUnion U (F j) := mem_iUnion₂.mpr
      ⟨⟨t,ht⟩,hF hj hn,hrt⟩
    simp only [mem_union,mem_ofPred_eq,hrH,or_false]
    exact iff_of_true hret hrU
  · exact Eventually.of_forall (fun n=>by
      have hnot : r∉wholeCapFiniteUnion U (F n) :=
        fun hh=>hrU (wholeCapFiniteUnion_subset U (F n) hh)
      simp only [mem_union,mem_ofPred_eq,hrH,or_false,hnot,hrU])

theorem thermal_integral_tendsto {U : Set ℝ} (hU : IsOpen U) {a b : ℝ}
    (hUb : U⊆Icc a b) (H R : ℝ→ℝ) (hH : Measurable H) (hR : Measurable R)
    (A : Set ℝ) (hA : MeasurableSet A) (T : ℝ→ℝ)
    (hT : IntegrableOn T (Icc (0:ℝ) 1))
    (F : ℕ→Finset (ordConnectedSection U)) (hF : Monotone F)
    (hcover : ∀t:ordConnectedSection U,∃n,t∈F n) :
    Tendsto (fun n=>∫u in Icc (0:ℝ) 1,
      (A∩NativeSelectedMask.fixedSupport (left U (F n)) (right U (F n)) H).indicator
        (fun _=>(1:ℝ)) (R u)*T u) atTop
      (𝓝 (∫u in Icc (0:ℝ) 1,(A∩(U∪{r | H r=0})).indicator (fun _=>(1:ℝ)) (R u)*T u)) := by
  have hzero : MeasurableSet {r | H r=0} := measurableSet_eq_fun hH measurable_const
  have hmasks n : MeasurableSet (A∩NativeSelectedMask.fixedSupport
      (left U (F n)) (right U (F n)) H) := by
    rw [fixedSupport_eq hU hUb]
    exact hA.inter ((wholeCapFiniteUnion_isOpen hU (F n)).measurableSet.union hzero)
  apply tendsto_integral_of_dominated_convergence (fun u=>‖T u‖)
  · intro n
    exact (((measurable_const.indicator (hmasks n)).comp hR).aestronglyMeasurable.restrict).mul
      hT.aestronglyMeasurable
  · exact hT.norm
  · intro n
    filter_upwards [] with u
    by_cases hu : R u∈A∩NativeSelectedMask.fixedSupport (left U (F n)) (right U (F n)) H
    · simp only [indicator_of_mem hu,one_mul,le_refl]
    · simp only [indicator_of_notMem hu,zero_mul,norm_zero];exact norm_nonneg _
  · filter_upwards [] with u
    apply tendsto_const_nhds.congr'
    filter_upwards [support_eventually_eq hU hUb H F hF hcover (R u)] with n hn
    have heq : (R u∈A∩NativeSelectedMask.fixedSupport (left U (F n)) (right U (F n)) H) ↔
        R u∈A∩(U∪{r | H r=0}) := and_congr_right (fun _=>hn)
    by_cases hu : R u∈A∩(U∪{r | H r=0})
    · rw [indicator_of_mem hu,indicator_of_mem (heq.mpr hu)]
    · rw [indicator_of_notMem hu,indicator_of_notMem (fun hh=>hu (heq.mp hh))]

section Native
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem actual_finite_cap_thermal_exhaustion
    (α : inverseIntegralConstraints 0 0 k M)
    {U : Set ℝ} (hU : IsOpen U) (hUb : U⊆Icc (0:ℝ) 1)
    (H : ℝ→ℝ) (hH : Measurable H) (A : Set ℝ) (hA : MeasurableSet A)
    (T : ℝ→ℝ) (hT : IntegrableOn T (Icc (0:ℝ) 1)) :
    ∃F : ℕ→Finset (ordConnectedSection U),Monotone F ∧
      (∀t:ordConnectedSection U,∃j,t∈F j) ∧
      Tendsto (fun j=>(wholeCapRadiusMass (comparisonSweepQuantile hc hk hkc hm hM α)
        (fun u _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α u)).real
        (U\wholeCapFiniteUnion U (F j))) atTop (𝓝 0) ∧
      Tendsto (fun j=>∫u in Icc (0:ℝ) 1,
        (A∩NativeSelectedMask.fixedSupport (left U (F j)) (right U (F j)) H).indicator
          (fun _=>(1:ℝ)) (comparisonSweepQuantile hc hk hkc hm hM α u)*T u) atTop
        (𝓝 (∫u in Icc (0:ℝ) 1,(A∩(U∪{r | H r=0})).indicator
          (fun _=>(1:ℝ)) (comparisonSweepQuantile hc hk hkc hm hM α u)*T u)) := by
  obtain ⟨F,hF,hcover,htail⟩ := wholeCap_actual_comparison_mass_finite_selection hc hk hkc hm hM α hU
  exact ⟨F,hF,hcover,htail,thermal_integral_tendsto hU hUb H _ hH
    (comparisonSweepQuantile_continuous hc hk hkc hm hM α).measurable A hA T hT F hF hcover⟩

end Native
end NativeCapExhaustion
end OAI.SKFluctuations.LaplaceWindowFormalization
