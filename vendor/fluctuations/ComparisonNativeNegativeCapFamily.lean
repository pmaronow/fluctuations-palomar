module

public import ComparisonNativeWholeCapThermalCover
public import ComparisonNativeCapExhaustion

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3600000
attribute [local instance] Classical.propDecidable

theorem exists_actual_native_negative_cap_family (m : NativeBandModel)
    (F : Finset (ordConnectedSection (nativeNegativeSet m))) (hshort : nativeCapTravel m<1) :
    ∃c:F→NativeActualCapInterval m,
      (∀i,(m.H (c i).a=0 ∧ m.H (c i).z=0) ∨ ((c i).a=0 ∧ m.H (c i).z=0) ∨
        (m.H (c i).a=0 ∧ (c i).z=1)) ∧
      (⋃i,Ioo (c i).a (c i).z)=wholeCapFiniteUnion (nativeNegativeSet m) F ∧
      Pairwise (fun i j=>Disjoint (Ioo (c i).a (c i).z) (Ioo (c j).a (c j).z)) := by
  have hr (i:F) : i.val.val∈nativeNegativeSet m := ordConnectedSection_subset i.val.property
  have hex (i:F) := actual_native_negative_component_endpoints m (hr i) hshort
  choose c hA hZ hC hboundary using hex
  refine ⟨c,hboundary,?_,?_⟩
  · ext r
    constructor
    · intro h
      obtain ⟨i,hi⟩ := mem_iUnion.mp h
      rw [hC i] at hi
      exact mem_iUnion₂.mpr ⟨i.val,i.property,hi⟩
    · intro h
      obtain ⟨i,hi,hr⟩ := mem_iUnion₂.mp h
      apply mem_iUnion.mpr
      refine ⟨⟨i,hi⟩,?_⟩
      rw [hC ⟨i,hi⟩]
      exact hr
  · intro i j hij
    rw [hA i,hZ i,hA j,hZ j]
    exact (NativeCapExhaustion.endpoints (nativeNegativeSet_open m)
      (nativeNegativeSet_subset m) F).2 hij

theorem actual_native_negative_cap_family_thermal_cover (m : NativeBandModel)
    (F : Finset (ordConnectedSection (nativeNegativeSet m))) (hshort : nativeCapTravel m<1) :
    ∃c:F→NativeActualCapInterval m,
      (∀i,(m.H (c i).a=0 ∧ m.H (c i).z=0) ∨ ((c i).a=0 ∧ m.H (c i).z=0) ∨
        (m.H (c i).a=0 ∧ (c i).z=1)) ∧
      (⋃i,Ioo (c i).a (c i).z)=wholeCapFiniteUnion (nativeNegativeSet m) F ∧
      Pairwise (fun i j=>Disjoint (Ioo (c i).a (c i).z) (Ioo (c j).a (c j).z)) ∧
      (∀A: Set ℝ,MeasurableSet A→
        (∫u in 0..1,(A∩(wholeCapFiniteUnion (nativeNegativeSet m) F∪nativeActualContactSet m)).indicator
          (fun _=>1) (m.R u)*m.thermal u)≤
        (∫u in 0..1,(A∩nativeActualContactSet m).indicator (fun _=>1) (m.R u)*m.thermal u)+
        (∫u in 0..1,(nativeActualComparableCapUnion m c).indicator (fun _=>1) (m.R u)*m.thermal u)+
        (∑p:nativeActualBroadSliceIndex m c,
          ∫u in 0..1,(nativeActualBroadSlice m c p).indicator (fun _=>1) (m.R u)*m.thermal u)+
        (∫u in 0..min (8*m.U) 1,m.thermal u)) := by
  obtain ⟨c,hcase,hunion,hd⟩ := exists_actual_native_negative_cap_family m F hshort
  refine ⟨c,hcase,hunion,hd,?_⟩
  intro A hA
  rw [←hunion]
  exact actual_native_finite_cap_thermal_cover m c hd A hA

end OAI.SKFluctuations.LaplaceWindowFormalization
