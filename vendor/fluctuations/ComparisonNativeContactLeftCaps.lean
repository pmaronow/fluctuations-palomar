module

public import ComparisonNativeNegativeCapFamily

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3400000
attribute [local instance] Classical.propDecidable

def nativeContactLeftCaps (m:NativeBandModel) : Set ℝ :=
  {r | r∈nativeNegativeSet m ∧ m.H (sInf (ordConnectedComponent (nativeNegativeSet m) r))=0}

theorem nativeContactLeftCaps_component_subset (m:NativeBandModel) {r:ℝ}
    (hr:r∈nativeContactLeftCaps m) :
    ordConnectedComponent (nativeNegativeSet m) r⊆nativeContactLeftCaps m := by
  intro t ht
  refine ⟨ordConnectedComponent_subset ht,?_⟩
  rw [←ordConnectedComponent_eq ht]
  exact hr.2

theorem nativeContactLeftCaps_component (m:NativeBandModel) {r:ℝ}
    (hr:r∈nativeContactLeftCaps m) :
    ordConnectedComponent (nativeContactLeftCaps m) r=ordConnectedComponent (nativeNegativeSet m) r := by
  apply Subset.antisymm
  · intro t ht
    exact (mem_ordConnectedComponent.mp ht).trans (fun _ h=>h.1)
  · exact subset_ordConnectedComponent (self_mem_ordConnectedComponent.mpr hr.1)
      (nativeContactLeftCaps_component_subset m hr)

theorem nativeContactLeftCaps_open (m:NativeBandModel) : IsOpen (nativeContactLeftCaps m) := by
  rw [isOpen_iff_forall_mem_open]
  intro r hr
  exact ⟨ordConnectedComponent (nativeNegativeSet m) r,nativeContactLeftCaps_component_subset m hr,
    wholeCap_component_isOpen (nativeNegativeSet_open m) r,self_mem_ordConnectedComponent.mpr hr.1⟩

theorem nativeContactLeftCaps_subset (m:NativeBandModel) : nativeContactLeftCaps m⊆Ioo (0:ℝ) 1 :=
  fun _ h=>h.1.1

theorem nativeContactLeftCaps_negative (m:NativeBandModel) {r:ℝ}
    (hr:r∈nativeContactLeftCaps m) : m.H r<0 := hr.1.2

theorem nativeContactLeftCaps_contact_component (m:NativeBandModel) {r:ℝ}
    (hr:r∈nativeContactLeftCaps m) (hshort:nativeCapTravel m<1) :
    m.H (sInf (ordConnectedComponent (nativeContactLeftCaps m) r))=0 ∧
      (m.H (sSup (ordConnectedComponent (nativeContactLeftCaps m) r))=0 ∨
        sSup (ordConnectedComponent (nativeContactLeftCaps m) r)=1) := by
  rw [nativeContactLeftCaps_component m hr]
  obtain ⟨c,hA,hZ,_,hcase⟩ := actual_native_negative_component_endpoints m hr.1 hshort
  refine ⟨hr.2,?_⟩
  rcases hcase with h|h|h
  · exact Or.inl (hZ ▸ h.2)
  · exact Or.inl (hZ ▸ h.2)
  · exact Or.inr (hZ ▸ h.2)

theorem native_actual_cap_component (m:NativeBandModel) (c:NativeActualCapInterval m)
    (hcase:(m.H c.a=0 ∧ m.H c.z=0) ∨ (c.a=0 ∧ m.H c.z=0) ∨ (m.H c.a=0 ∧ c.z=1))
    {r:ℝ} (hr:r∈Ioo c.a c.z) :
    ordConnectedComponent (nativeNegativeSet m) r=Ioo c.a c.z := by
  have hsub : Ioo c.a c.z⊆nativeNegativeSet m :=
    fun t ht=>⟨⟨c.ha.trans_lt ht.1,ht.2.trans_le c.hz⟩,c.negative t ht⟩
  have hleft : m.H c.a=0 ∨ c.a=0 := by rcases hcase with h|h|h <;> tauto
  have hright : m.H c.z=0 ∨ c.z=1 := by rcases hcase with h|h|h <;> tauto
  have hnotA : c.a∉nativeNegativeSet m := by
    intro h
    rcases hleft with ha|ha
    · have hh:m.H c.a<0 := h.2
      rw [ha] at hh
      exact lt_irrefl _ hh
    · have hh:0< c.a := h.1.1
      rw [ha] at hh
      exact lt_irrefl _ hh
  have hnotZ : c.z∉nativeNegativeSet m := by
    intro h
    rcases hright with hz|hz
    · have hh:m.H c.z<0 := h.2
      rw [hz] at hh
      exact lt_irrefl _ hh
    · have hh:c.z<1 := h.1.2
      rw [hz] at hh
      exact lt_irrefl _ hh
  apply Subset.antisymm
  · intro t ht
    have hconnect := mem_ordConnectedComponent.mp ht
    constructor
    · by_contra hbad
      have hta:t≤ c.a := le_of_not_gt hbad
      rw [uIcc_of_ge (hta.trans hr.1.le)] at hconnect
      exact hnotA (hconnect ⟨hta,hr.1.le⟩)
    · by_contra hbad
      have hzt:c.z≤ t := le_of_not_gt hbad
      rw [uIcc_of_le (hr.2.le.trans hzt)] at hconnect
      exact hnotZ (hconnect ⟨hr.2.le,hzt⟩)
  · exact subset_ordConnectedComponent hr hsub

theorem native_actual_cap_subset_contactLeft_of_positive_mass (m:NativeBandModel)
    (c:NativeActualCapInterval m)
    (hcase:(m.H c.a=0 ∧ m.H c.z=0) ∨ (c.a=0 ∧ m.H c.z=0) ∨ (m.H c.a=0 ∧ c.z=1))
    (hmass:0< m.alpha.val.val c.a) : Ioo c.a c.z⊆nativeContactLeftCaps m := by
  have haH:m.H c.a=0 := by
    rcases hcase with h|h|h
    · exact h.1
    · have hh := hmass
      rw [h.1,m.alpha.property.1] at hh
      exact False.elim (lt_irrefl _ hh)
    · exact h.1
  intro r hr
  refine ⟨⟨⟨c.ha.trans_lt hr.1,hr.2.trans_le c.hz⟩,c.negative r hr⟩,?_⟩
  rw [native_actual_cap_component m c hcase hr,csInf_Ioo c.haz]
  exact haH

theorem native_actual_cap_contactLeft_wholeUnit (m:NativeBandModel) (c:NativeActualCapInterval m)
    (hcase:(m.H c.a=0 ∧ m.H c.z=0) ∨ (c.a=0 ∧ m.H c.z=0) ∨ (m.H c.a=0 ∧ c.z=1))
    (hmass:0< m.alpha.val.val c.a) {r:ℝ} (hr:r∈Ioo c.a c.z) :
    wholeUnit (nativeContactLeftCaps m) r=Ioo c.a c.z := by
  have hmem := native_actual_cap_subset_contactLeft_of_positive_mass m c hcase hmass hr
  simp only [wholeUnit,ite_eq_left hmem]
  rw [nativeContactLeftCaps_component m hmem,native_actual_cap_component m c hcase hr]

end OAI.SKFluctuations.LaplaceWindowFormalization
