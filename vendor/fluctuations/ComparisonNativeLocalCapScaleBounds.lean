module

public import ComparisonNativeLocalCapThermalCover

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4000000
attribute [local instance] Classical.propDecidable

theorem native_whole_broad_slice_width_bounds {m : NativeBandModel}
    {c : NativeActualCapInterval m} (f : NativeWholeCapBroadSampler m c) (i : Fin f.count) :
    f.scale i ≤ (∫r in f.slice i,deriv m.alpha.val.val r) ∧
      (∫r in f.slice i,deriv m.alpha.val.val r) ≤ 4*f.scale i ∧
      (∫r in f.slice i,deriv m.alpha.val.val r) ≤ 1 := by
  have hg := f.geometry i
  have hn := f.nodes_mem i
  rw [nativeBroadMassSlice_mass m.hc m.hk m.hkc m.hm m.hM m.alpha hn.1 hn.2 hg.2.2.2.2.2.2]
  exact ⟨hg.2.1,by linarith [hn.1.1,hg.2.2.2.1],by linarith [hn.1.1,hn.2.2]⟩

theorem native_relevant_broad_slice_scale_bounds {ι : Type*} [Fintype ι]
    (m : NativeBandModel) (c : ι → NativeActualCapInterval m) (A : Set ℝ)
    {lo hi : ℝ} (hA : ∀r∈A, lo ≤ m.alpha.val.val r ∧ m.alpha.val.val r ≤ hi)
    (p : NativeRelevantBroadSlice m c A) :
    lo/4 ≤ nativeActualBroadSliceScale m c p.val ∧
      nativeActualBroadSliceScale m c p.val ≤ 2*hi := by
  obtain ⟨r,hrA,hr⟩ := p.property
  let f := nativeActualBroadCapSampler m c p.val.1
  let i := p.val.2
  have hg := f.geometry i
  have hn := f.nodes_mem i
  have hm := native_mass_slice_profile_mem m hn.1 hn.2 hr
  have ha := hA r hrA
  change lo/4 ≤ f.scale i ∧ f.scale i ≤ 2*hi
  constructor <;> linarith [hg.2.2.1,hg.2.2.2.1,hm.1,hm.2]

theorem native_relevant_comparable_cap_dyadic_scale {ι : Type*} [Fintype ι]
    (m : NativeBandModel) (c : ι → NativeActualCapInterval m) (A : Set ℝ)
    {lo hi : ℝ} (hA : ∀r∈A, lo ≤ m.alpha.val.val r ∧ m.alpha.val.val r ≤ hi)
    (i : NativeRelevantComparableCap m c A) :
    ∃j : comparisonMassDyadicIndices m.U,
      lo/16 ≤ m.U*(2:ℝ)^(j:ℕ) ∧ m.U*(2:ℝ)^(j:ℕ) ≤ hi ∧
      m.U*(2:ℝ)^(j:ℕ) ≤ m.alpha.val.val (c i.val).a ∧
      m.alpha.val.val (c i.val).z ≤ min (16*(m.U*(2:ℝ)^(j:ℕ))) 1 := by
  obtain ⟨r,hrA,hr⟩ := i.property.2
  have hApoint := hA r hrA
  have hl := m.alpha.val.property.2 hr.1.le
  have hz := m.alpha.val.property.2 hr.2.le
  have hco := le_of_not_gt i.property.1.1
  have hUA : m.U ≤ m.alpha.val.val (c i.val).a := by
    by_contra hh
    have hh' := le_of_not_ge hh
    rw [max_eq_right hh'] at hco
    exact i.property.1.2.not_ge hco
  rw [max_eq_left hUA] at hco
  obtain ⟨j,hj,hj'⟩ := comparison_mass_dyadic_cover m.hU hUA (m.alpha.val.property.1 _).2
  refine ⟨j,?_,hj.trans (hl.trans hApoint.2),hj,?_⟩
  · linarith [hApoint.1]
  · exact le_min (by linarith) (m.alpha.val.property.1 _).2

theorem native_relevant_broad_slice_card_le_log_count {ι : Type*} [Fintype ι]
    (m : NativeBandModel) (c : ι → NativeActualCapInterval m) (A : Set ℝ)
    (hd : Pairwise (fun i j => Disjoint (Ioo (c i).a (c i).z) (Ioo (c j).a (c j).z))) :
    Fintype.card (NativeRelevantBroadSlice m c A) ≤
      4*(Nat.ceil (Real.log (1/m.U)/Real.log 2)+1) := by
  have hc : Fintype.card (NativeRelevantBroadSlice m c A) ≤
      Fintype.card (nativeActualBroadSliceIndex m c) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  exact hc.trans (nativeActualBroadSlice_card_le_log_count m c hd)

end OAI.SKFluctuations.LaplaceWindowFormalization
