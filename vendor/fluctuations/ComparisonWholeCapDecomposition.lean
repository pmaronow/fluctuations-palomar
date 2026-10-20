module

public import Mathlib

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.WholeUnitSideKernel
open Set MeasureTheory Filter
open scoped Topology ENNReal
attribute [local instance] Classical.propDecidable

theorem wholeCap_component_isOpen {U : Set ℝ} (hU : IsOpen U) (r : ℝ) :
    IsOpen (ordConnectedComponent U r) := by
  apply isOpen_iff_mem_nhds.mpr
  intro t ht
  rw [ordConnectedComponent_eq ht]
  exact ordConnectedComponent_mem_nhds.mpr (hU.mem_nhds (ordConnectedComponent_subset ht))

theorem wholeCap_representatives_pairwiseDisjoint (U : Set ℝ) :
    (ordConnectedSection U).PairwiseDisjoint (ordConnectedComponent U) := by
  intro r hr t ht hrt
  apply disjoint_left.mpr
  intro z hzR hzT
  exact hrt (eq_of_mem_ordConnectedSection_of_uIcc_subset hr ht
    (mem_ordConnectedComponent_trans hzR (mem_ordConnectedComponent_comm.mpr hzT)))

theorem wholeCap_representatives_countable {U : Set ℝ} (hU : IsOpen U) :
    (ordConnectedSection U).Countable :=
  (wholeCap_representatives_pairwiseDisjoint U).countable_of_isOpen
    (fun r _ => wholeCap_component_isOpen hU r)
    (fun r hr => nonempty_ordConnectedComponent.mpr (ordConnectedSection_subset hr))

theorem wholeCap_representatives_union (U : Set ℝ) :
    (⋃ r ∈ ordConnectedSection U, ordConnectedComponent U r)=U := by
  apply Subset.antisymm
  · exact iUnion₂_subset (fun _ _ => ordConnectedComponent_subset)
  · intro r hr
    exact mem_iUnion₂.mpr ⟨ordConnectedProj U ⟨r,hr⟩,⟨⟨r,hr⟩,rfl⟩,
      mem_ordConnectedComponent_ordConnectedProj U ⟨r,hr⟩⟩

def wholeCapFiniteUnion (U : Set ℝ) (F : Finset (ordConnectedSection U)) : Set ℝ :=
  ⋃ r ∈ F, ordConnectedComponent U r.val

theorem wholeCapFiniteUnion_subset (U : Set ℝ) (F : Finset (ordConnectedSection U)) :
    wholeCapFiniteUnion U F⊆U := iUnion₂_subset (fun _ _ => ordConnectedComponent_subset)

theorem wholeCapFiniteUnion_isOpen {U : Set ℝ} (hU : IsOpen U)
    (F : Finset (ordConnectedSection U)) : IsOpen (wholeCapFiniteUnion U F) :=
  isOpen_iUnion fun r => isOpen_iUnion fun _ => wholeCap_component_isOpen hU r.val

theorem wholeCapFiniteUnion_mono (U : Set ℝ) : Monotone (wholeCapFiniteUnion U) := by
  intro F G hFG r hr
  obtain ⟨z,hz,hrz⟩ := mem_iUnion₂.mp hr
  exact mem_iUnion₂.mpr ⟨z,hFG hz,hrz⟩

theorem wholeCapFiniteUnion_whole_component (U : Set ℝ)
    (F : Finset (ordConnectedSection U)) (r : ordConnectedSection U) :
    r ∈ F → ordConnectedComponent U r.val⊆wholeCapFiniteUnion U F := by
  intro hr t ht
  exact mem_iUnion₂.mpr ⟨r,hr,ht⟩

theorem wholeCapFiniteUnion_disjoint_unselected (U : Set ℝ)
    (F : Finset (ordConnectedSection U)) (r : ordConnectedSection U) (hr : r ∉ F) :
    Disjoint (ordConnectedComponent U r.val) (wholeCapFiniteUnion U F) := by
  apply disjoint_left.mpr
  intro t ht htf
  obtain ⟨z,hz,htz⟩ := mem_iUnion₂.mp htf
  have hne : r.val ≠ z.val := by
    intro heq
    exact hr (Subtype.ext_iff.mpr heq ▸ hz)
  exact (wholeCap_representatives_pairwiseDisjoint U r.property z.property hne).le_bot ⟨ht,htz⟩

theorem countable_finset_exhaustion (ι : Type*) [Countable ι] :
    ∃ F : ℕ → Finset ι, Monotone F ∧ ∀ r : ι, ∃ n, r ∈ F n := by
  let : Encodable ι := Encodable.ofCountable ι
  let F : ℕ → Finset ι := fun n =>
    (Finset.range n).preimage (Encodable.encode : ι → ℕ) Encodable.encode_injective.injOn
  refine ⟨F,?_,?_⟩
  · intro n k hnk r hr
    have hrn : Encodable.encode r < n := by simpa only [F,Finset.mem_preimage,Finset.mem_range] using hr
    simpa only [F,Finset.mem_preimage,Finset.mem_range] using hrn.trans_le hnk
  · intro r
    exact ⟨Encodable.encode r+1,by simp [F]⟩

theorem wholeCap_finite_selection_tendsto {U : Set ℝ} (hU : IsOpen U)
    (μ : Measure ℝ) (hfinite : μ U ≠ ∞) :
    ∃ F : ℕ → Finset (ordConnectedSection U), Monotone F ∧
      (∀ r : ordConnectedSection U, ∃ n, r ∈ F n) ∧
      Tendsto (fun n => μ (U\wholeCapFiniteUnion U (F n))) atTop (𝓝 0) := by
  let : Countable (ordConnectedSection U) := (wholeCap_representatives_countable hU).to_subtype
  obtain ⟨F,hF,hcover⟩ := countable_finset_exhaustion (ordConnectedSection U)
  refine ⟨F,hF,hcover,?_⟩
  let tail := fun n => U\wholeCapFiniteUnion U (F n)
  have htail : Antitone tail := by
    intro n k hnk
    exact sdiff_subset_sdiff Subset.rfl (wholeCapFiniteUnion_mono U (hF hnk))
  have hmeas : ∀ n, NullMeasurableSet (tail n) μ := fun n =>
    (hU.measurableSet.diff (wholeCapFiniteUnion_isOpen hU (F n)).measurableSet).nullMeasurableSet
  have hzero : (⋂ n, tail n)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro r hr
    have hrU : r ∈ U := (mem_iInter.mp hr 0).1
    obtain ⟨z,hz,hrz⟩ := mem_iUnion₂.mp ((wholeCap_representatives_union U).symm ▸ hrU)
    obtain ⟨n,hn⟩ := hcover ⟨z,hz⟩
    exact (mem_iInter.mp hr n).2 (mem_iUnion₂.mpr ⟨⟨z,hz⟩,hn,hrz⟩)
  have hh := tendsto_measure_iInter_atTop hmeas htail
    ⟨0,ne_top_of_le_ne_top hfinite (measure_mono sdiff_subset)⟩
  simpa only [hzero,measure_empty,Function.comp_def,tail] using hh

theorem wholeCap_exists_finite_selection {U : Set ℝ} (hU : IsOpen U)
    (μ : Measure ℝ) (hfinite : μ U ≠ ∞) {epsilon : ℝ≥0∞} (hepsilon : 0 < epsilon) :
    ∃ F : Finset (ordConnectedSection U), μ (U\wholeCapFiniteUnion U F)<epsilon := by
  obtain ⟨F,_,_,htail⟩ := wholeCap_finite_selection_tendsto hU μ hfinite
  obtain ⟨n,hn⟩ := (htail.eventually (Iio_mem_nhds hepsilon)).exists
  exact ⟨F n,hn⟩

def wholeCapRetainedRegion (a b : ℝ) (U : Set ℝ)
    (F : Finset (ordConnectedSection U)) : Set ℝ := (Icc a b\U)∪wholeCapFiniteUnion U F

theorem wholeCapRetainedRegion_contact (a b : ℝ) (U : Set ℝ)
    (F : Finset (ordConnectedSection U)) : Icc a b\U⊆wholeCapRetainedRegion a b U F :=
  subset_union_left

theorem wholeCapRetainedRegion_partition {a b : ℝ} {U : Set ℝ} (hU : U⊆Icc a b)
    (F : Finset (ordConnectedSection U)) :
    wholeCapRetainedRegion a b U F ∪ (U\wholeCapFiniteUnion U F)=Icc a b ∧
      Disjoint (wholeCapRetainedRegion a b U F) (U\wholeCapFiniteUnion U F) := by
  constructor
  · ext r
    constructor
    · rintro ((hr|hr)|hr)
      · exact hr.1
      · exact hU (wholeCapFiniteUnion_subset U F hr)
      · exact hU hr.1
    · intro hr
      by_cases hrU : r∈U
      · by_cases hrF : r∈wholeCapFiniteUnion U F
        · exact Or.inl (Or.inr hrF)
        · exact Or.inr ⟨hrU,hrF⟩
      · exact Or.inl (Or.inl ⟨hr,hrU⟩)
  · apply disjoint_left.mpr
    intro r hr hrt
    rcases hr with hr|hr
    · exact hr.2 hrt.1
    · exact hrt.2 hr

end OAI.SKFluctuations.WholeUnitSideKernel
