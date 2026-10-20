module

public import ComparisonNativeSelectedMaskWitnesses
public import ComparisonSelectedUnitEndpointCoordinates
public import ComparisonNativeMaskMassTransport
public import ComparisonCapInteriorCutTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3600000
attribute [local instance] Classical.propDecidable

structure NativeConstructedCoordinates {ι : Type} (steps : List (GaussianStep ι))
    (J : Finset (Fin (steps.length+1))) (r : Fin (steps.length+1) → ℝ) (U : Set ℝ) where
  K : ℕ
  unit : Fin (steps.length+1) → Fin K
  x : ℕ → ℝ
  start : x 0=0
  width : x K=physicalWindowMass steps 0 J
  strict : J.Nonempty → ∀u : Fin K,x u.val<x (u.val+1)
  mass : ∀u : Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u.val
  classes : ∀i∈J,∀j∈J,unit i=unit j ↔ wholeUnit U (r i)=wholeUnit U (r j)
  order : MonotoneOn unit (J:Set (Fin (steps.length+1)))

theorem exists_nativeConstructedCoordinates {ι : Type} (steps : List (GaussianStep ι))
    (ha : OrderedSteps 0 steps) (J : Finset (Fin (steps.length+1)))
    (hp : ∀i∈J,0<pathMassDifferences steps 0 i)
    (r : Fin (steps.length+1) → ℝ) (hr : Monotone r) (U : Set ℝ) :
    Nonempty (NativeConstructedCoordinates steps J r U) := by
  by_cases hn : J.Nonempty
  · obtain ⟨K,unit,x,_,h0,hwidth,hx,hmass,hclass,horder⟩ :=
      exists_finite_selected_unit_coordinates steps ha J hn hp (firstWholeUnitCell U r)
        ((firstWholeUnitCell_monotone U r hr).monotoneOn _)
    exact ⟨⟨K,unit,x,h0,hwidth,fun _=>hx,hmass,
      fun i hi j hj=>(hclass i hi j hj).trans (firstWholeUnitCell_eq_iff U r i j),horder⟩⟩
  · have he : J=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    subst J
    refine ⟨⟨1,fun _=>0,fun _=>0,rfl,?_,?_,?_,?_,?_⟩⟩
    · simp [physicalWindowMass]
    · simp
    · intro u
      simp [physicalSelectedUnitMass]
    · simp
    · intro i hi
      exact False.elim (by simpa using hi)

theorem physicalWindowMass_mem_Icc_one {ι : Type} (steps : List (GaussianStep ι))
    (ha : OrderedSteps 0 steps) (J : Finset (Fin (steps.length+1))) :
    physicalWindowMass steps 0 J∈Icc (0:ℝ) 1 := by
  have hp := pathMassDifferences_nonneg steps ha
  constructor
  · exact Finset.sum_nonneg (fun i _=>hp i)
  · calc
      physicalWindowMass steps 0 J ≤ ∑i : Fin (steps.length+1),pathMassDifferences steps 0 i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J) (fun i _ _=>hp i)
      _=1 := by simpa only [sub_zero] using sum_pathMassDifferences steps 0

theorem NativeConstructedCoordinates.strict_of_width {ι : Type}
    {steps : List (GaussianStep ι)} {J : Finset (Fin (steps.length+1))}
    {r : Fin (steps.length+1) → ℝ} {U : Set ℝ}
    (C : NativeConstructedCoordinates steps J r U) {δ : ℝ} (hδ : 0<δ)
    (hw : 2*δ ≤ C.x C.K) : ∀u : Fin C.K,C.x u.val<C.x (u.val+1) := by
  apply C.strict
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  have hzero : C.x C.K=0 := by rw [C.width,he]; simp [physicalWindowMass]
  linarith

theorem constructed_small_bins_mass_le {bins : ℕ} (width : Fin bins → ℝ) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    (∑b : Fin bins,if width b<2*δ then width b else 0) ≤ 2*(bins:ℝ)*δ := by
  calc
    _ ≤ ∑_b : Fin bins,2*δ := Finset.sum_le_sum (fun b _=>by split_ifs with h;exact h.le;positivity)
    _=_ := by simp; ring

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

def comparisonConstructedRows {ι : Type} {τ : Type*}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ) (ag zg : ℝ) :
    Finset (Fin ((sampleClockSteps q 0 as).length+1)) :=
  (comparisonNativeSelectedRows hc hk hkc hm hM q α as a z H D).filter (fun i=>
    0<pathMassDifferences (sampleClockSteps q 0 as) 0 i ∧
    ag ≤ comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i.val) ∧
    comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as (i.val+1)) ≤ zg)

def comparisonConstructedRowRadius {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (i : Fin ((sampleClockSteps q 0 as).length+1)) : ℝ :=
  comparisonSweepQuantile hc hk hkc hm hM α (physicalCutMass 0 (sampleClockSteps q 0 as) i.val)

def comparisonConstructedBin {τ : Type*}
    (n bins : ℕ) (q : ℝ → FeatureIndex n → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ) (ag zg w : ℝ) (U : Set ℝ)
    (b : Fin bins) : Finset (Fin ((sampleClockSteps q 0 as).length+1)) :=
  NativeUnitHeight.bin
    (fun i=>physicalPathSecondMoment n (sampleClockSteps q 0 as) (q 0) i.val)
    (comparisonConstructedRows hc hk hkc hm hM q α as a z H D ag zg)
    (firstWholeUnitCell U (comparisonConstructedRowRadius hc hk hkc hm hM q α as)) bins w b

theorem comparisonConstructedRowRadius_eq {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (i : Fin ((sampleClockSteps q 0 as).length+1)) :
    comparisonConstructedRowRadius hc hk hkc hm hM q α as i=
      comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i.val) := by
  unfold comparisonConstructedRowRadius
  rw [physicalCutMass_sampleClockSteps q 0 as i.val (by
    simpa only [sampleClockSteps_length] using Nat.le_of_lt_succ i.isLt)]

theorem comparisonConstructedRowRadius_monotone {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as) : Monotone (comparisonConstructedRowRadius hc hk hkc hm hM q α as) := by
  intro i j hij
  exact (comparisonSweepQuantile_monotone hc hk hkc hm hM α)
    (physicalCutMass_monotone _ (sampleClockSteps_ordered q as ho) hij)

theorem comparisonConstructedRows_subset {ι : Type} {τ : Type*}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ) (ag zg : ℝ) :
    comparisonConstructedRows hc hk hkc hm hM q α as a z H D ag zg⊆
      comparisonNativeSelectedRows hc hk hkc hm hM q α as a z H D := Finset.filter_subset _ _

theorem comparisonConstructedBin_subset {τ : Type*}
    (n bins : ℕ) (q : ℝ → FeatureIndex n → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ) (ag zg w : ℝ) (U : Set ℝ) (b : Fin bins) :
    comparisonConstructedBin hc hk hkc hm hM n bins q α as a z H D ag zg w U b⊆
      comparisonConstructedRows hc hk hkc hm hM q α as a z H D ag zg := Finset.filter_subset _ _

theorem comparisonConstructedBin_exists_coordinates {τ : Type*}
    (n bins : ℕ) (q : ℝ → FeatureIndex n → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass) (ho : MassOrdered 0 as)
    (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ) (ag zg w : ℝ) (U : Set ℝ) (b : Fin bins) :
    Nonempty (NativeConstructedCoordinates (sampleClockSteps q 0 as)
      (comparisonConstructedBin hc hk hkc hm hM n bins q α as a z H D ag zg w U b)
      (comparisonConstructedRowRadius hc hk hkc hm hM q α as) U) := by
  apply exists_nativeConstructedCoordinates _ (sampleClockSteps_ordered q as ho) _ _ _
    (comparisonConstructedRowRadius_monotone hc hk hkc hm hM q α as ho) U
  intro i hi
  have hh := comparisonConstructedBin_subset hc hk hkc hm hM n bins q α as a z H D ag zg w U b hi
  exact (Finset.mem_filter.mp hh).2.1

theorem comparisonOriginalCell_mass_pos {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (i : Fin ((sampleClockSteps q 0 as).length+1)) (hi : i.val<as.length)
    {r : ℝ} (hr : r∈Ioc
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i.val))
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as (i.val+1)))) :
    0<pathMassDifferences (sampleClockSteps q 0 as) 0 i := by
  rw [pathMassDifferences_eq_cutMass,
    physicalCutMass_sampleClockSteps q 0 as i.val hi.le,
    physicalCutMass_sampleClockSteps q 0 as (i.val+1) (by omega),sub_pos]
  by_contra h
  have hh := (comparisonSweepQuantile_monotone hc hk hkc hm hM α) (le_of_not_gt h)
  exact (not_lt_of_ge hh) (hr.1.trans_le hr.2)

theorem comparisonConstructedRows_cell_eventually {ι : Type} {τ : Type*}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hlim : Tendsto mesh atTop (𝓝 0))
    (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ) {ag zg : ℝ}
    (hag : 0 ≤ ag) (hzg : zg ≤ 1) {r : ℝ} (hr : r∈Ioo ag zg) (hrD : r∉D)
    (hsel : r∈NativeSelectedMask.fixedSupport a z H) :
    ∀ᶠ j in atTop,∃i : Fin ((sampleClockSteps q 0 (as j)).length+1),
      i∈comparisonConstructedRows hc hk hkc hm hM q α (as j) a z H D ag zg ∧
      i.val<(as j).length ∧
      r∈Ioc (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i.val))
        (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) (i.val+1))) := by
  let p := fun j i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)
  obtain ⟨_,_,_,hdiam,ht⟩ := comparisonNativeSelectedRows_grid hc hk hkc hm hM α as mesh ho he hmesh hlim
  have hcella := comparisonNativeSelectedRows_cell_eventually hc hk hkc hm hM q α
    as mesh ho he hmesh hlim a z H D ⟨hag.trans_lt hr.1,hr.2.trans_le hzg⟩ hrD hsel
  filter_upwards [hcella,NativeSelectedMask.cells_eventually_subset_open p _ _ hdiam ht
    (Ioo ag zg) isOpen_Ioo hr] with j hj hband
  obtain ⟨i,hi,hil,hri⟩ := hj
  have hle := hri.1.le.trans hri.2
  have hl := hband i.val hil hri (left_mem_Icc.mpr hle)
  have hu := hband i.val hil hri (right_mem_Icc.mpr hle)
  refine ⟨i,Finset.mem_filter.mpr ⟨hi,?_,hl.1.le,hu.2.le⟩,hil,hri⟩
  exact comparisonOriginalCell_mass_pos hc hk hkc hm hM q α (as j) i hil hri

theorem comparisonConstructedRows_support_eventually {ι : Type} {τ : Type*}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hlim : Tendsto mesh atTop (𝓝 0))
    (a z : τ → ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H (Icc (0:ℝ) 1)) (D : Finset ℝ)
    {ag zg : ℝ} (hag : 0 ≤ ag) (hzg : zg ≤ 1)
    {r : ℝ} (hrD : r∉D) (hrz : ∀t,r≠z t) (hrag : r≠ag) (hrzg : r≠zg) :
    ∀ᶠ j in atTop,
      (r∈NativeSelectedMask.finiteSupport
        (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i))
        (comparisonConstructedRows hc hk hkc hm hM q α (as j) a z H D ag zg) ↔
          r∈Ioo ag zg ∩ NativeSelectedMask.fixedSupport a z H) := by
  by_cases hband : r∈Ioo ag zg
  · by_cases hsel : r∈NativeSelectedMask.fixedSupport a z H
    · filter_upwards [comparisonConstructedRows_cell_eventually hc hk hkc hm hM q α
        as mesh ho he hmesh hlim a z H D hag hzg hband hrD hsel] with j hj
      obtain ⟨i,hi,_,hri⟩ := hj
      exact ⟨fun _=>⟨hband,hsel⟩,fun _=>⟨i,hi,hri⟩⟩
    · obtain ⟨_,_,hp,hdiam,ht⟩ := comparisonNativeSelectedRows_grid hc hk hkc hm hM α as mesh ho he hmesh hlim
      filter_upwards [NativeSelectedMask.outside_cell_eventually a z H hH D
        (fun j i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i))
        _ _ hp hdiam ht hsel hrz] with j hj
      constructor
      · rintro ⟨i,hi,hri⟩
        have hglobal := (Finset.mem_filter.mp hi).1
        have hh := (comparisonNativeSelectedRows_mem hc hk hkc hm hM q α (as j) a z H D i).mp hglobal
        exact False.elim (hj ⟨i.val,hh.1,hh.2,hri⟩)
      · exact fun h=>False.elim (hsel h.2)
  · apply Eventually.of_forall
    intro j
    constructor
    · rintro ⟨i,hi,hri⟩
      have hh := (Finset.mem_filter.mp hi).2
      have hrr : r∈Ioo ag zg :=
        ⟨lt_of_le_of_ne (hh.2.1.trans hri.1.le) hrag.symm,lt_of_le_of_ne (hri.2.trans hh.2.2) hrzg⟩
      exact False.elim (hband hrr)
    · exact fun h=>False.elim (hband h.1)

end
end OAI.SKFluctuations.LaplaceWindowFormalization
