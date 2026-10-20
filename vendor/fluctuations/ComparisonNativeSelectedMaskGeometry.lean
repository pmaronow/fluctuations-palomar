module

public import ComparisonContactCover
public import ComparisonNativeVarianceBinGeometry
public import ComparisonNativeContactColumnConvergence
public import Mathlib.Topology.Sequences

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2400000
attribute [local instance] Classical.propDecidable

namespace NativeSelectedMask

def fixedSupport {τ : Type*} (a z : τ → ℝ) (H : ℝ → ℝ) : Set ℝ :=
  {r | (∃t,r ∈ Ioo (a t) (z t)) ∨ H r=0}

def rowSelected {τ : Type*} (a z : τ → ℝ) (H p : ℝ → ℝ)
    (nodes : ℕ → ℝ) (D : Finset ℝ) (i : ℕ) : Prop :=
  (∀d ∈ D,p (nodes i)≠d) ∧
  ((∃t,p (nodes i) ∈ Ioo (a t) (z t) ∧ p (nodes (i+1))   ≤   z t) ∨
    ∃r ∈ Icc (p (nodes i)) (p (nodes (i+1))),H r=0)

def cellSupport (p : ℕ → ℝ) (N : ℕ) (P : ℕ → Prop) : Set ℝ :=
  {r | ∃i<N,P i ∧ r ∈ Ioc (p i) (p (i+1))}

theorem cellSupport_measurable (p : ℕ → ℝ) (N : ℕ) (P : ℕ → Prop) :
    MeasurableSet (cellSupport p N P) := by
  have he : cellSupport p N P=⋃i:ℕ,if i<N ∧ P i then Ioc (p i) (p (i+1)) else ∅ := by
    ext r
    simp only [cellSupport,mem_ofPred_eq,mem_iUnion]
    constructor
    · rintro ⟨i,hi,hP,hr⟩
      exact ⟨i,by rw [ite_eq_left (show i<N ∧ P i from ⟨hi,hP⟩)]; exact hr⟩
    · rintro ⟨i,hi⟩
      split_ifs at hi with h
      · exact ⟨i,h.1,h.2,hi⟩
      · exact False.elim hi
  rw [he]
  apply MeasurableSet.iUnion
  intro i
  split_ifs <;> simp only [measurableSet_Ioc,MeasurableSet.empty]

theorem cell_exists (p : ℕ → ℝ) (N : ℕ) {r : ℝ}
    (h0 : p 0<r) (hN : r   ≤   p N) : ∃i<N,r ∈ Ioc (p i) (p (i+1)) := by
  obtain ⟨i,hi,_,hr⟩ := contactMeetingCells_cover (fun _=>0) id p N h0 hN rfl
  exact ⟨i,hi,hr⟩

theorem cells_eventually_subset_open
    (p : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (mesh : ℕ → ℝ)
    (hmesh : ∀j i,i<N j → p j (i+1)-p j i    ≤    mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) (G : Set ℝ) (hG : IsOpen G)
    {r : ℝ} (hr : r ∈ G) :
    ∀ᶠ j in atTop,∀i<N j,r ∈ Ioc (p j i) (p j (i+1)) →
      Icc (p j i) (p j (i+1)) ⊆ G := by
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hG r hr
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with j hj
  intro i hi hri t ht
  apply hball
  rw [Metric.mem_ball,Real.dist_eq]
  exact (abs_le.mpr ⟨by linarith [hri.2,ht.1,hmesh j i hi],
    by linarith [hri.1,ht.2,hmesh j i hi]⟩).trans_lt hj

theorem retained_cap_cell_eventually {τ : Type*}
    (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ)
    (p : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (mesh : ℕ → ℝ)
    (h0 : ∀j,p j 0=0) (hN : ∀j,p j (N j)=1)
    (hmesh : ∀j i,i<N j → p j (i+1)-p j i    ≤    mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1) (hrD : r ∉ D)
    (t : τ) (hrt : r ∈ Ioo (a t) (z t)) :
    ∀ᶠ j in atTop,∃i<N j,rowSelected a z H id (p j) D i ∧
      r ∈ Ioc (p j i) (p j (i+1)) := by
  have hopen : IsOpen (Ioo (a t) (z t) ∩ (D:Set ℝ)ᶜ) :=
    isOpen_Ioo.inter D.finite_toSet.isClosed.isOpen_compl
  filter_upwards [cells_eventually_subset_open p N mesh hmesh hlim _ hopen ⟨hrt,hrD⟩] with j hj
  obtain ⟨i,hi,hri⟩ := cell_exists (p j) (N j) (by simpa [h0 j] using hr.1)
    (by simpa [hN j] using hr.2.le)
  have hle : p j i   ≤   p j (i+1) := hri.1.le.trans hri.2
  have hl := hj i hi hri (left_mem_Icc.mpr hle)
  have hh := hj i hi hri (right_mem_Icc.mpr hle)
  refine ⟨i,hi,⟨?_,Or.inl ⟨t,hl.1,hh.1.2.le⟩⟩,hri⟩
  intro d hd heq
  change p j i=d at heq
  exact hl.2 (by simpa only [Finset.mem_coe,heq] using hd)

theorem contact_cell_eventually {τ : Type*}
    (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ)
    (p : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (mesh : ℕ → ℝ)
    (h0 : ∀j,p j 0=0) (hN : ∀j,p j (N j)=1)
    (hmesh : ∀j i,i<N j → p j (i+1)-p j i    ≤    mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1) (hrD : r ∉ D) (hHr : H r=0) :
    ∀ᶠ j in atTop,∃i<N j,rowSelected a z H id (p j) D i ∧
      r ∈ Ioc (p j i) (p j (i+1)) := by
  filter_upwards [cells_eventually_subset_open p N mesh hmesh hlim (D:Set ℝ)ᶜ
    D.finite_toSet.isClosed.isOpen_compl hrD] with j hj
  obtain ⟨i,hi,hri⟩ := cell_exists (p j) (N j) (by simpa [h0 j] using hr.1)
    (by simpa [hN j] using hr.2.le)
  refine ⟨i,hi,⟨?_,Or.inr ⟨r,⟨hri.1.le,hri.2⟩,hHr⟩⟩,hri⟩
  intro d hd heq
  change p j i=d at heq
  have hle : p j i   ≤   p j (i+1) := hri.1.le.trans hri.2
  exact hj i hi hri (left_mem_Icc.mpr hle) (by simpa only [Finset.mem_coe,heq] using hd)

theorem outside_cell_eventually {τ : Type*}
    (a z : τ → ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H (Icc (0:ℝ) 1))
    (D : Finset ℝ) (p : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (mesh : ℕ → ℝ)
    (hp : ∀j i,i   ≤   N j → p j i ∈ Icc (0:ℝ) 1)
    (hmesh : ∀j i,i<N j → p j (i+1)-p j i    ≤    mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {r : ℝ}
    (hr : r ∉ fixedSupport a z H) (hrz : ∀t,r≠z t) :
    ∀ᶠ j in atTop,r ∉ cellSupport (p j) (N j) (rowSelected a z H id (p j) D) := by
  have hcap : ∀t,r ∉ Ioo (a t) (z t) := fun t ht=>hr (Or.inl ⟨t,ht⟩)
  have hzero : H r≠0 := fun hz=>hr (Or.inr hz)
  obtain ⟨ε,hε,hclose⟩ := contactMeetingCells_small_potential H hH (abs_pos.mpr hzero)
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with j hj
  rintro ⟨i,hi,hsel,hri⟩
  rcases hsel.2 with ⟨t,hl,hh⟩ | ⟨s,hs,hHs⟩
  · exact hcap t ⟨hl.1.trans hri.1,lt_of_le_of_ne (hri.2.trans hh) (hrz t)⟩
  · exact (lt_irrefl |H r|) (hclose (p j i) (p j (i+1)) s r
      (hp j i hi.le) (hp j (i+1) (by omega)) ((hmesh j i hi).trans_lt hj) hs hHs hri)

theorem membership_eventually {τ : Type*}
    (a z : τ → ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H (Icc (0:ℝ) 1))
    (D : Finset ℝ) (p : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (mesh : ℕ → ℝ)
    (h0 : ∀j,p j 0=0) (hN : ∀j,p j (N j)=1)
    (hp : ∀j i,i   ≤   N j → p j i ∈ Icc (0:ℝ) 1)
    (hmesh : ∀j i,i<N j → p j (i+1)-p j i    ≤    mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {r : ℝ}
    (hr : r ∈ Ioo (0:ℝ) 1) (hrD : r ∉ D) (hrz : ∀t,r≠z t) :
    ∀ᶠ j in atTop,
      (r ∈ cellSupport (p j) (N j) (rowSelected a z H id (p j) D) ↔ r ∈ fixedSupport a z H) := by
  by_cases hsel : r ∈ fixedSupport a z H
  · have hw : ∀ᶠ j in atTop,r ∈ cellSupport (p j) (N j) (rowSelected a z H id (p j) D) := by
      rcases hsel with ⟨t,ht⟩ | hzero
      · exact retained_cap_cell_eventually a z H D p N mesh h0 hN hmesh hlim hr hrD t ht
      · exact contact_cell_eventually a z H D p N mesh h0 hN hmesh hlim hr hrD hzero
    exact hw.mono (fun _ hj=>⟨fun _=>hsel,fun _=>hj⟩)
  · exact (outside_cell_eventually a z H hH D p N mesh hp hmesh hlim hsel hrz).mono
      (fun _ hj=>⟨fun h=>False.elim (hj h),fun h=>False.elim (hsel h)⟩)

theorem index_interval_support (p : ℕ → ℝ) (hp : Monotone p)
    (N lo hi : ℕ) (P : ℕ → Prop) :
    cellSupport p N (fun i=>P i ∧ lo    ≤    i ∧ i    ≤    hi)=
      cellSupport p N P ∩ Ioc (p lo) (p (hi+1)) := by
  ext r
  constructor
  · rintro ⟨i,hiN,⟨hP,hlo,hhi⟩,hr⟩
    exact ⟨⟨i,hiN,hP,hr⟩,lt_of_le_of_lt (hp hlo) hr.1,
      hr.2.trans (hp (Nat.add_le_add_right hhi 1))⟩
  · rintro ⟨⟨i,hiN,hP,hr⟩,hl,hh⟩
    refine ⟨i,hiN,⟨hP,?_,?_⟩,hr⟩
    · by_contra h
      have hle : i+1   ≤   lo := by omega
      exact (not_lt_of_ge (hr.2.trans (hp hle))) hl
    · by_contra h
      have hle : hi+1   ≤   i := by omega
      exact (not_lt_of_ge (hh.trans (hp hle))) hr.1

theorem finite_endpoints_subsequence {β : Type*} [Fintype β]
    (e : ℕ → β → Icc (0:ℝ) 1) :
    ∃v : β → Icc (0:ℝ) 1,∃φ : ℕ → ℕ,StrictMono φ ∧
      ∀b,Tendsto (fun j=>(e (φ j) b).val) atTop (𝓝 (v b).val) := by
  obtain ⟨v,φ,hφ,hl⟩ := CompactSpace.tendsto_subseq e
  refine ⟨v,φ,hφ,fun b=>?_⟩
  exact continuous_subtype_val.continuousAt.tendsto.comp
    ((continuous_apply b).continuousAt.tendsto.comp hl)

theorem interval_membership_eventually (l u : ℕ → ℝ) {a z r : ℝ}
    (hl : Tendsto l atTop (𝓝 a)) (hu : Tendsto u atTop (𝓝 z))
    (hra : r≠a) (hrz : r≠z) :
    ∀ᶠ j in atTop,(r ∈ Ioc (l j) (u j) ↔ r ∈ Ioo a z) := by
  rcases lt_or_gt_of_ne hra with h | h
  · filter_upwards [(tendsto_order.mp hl).1 r h] with j hj
    exact ⟨fun hr=>False.elim (not_lt_of_ge hj.le hr.1),
      fun hr=>False.elim (not_lt_of_ge h.le hr.1)⟩
  · rcases lt_or_gt_of_ne hrz with hh | hh
    · filter_upwards [(tendsto_order.mp hl).2 r h,(tendsto_order.mp hu).1 r hh] with j hj hjj
      exact ⟨fun _=>⟨h,hh⟩,fun _=>⟨hj,hjj.le⟩⟩
    · filter_upwards [(tendsto_order.mp hu).2 r hh] with j hj
      exact ⟨fun hr=>False.elim (not_le_of_gt hj hr.2),
        fun hr=>False.elim (not_lt_of_ge hh.le hr.2)⟩

theorem bin_membership_eventually (A B : ℕ → Set ℝ) (F : Set ℝ)
    (l u : ℕ → ℝ) {a z r : ℝ}
    (hB : ∀j,B j=A j ∩ Ioc (l j) (u j))
    (hA : ∀ᶠ j in atTop,(r ∈ A j ↔ r ∈ F))
    (hl : Tendsto l atTop (𝓝 a)) (hu : Tendsto u atTop (𝓝 z))
    (hra : r≠a) (hrz : r≠z) :
    ∀ᶠ j in atTop,(r ∈ B j ↔ r ∈ F ∩ Ioo a z) := by
  filter_upwards [hA,interval_membership_eventually l u hl hu hra hrz] with j hj hij
  rw [hB j,mem_inter_iff,mem_inter_iff,hj,hij]

theorem masks_L1 (A : ℕ → Set ℝ) (F : Set ℝ)
    (hA : ∀j,MeasurableSet (A j)) (hF : MeasurableSet F)
    (hlim : ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),
      ∀ᶠ j in atTop,(r ∈ A j ↔ r ∈ F)) :
    Tendsto (fun j=>∫r in Ioo (0:ℝ) 1,
      |(A j).indicator (fun _=>(1:ℝ)) r-F.indicator (fun _=>(1:ℝ)) r|)
      atTop (𝓝 0) := by
  have hpoint : ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),Tendsto
      (fun j=>|(A j).indicator (fun _=>(1:ℝ)) r-F.indicator (fun _=>(1:ℝ)) r|)
      atTop (𝓝 0) := by
    filter_upwards [hlim] with r hr
    apply tendsto_const_nhds.congr'
    filter_upwards [hr] with j hj
    simp only [Set.indicator_apply,hj,sub_self,abs_zero]
  have hi : IntegrableOn (fun _ : ℝ=>(2:ℝ)) (Ioo (0:ℝ) 1) :=
    integrableOn_const (by simp)
  have hb j : ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),
      ‖|(A j).indicator (fun _=>(1:ℝ)) r-F.indicator (fun _=>(1:ℝ)) r|‖   ≤   2 := by
    apply ae_of_all
    intro r
    simp only [Set.indicator_apply]
    split_ifs <;> norm_num
  have hm j : AEStronglyMeasurable
      (fun r=>|(A j).indicator (fun _=>(1:ℝ)) r-F.indicator (fun _=>(1:ℝ)) r|)
      (volume.restrict (Ioo (0:ℝ) 1)) :=
    (((measurable_const.indicator (hA j)).sub (measurable_const.indicator hF)).abs).aestronglyMeasurable
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (fun _=>(2:ℝ)) hm hi hb hpoint

def finiteSupport {N : ℕ} (p : ℕ → ℝ) (J : Finset (Fin N)) : Set ℝ :=
  {r | ∃i∈J,r ∈ Ioc (p i.val) (p (i.val+1))}

theorem finiteSupport_measurable {N : ℕ} (p : ℕ → ℝ) (J : Finset (Fin N)) :
    MeasurableSet (finiteSupport p J) := by
  have he : finiteSupport p J=⋃i : Fin N,⋃(_ : i∈J),Ioc (p i.val) (p (i.val+1)) := by
    ext r
    simp only [finiteSupport,mem_ofPred_eq,mem_iUnion,exists_prop]
  rw [he]
  exact MeasurableSet.iUnion (fun _=>MeasurableSet.iUnion (fun _=>measurableSet_Ioc))

theorem native_bin_physical_interval {N K bins : ℕ}
    (p : ℕ → ℝ) (hp : Monotone p) (hpb : ∀i,p i∈Icc (0:ℝ) 1)
    (S : Fin N → ℝ) (J : Finset (Fin N)) (unit : Fin N → Fin K)
    (hS : Monotone S) (hu : MonotoneOn unit (J:Set (Fin N)))
    {w : ℝ} (hw : 0<w) (b : Fin bins) :
    ∃l u : Icc (0:ℝ) 1,
      finiteSupport p (NativeUnitHeight.bin S J unit bins w b)=
        finiteSupport p J ∩ Ioc l.val u.val := by
  by_cases hn : (NativeUnitHeight.bin S J unit bins w b).Nonempty
  · obtain ⟨lo,hi,hlo,hhi,hB⟩ := NativeUnitHeight.bin_eq_selected_index_interval S J unit hS hu hw b hn
    refine ⟨⟨p lo.val,hpb _⟩,⟨p (hi.val+1),hpb _⟩,?_⟩
    ext r
    constructor
    · rintro ⟨i,hiB,hri⟩
      rw [hB] at hiB
      obtain ⟨hiJ,hl,hh⟩ := Finset.mem_filter.mp hiB
      exact ⟨⟨i,hiJ,hri⟩,lt_of_le_of_lt (hp hl) hri.1,
        hri.2.trans (hp (Nat.add_le_add_right hh 1))⟩
    · rintro ⟨⟨i,hiJ,hri⟩,hl,hh⟩
      refine ⟨i,?_,hri⟩
      rw [hB]
      refine Finset.mem_filter.mpr ⟨hiJ,?_,?_⟩
      · by_contra h
        have hle : i.val+1   ≤   lo.val := by exact Nat.succ_le_of_lt (lt_of_not_ge h)
        exact (not_lt_of_ge (hri.2.trans (hp hle))) hl
      · by_contra h
        have hle : hi.val+1   ≤   i.val := by exact Nat.succ_le_of_lt (lt_of_not_ge h)
        exact (not_lt_of_ge (hh.trans (hp hle))) hri.1
  · refine ⟨⟨0,by simp⟩,⟨0,by simp⟩,?_⟩
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he,finiteSupport,Finset.notMem_empty,false_and,exists_false,
      ofPred_false,Ioc_self,inter_empty]

theorem finite_bin_limits {β : Type*} [Fintype β]
    (A : ℕ → Set ℝ) (B : ℕ → β → Set ℝ) (F : Set ℝ)
    (hF : MeasurableSet F) (hB : ∀j b,MeasurableSet (B j b))
    (hinterval : ∀j b,∃l u : Icc (0:ℝ) 1,B j b=A j ∩ Ioc l.val u.val)
    (hA : ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,(r∈A j ↔ r∈F)) :
    ∃l u : β → Icc (0:ℝ) 1,∃φ : ℕ → ℕ,StrictMono φ ∧ ∀b,
      (∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
        (r∈B (φ j) b ↔ r∈F ∩ Ioo (l b).val (u b).val)) ∧
      Tendsto (fun j=>∫r in Ioo (0:ℝ) 1,
        |(B (φ j) b).indicator (fun _=>(1:ℝ)) r-
          (F ∩ Ioo (l b).val (u b).val).indicator (fun _=>(1:ℝ)) r|) atTop (𝓝 0) := by
  choose ls us hrep using hinterval
  let e : ℕ → β × Bool → Icc (0:ℝ) 1 := fun j b=>if b.2 then us j b.1 else ls j b.1
  obtain ⟨v,φ,hφ,hlim⟩ := finite_endpoints_subsequence e
  let l := fun b=>v (b,false)
  let u := fun b=>v (b,true)
  refine ⟨l,u,φ,hφ,?_⟩
  intro b
  have hl : Tendsto (fun j=>(ls (φ j) b).val) atTop (𝓝 (l b).val) := by
    simpa only [e,Bool.false_eq_true,ite_false] using hlim (b,false)
  have hu : Tendsto (fun j=>(us (φ j) b).val) atTop (𝓝 (u b).val) := by
    simpa only [e,ite_true] using hlim (b,true)
  have hmem : ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
      (r∈B (φ j) b ↔ r∈F ∩ Ioo (l b).val (u b).val) := by
    filter_upwards [hA,ae_mono Measure.restrict_le_self (volume.ae_ne (l b).val),
      ae_mono Measure.restrict_le_self (volume.ae_ne (u b).val)] with r hr hrl hru
    exact bin_membership_eventually (fun j=>A (φ j)) (fun j=>B (φ j) b) F _ _
      (fun j=>hrep (φ j) b) (hφ.tendsto_atTop.eventually hr) hl hu hrl hru
  exact ⟨hmem,masks_L1 _ _ (fun j=>hB (φ j) b) (hF.inter measurableSet_Ioo) hmem⟩

theorem fixedSupport_band_measurable {τ : Type*} [Fintype τ]
    (a z : τ → ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H (Icc (0:ℝ) 1)) :
    MeasurableSet (Ioo (0:ℝ) 1 ∩ fixedSupport a z H) := by
  let He := fun r=>H (projIcc (0:ℝ) 1 zero_le_one r)
  have hHe : Continuous He :=
    (continuousOn_iff_continuous_domRestrict.mp hH).comp continuous_projIcc
  have hcap : MeasurableSet {r | ∃t,r ∈ Ioo (a t) (z t)} := by
    have he : {r | ∃t,r ∈ Ioo (a t) (z t)}=⋃t,Ioo (a t) (z t) := by ext r; simp
    rw [he]
    exact MeasurableSet.iUnion (fun _=>measurableSet_Ioo)
  have hE : Ioo (0:ℝ) 1 ∩ fixedSupport a z H=
      Ioo (0:ℝ) 1 ∩ ({r | ∃t,r ∈ Ioo (a t) (z t)} ∪ {r | He r=0}) := by
    ext r
    by_cases hr : r ∈ Ioo (0:ℝ) 1
    · have heq : He r=H r := by
        simp only [He,projIcc_of_mem zero_le_one ⟨hr.1.le,hr.2.le⟩]
      simp only [mem_inter_iff,hr,true_and,fixedSupport,mem_ofPred_eq,mem_union,heq]
    · simp only [mem_inter_iff,hr,false_and]
  rw [hE]
  exact measurableSet_Ioo.inter (hcap.union (isClosed_eq hHe continuous_const).measurableSet)

end NativeSelectedMask

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c   ≤   k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0   ≤   M 1)

def comparisonNativeSelectedRows {ι : Type} {τ : Type*}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ) :
    Finset (Fin ((sampleClockSteps q 0 as).length+1)) :=
  Finset.univ.filter (fun i=>i.val<as.length ∧ NativeSelectedMask.rowSelected
    a z H (comparisonSweepQuantile hc hk hkc hm hM α) (partitionPoint 0 as) D i.val)

theorem comparisonNativeSelectedRows_mem {ι : Type} {τ : Type*}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ)
    (i : Fin ((sampleClockSteps q 0 as).length+1)) :
    i ∈ comparisonNativeSelectedRows hc hk hkc hm hM q α as a z H D ↔
      i.val<as.length ∧ NativeSelectedMask.rowSelected a z H
        (comparisonSweepQuantile hc hk hkc hm hM α) (partitionPoint 0 as) D i.val := by
  simp only [comparisonNativeSelectedRows,Finset.mem_filter,Finset.mem_univ,true_and]

theorem comparisonNativeSelectedRows_grid
    (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hlim : Tendsto mesh atTop (𝓝 0)) :
    let p := fun j i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)
    (∀j,p j 0=0) ∧ (∀j,p j (as j).length=1) ∧
    (∀j i,i   ≤   (as j).length → p j i ∈ Icc (0:ℝ) 1) ∧
    (∀j i,i<(as j).length → p j (i+1)-p j i   ≤   mesh j/c) ∧
    Tendsto (fun j=>mesh j/c) atTop (𝓝 0) := by
  dsimp only
  have h0 : comparisonSweepQuantile hc hk hkc hm hM α 0=0 := by
    simpa only [α.property.1] using comparisonSweepQuantile_inverse hc hk hkc hm hM α
      (show (0:ℝ)∈Icc (0:ℝ) 1 by simp)
  have h1 : comparisonSweepQuantile hc hk hkc hm hM α 1=1 := by
    simpa only [α.property.2.1] using comparisonSweepQuantile_inverse hc hk hkc hm hM α
      (show (1:ℝ)∈Icc (0:ℝ) 1 by simp)
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j
    simpa only [partitionPoint,partitionValues_zero,id_eq] using h0
  · intro j
    simpa only [partitionPoint_length,he j] using h1
  · exact fun j i _=>comparisonSweepQuantile_bounds hc hk hkc hm hM α _
  · exact fun j i hi=>comparisonSampledRadius_point_mesh hc hk hkc hm hM α
      (as j) (ho j) (hmesh j) i hi
  · simpa only [zero_div] using hlim.div_const c

theorem comparisonNativeSelectedRows_cell_eventually {ι : Type} {τ : Type*}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hlim : Tendsto mesh atTop (𝓝 0))
    (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ)
    {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1) (hrD : r ∉ D)
    (hsel : r ∈ NativeSelectedMask.fixedSupport a z H) :
    ∀ᶠ j in atTop,∃i : Fin ((sampleClockSteps q 0 (as j)).length+1),
      i ∈ comparisonNativeSelectedRows hc hk hkc hm hM q α (as j) a z H D ∧
      i.val<(as j).length ∧
      r ∈ Ioc (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i.val))
        (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) (i.val+1))) := by
  let p := fun j i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)
  obtain ⟨h0,hN,hp,hdiam,ht⟩ := comparisonNativeSelectedRows_grid hc hk hkc hm hM α
    as mesh ho he hmesh hlim
  have hw : ∀ᶠ j in atTop,∃i<(as j).length,
      NativeSelectedMask.rowSelected a z H id (p j) D i ∧ r ∈ Ioc (p j i) (p j (i+1)) := by
    rcases hsel with ⟨t,htc⟩ | hzero
    · exact NativeSelectedMask.retained_cap_cell_eventually a z H D p _ _
        h0 hN hdiam ht hr hrD t htc
    · exact NativeSelectedMask.contact_cell_eventually a z H D p _ _
        h0 hN hdiam ht hr hrD hzero
  filter_upwards [hw] with j hj
  obtain ⟨i,hi,hrow,hri⟩ := hj
  let ii : Fin ((sampleClockSteps q 0 (as j)).length+1) :=
    ⟨i,by simpa only [sampleClockSteps_length] using Nat.lt_succ_of_lt hi⟩
  refine ⟨ii,?_,hi,hri⟩
  rw [comparisonNativeSelectedRows_mem]
  exact ⟨hi,hrow⟩

theorem comparisonNativeMask_on_cell {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps q 0 as).length+1) → Fin K)
    (i : Fin ((sampleClockSteps q 0 as).length+1)) (hi : i.val<as.length)
    {r : ℝ} (hr : r ∈ Ioc
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i.val))
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as (i.val+1)))) :
    comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J unit (fun _=>1) r=
      if i∈J then 1 else 0 := by
  unfold comparisonNativeUnitColumnWeight
  rw [radiusCellEnergyDensity_on_original_cell _
    (comparisonSweepQuantile_monotone hc hk hkc hm hM α) as ho _ hi hr,
    nativeSelectedColumn_atIndex]

theorem comparisonNativeSelectedRows_mask_eventually {ι : Type} {τ : Type*}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hlim : Tendsto mesh atTop (𝓝 0))
    (a z : τ → ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H (Icc (0:ℝ) 1))
    (D : Finset ℝ) {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1) (hrD : r ∉ D)
    (hrz : ∀t,r≠z t) :
    ∀ᶠ j in atTop,comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
      (comparisonNativeSelectedRows hc hk hkc hm hM q α (as j) a z H D)
      (fun _=>(0:Fin 1)) (fun _=>1) r=
      (NativeSelectedMask.fixedSupport a z H).indicator (fun _=>1) r := by
  by_cases hsel : r ∈ NativeSelectedMask.fixedSupport a z H
  · filter_upwards [comparisonNativeSelectedRows_cell_eventually hc hk hkc hm hM q α
      as mesh ho he hmesh hlim a z H D hr hrD hsel] with j hj
    obtain ⟨i,hi,hil,hri⟩ := hj
    rw [comparisonNativeMask_on_cell hc hk hkc hm hM q α (as j) (ho j) _ _ i hil hri,
      ite_eq_left hi,indicator_of_mem hsel]
  · let p := fun j i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)
    obtain ⟨h0,hN,hp,hdiam,ht⟩ := comparisonNativeSelectedRows_grid hc hk hkc hm hM α
      as mesh ho he hmesh hlim
    filter_upwards [NativeSelectedMask.outside_cell_eventually a z H hH D p _ _ hp hdiam ht hsel hrz]
      with j hj
    obtain ⟨i,hi,hri⟩ := NativeSelectedMask.cell_exists (p j) (as j).length
      (r:=r) (by rw [show p j 0=0 from h0 j]; exact hr.1)
      (by rw [show p j (as j).length=1 from hN j]; exact hr.2.le)
    let ii : Fin ((sampleClockSteps q 0 (as j)).length+1) :=
      ⟨i,by simpa only [sampleClockSteps_length] using Nat.lt_succ_of_lt hi⟩
    have hn : ii ∉ comparisonNativeSelectedRows hc hk hkc hm hM q α (as j) a z H D := by
      intro h
      have hrow := (comparisonNativeSelectedRows_mem hc hk hkc hm hM q α (as j) a z H D ii).mp h
      exact hj ⟨i,hi,hrow.2,hri⟩
    rw [comparisonNativeMask_on_cell hc hk hkc hm hM q α (as j) (ho j) _ _ ii hi hri,
      ite_eq_right hn,indicator_of_notMem hsel]

theorem comparisonNativeSelectedRows_mask_ae {ι : Type} {τ : Type*} [Fintype τ]
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hlim : Tendsto mesh atTop (𝓝 0))
    (a z : τ → ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H (Icc (0:ℝ) 1)) (D : Finset ℝ) :
    ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
      comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
        (comparisonNativeSelectedRows hc hk hkc hm hM q α (as j) a z H D)
        (fun _=>(0:Fin 1)) (fun _=>1) r=
        (NativeSelectedMask.fixedSupport a z H).indicator (fun _=>1) r := by
  have hD : ∀ᵐ r : ℝ,r∉D := by
    apply ae_iff.mpr
    simpa using D.measure_zero volume
  have hz : ∀ᵐ r : ℝ,∀t,r≠z t := ae_all_iff.mpr (fun t=>volume.ae_ne (z t))
  filter_upwards [ae_restrict_mem measurableSet_Ioo,ae_mono Measure.restrict_le_self hD,
    ae_mono Measure.restrict_le_self hz] with r hr hrD hrz
  exact comparisonNativeSelectedRows_mask_eventually hc hk hkc hm hM q α as mesh
    ho he hmesh hlim a z H hH D hr hrD hrz

theorem comparisonNativeSelectedRows_mask_L1 {ι : Type} {τ : Type*} [Fintype τ]
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hlim : Tendsto mesh atTop (𝓝 0))
    (a z : τ → ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H (Icc (0:ℝ) 1)) (D : Finset ℝ) :
    Tendsto (fun j=>∫r in Ioo (0:ℝ) 1,
      |comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
        (comparisonNativeSelectedRows hc hk hkc hm hM q α (as j) a z H D)
        (fun _=>(0:Fin 1)) (fun _=>1) r-
          (NativeSelectedMask.fixedSupport a z H).indicator (fun _=>1) r|) atTop (𝓝 0) := by
  apply bounded_contact_weights_tendsto_L1 (B:=1) (Ioo (0:ℝ) 1) (by simp)
  · exact fun j=>(comparisonNativeUnitColumnWeight_measurable hc hk hkc hm hM q α
      (as j) _ _ _).aestronglyMeasurable.restrict
  · intro j
    apply ae_of_all
    intro r
    have hh := radiusCellEnergyDensity_mem_Icc_bound _
      (comparisonSweepQuantile_monotone hc hk hkc hm hM α) (as j) (ho j)
      (nativeSelectedColumn (comparisonNativeSelectedRows hc hk hkc hm hM q α (as j) a z H D)
        (fun _=>(0:Fin 1)) (fun _=>(1:ℝ))) zero_le_one (fun i=>by
          unfold nativeSelectedColumn
          split_ifs <;> norm_num) r
    simpa only [comparisonNativeUnitColumnWeight,Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2
  · filter_upwards [comparisonNativeSelectedRows_mask_ae hc hk hkc hm hM q α as mesh
      ho he hmesh hlim a z H hH D] with r hr
    exact tendsto_const_nhds.congr' (hr.mono (fun _ hj=>hj.symm))

theorem comparisonNativeSelectedRows_support {ι : Type} {τ : Type*}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ) :
    NativeSelectedMask.finiteSupport
      (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i))
      (comparisonNativeSelectedRows hc hk hkc hm hM q α as a z H D)=
    NativeSelectedMask.cellSupport
      (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i)) as.length
      (NativeSelectedMask.rowSelected a z H (comparisonSweepQuantile hc hk hkc hm hM α)
        (partitionPoint 0 as) D) := by
  ext r
  constructor
  · rintro ⟨i,hi,hri⟩
    have hh := (comparisonNativeSelectedRows_mem hc hk hkc hm hM q α as a z H D i).mp hi
    exact ⟨i.val,hh.1,hh.2,hri⟩
  · rintro ⟨i,hi,hs,hri⟩
    let ii : Fin ((sampleClockSteps q 0 as).length+1) :=
      ⟨i,by simpa only [sampleClockSteps_length] using Nat.lt_succ_of_lt hi⟩
    exact ⟨ii,(comparisonNativeSelectedRows_mem hc hk hkc hm hM q α as a z H D ii).mpr
      ⟨hi,hs⟩,hri⟩

theorem comparisonNativeSelectedRows_height_bins_limit {τ : Type*} [Fintype τ]
    (n bins : ℕ) (q : ℝ → FeatureIndex n → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hlim : Tendsto mesh atTop (𝓝 0))
    (a z : τ → ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H (Icc (0:ℝ) 1)) (D : Finset ℝ)
    (K : ℕ → ℕ)
    (unit : ∀j,Fin ((sampleClockSteps q 0 (as j)).length+1) → Fin (K j))
    (hunit : ∀j,MonotoneOn (unit j)
      (comparisonNativeSelectedRows hc hk hkc hm hM q α (as j) a z H D:Set _))
    (w : ℕ → ℝ) (hw : ∀j,0<w j) :
    let p := fun j i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)
    let J := fun j=>comparisonNativeSelectedRows hc hk hkc hm hM q α (as j) a z H D
    let S := fun j (i : Fin ((sampleClockSteps q 0 (as j)).length+1))=>
      physicalPathSecondMoment n (sampleClockSteps q 0 (as j)) (q 0) i.val
    let B := fun j b=>NativeSelectedMask.finiteSupport (p j)
      (NativeUnitHeight.bin (S j) (J j) (unit j) bins (w j) b)
    let F := Ioo (0:ℝ) 1 ∩ NativeSelectedMask.fixedSupport a z H
    ∃l u : Fin bins → Icc (0:ℝ) 1,∃φ : ℕ → ℕ,StrictMono φ ∧ ∀b,
      (∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
        (r∈B (φ j) b ↔ r∈F ∩ Ioo (l b).val (u b).val)) ∧
      Tendsto (fun j=>∫r in Ioo (0:ℝ) 1,
        |(B (φ j) b).indicator (fun _=>(1:ℝ)) r-
          (F ∩ Ioo (l b).val (u b).val).indicator (fun _=>(1:ℝ)) r|) atTop (𝓝 0) := by
  dsimp only
  let p := fun j i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)
  let J := fun j=>comparisonNativeSelectedRows hc hk hkc hm hM q α (as j) a z H D
  let S := fun j (i : Fin ((sampleClockSteps q 0 (as j)).length+1))=>
    physicalPathSecondMoment n (sampleClockSteps q 0 (as j)) (q 0) i.val
  let A := fun j=>NativeSelectedMask.finiteSupport (p j) (J j)
  let B := fun j b=>NativeSelectedMask.finiteSupport (p j)
    (NativeUnitHeight.bin (S j) (J j) (unit j) bins (w j) b)
  let F := Ioo (0:ℝ) 1 ∩ NativeSelectedMask.fixedSupport a z H
  apply NativeSelectedMask.finite_bin_limits A B F
    (NativeSelectedMask.fixedSupport_band_measurable a z H hH)
    (fun j b=>NativeSelectedMask.finiteSupport_measurable _ _)
  · intro j b
    exact NativeSelectedMask.native_bin_physical_interval (p j)
      (fun i l hil=>(comparisonSweepQuantile_monotone hc hk hkc hm hM α)
        (partitionPoint_mono (as j) (ho j) hil))
      (fun i=>comparisonSweepQuantile_bounds hc hk hkc hm hM α _)
      (S j) (J j) (unit j)
      (physicalProfile_monotone_on_rows n _ (sampleClockSteps_ordered q (as j) (ho j)) (q 0))
      (hunit j) (hw j) b
  · have hD : ∀ᵐ r : ℝ,r∉D := by apply ae_iff.mpr; simpa using D.measure_zero volume
    have hz : ∀ᵐ r : ℝ,∀t,r≠z t := ae_all_iff.mpr (fun t=>volume.ae_ne (z t))
    filter_upwards [ae_restrict_mem measurableSet_Ioo,ae_mono Measure.restrict_le_self hD,
      ae_mono Measure.restrict_le_self hz] with r hr hrD hrz
    obtain ⟨h0,hN,hp,hdiam,ht⟩ := comparisonNativeSelectedRows_grid hc hk hkc hm hM α
      as mesh ho he hmesh hlim
    have hmem := NativeSelectedMask.membership_eventually a z H hH D p _ _ h0 hN hp hdiam ht
      hr hrD hrz
    filter_upwards [hmem] with j hj
    change (r ∈ NativeSelectedMask.finiteSupport (p j) (J j) ↔ r ∈ F)
    rw [show NativeSelectedMask.finiteSupport (p j) (J j)=
      NativeSelectedMask.cellSupport (p j) (as j).length
        (NativeSelectedMask.rowSelected a z H id (p j) D) from
          comparisonNativeSelectedRows_support hc hk hkc hm hM q α (as j) a z H D]
    simpa only [F,mem_inter_iff,hr,true_and] using hj

end
end OAI.SKFluctuations.LaplaceWindowFormalization
