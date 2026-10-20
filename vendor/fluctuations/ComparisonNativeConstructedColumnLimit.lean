module

public import ComparisonNativeConstructedRows
public import ComparisonConstructedCapFibre
public import ComparisonSelectedCumulativeFiniteCompactness
public import ComparisonSelectedUnitEndpointCoordinates
public import ComparisonNativeMaskMassTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 3600000
attribute [local instance] Classical.propDecidable

theorem finiteSupport_mem_iff_of_original_cell {N : ℕ}
    (p : ℕ → ℝ) (hp : Monotone p) (J : Finset (Fin N))
    (i : Fin N) {r : ℝ} (hr : r∈Ioc (p i.val) (p (i.val+1))) :
    r∈NativeSelectedMask.finiteSupport p J ↔ i∈J := by
  constructor
  · rintro ⟨j,hj,hrj⟩
    have he : j=i := by
      apply Fin.ext
      by_contra h
      rcases lt_or_gt_of_ne h with hlt | hlt
      · have hh := hp (Nat.succ_le_of_lt hlt)
        exact (not_lt_of_ge (hrj.2.trans hh)) hr.1
      · have hh := hp (Nat.succ_le_of_lt hlt)
        exact (not_lt_of_ge (hr.2.trans hh)) hrj.1
    exact he ▸ hj
  · exact fun hi=>⟨i,hi,hr⟩

theorem finite_state_constant_subsequence {F : Type*} [Fintype F]
    [TopologicalSpace F] [DiscreteTopology F] (state : ℕ → F) :
    ∃s : F,∃φ : ℕ → ℕ,StrictMono φ ∧ ∀j,state (φ j)=s := by
  obtain ⟨s,φ,hφ,ht⟩ := CompactSpace.tendsto_subseq state
  have he : ∀ᶠ j in atTop,state (φ j)=s :=
    (ht.eventually ((isOpen_discrete {s}).mem_nhds (by simp))).mono (fun _ hj=>Set.mem_singleton_iff.mp hj)
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨s,fun j=>φ (j+N),?_,fun j=>hN (j+N) (by omega)⟩
  exact hφ.comp (fun i j hij=>Nat.add_lt_add_right hij N)

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

def comparisonConstructedCapRepresentative {ι : Type} {τ : Type*}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ)
    (ag zg : ℝ) (t : τ) : Fin ((sampleClockSteps q 0 as).length+1) :=
  let T := (comparisonConstructedRows hc hk hkc hm hM q α as a z H D ag zg).filter
    (fun i=>comparisonConstructedRowRadius hc hk hkc hm hM q α as i∈Ioo (a t) (z t))
  if hT : T.Nonempty then T.min' hT else 0

def comparisonConstructedCapLabel {τ : Type*}
    (n bins : ℕ) (hbins : 0<bins) (q : ℝ → FeatureIndex n → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ) (ag zg w : ℝ) (U : Set ℝ) (t : τ) : Fin bins :=
  ⟨heightBin bins w (NativeUnitHeight.height
    (fun i=>physicalPathSecondMoment n (sampleClockSteps q 0 as) (q 0) i.val)
    (comparisonConstructedRows hc hk hkc hm hM q α as a z H D ag zg)
    (firstWholeUnitCell U (comparisonConstructedRowRadius hc hk hkc hm hM q α as))
    (firstWholeUnitCell U (comparisonConstructedRowRadius hc hk hkc hm hM q α as)
      (comparisonConstructedCapRepresentative hc hk hkc hm hM q α as a z H D ag zg t))),
    heightBin_lt hbins _ _⟩

theorem comparisonConstructedCapRepresentative_mem {ι : Type} {τ : Type*}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ)
    (ag zg : ℝ) (t : τ)
    (hn : ((comparisonConstructedRows hc hk hkc hm hM q α as a z H D ag zg).filter
      (fun i=>comparisonConstructedRowRadius hc hk hkc hm hM q α as i∈Ioo (a t) (z t))).Nonempty) :
    comparisonConstructedCapRepresentative hc hk hkc hm hM q α as a z H D ag zg t∈
      comparisonConstructedRows hc hk hkc hm hM q α as a z H D ag zg ∧
    comparisonConstructedRowRadius hc hk hkc hm hM q α as
      (comparisonConstructedCapRepresentative hc hk hkc hm hM q α as a z H D ag zg t)∈Ioo (a t) (z t) := by
  unfold comparisonConstructedCapRepresentative
  rw [dite_eq_left hn]
  exact Finset.mem_filter.mp (Finset.min'_mem _ hn)

theorem comparisonConstructedBin_cap_label_iff {τ : Type*}
    (n bins : ℕ) (hbins : 0<bins) (q : ℝ → FeatureIndex n → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ) (ag zg w : ℝ) (U : Set ℝ)
    (hcaps : ∀t,∀r∈Ioo (a t) (z t),wholeUnit U r=Ioo (a t) (z t))
    (t : τ) (b : Fin bins) (i : Fin ((sampleClockSteps q 0 as).length+1))
    (hi : i∈comparisonConstructedRows hc hk hkc hm hM q α as a z H D ag zg)
    (hit : comparisonConstructedRowRadius hc hk hkc hm hM q α as i∈Ioo (a t) (z t)) :
    i∈comparisonConstructedBin hc hk hkc hm hM n bins q α as a z H D ag zg w U b ↔
      comparisonConstructedCapLabel hc hk hkc hm hM n bins hbins q α as a z H D ag zg w U t=b := by
  let rep := comparisonConstructedCapRepresentative hc hk hkc hm hM q α as a z H D ag zg t
  have hr := comparisonConstructedCapRepresentative_mem hc hk hkc hm hM q α as a z H D ag zg t
    ⟨i,Finset.mem_filter.mpr ⟨hi,hit⟩⟩
  have hu : firstWholeUnitCell U (comparisonConstructedRowRadius hc hk hkc hm hM q α as) i=
      firstWholeUnitCell U (comparisonConstructedRowRadius hc hk hkc hm hM q α as) rep := by
    apply (firstWholeUnitCell_eq_iff U _ i rep).mpr
    exact (hcaps t _ hit).trans (hcaps t _ hr.2).symm
  simp only [comparisonConstructedBin,NativeUnitHeight.bin,Finset.mem_filter,hi,true_and,hu]
  constructor
  · exact fun h=>Fin.ext h
  · exact fun h=>congrArg Fin.val h

theorem comparisonConstructedBin_cap_support_eventually {τ : Type*}
    (n bins : ℕ) (hbins : 0<bins) (q : ℝ → FeatureIndex n → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0))
    (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ) {ag zg : ℝ}
    (hag : 0 ≤ ag) (hzg : zg ≤ 1) (ha : ∀t,ag ≤ a t) (hz : ∀t,z t ≤ zg)
    (w : ℕ → ℝ) (U : Set ℝ)
    (hcaps : ∀t,∀r∈Ioo (a t) (z t),wholeUnit U r=Ioo (a t) (z t))
    (labels : τ → Fin bins)
    (hlabels : ∀j t,comparisonConstructedCapLabel hc hk hkc hm hM n bins hbins q α (as j)
      a z H D ag zg (w j) U t=labels t)
    (t : τ) (b : Fin bins) {r : ℝ} (hr : r∈Ioo (a t) (z t)) (hrD : r∉D) :
    ∀ᶠ j in atTop,(r∈NativeSelectedMask.finiteSupport
      (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i))
      (comparisonConstructedBin hc hk hkc hm hM n bins q α (as j) a z H D ag zg (w j) U b) ↔
        labels t=b) := by
  let p := fun j i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)
  obtain ⟨_,_,_,hdiam,ht⟩ := comparisonNativeSelectedRows_grid hc hk hkc hm hM α as mesh ho he hmesh hlim
  have hcella := comparisonConstructedRows_cell_eventually hc hk hkc hm hM q α as mesh ho he
    hmesh hlim a z H D hag hzg ⟨(ha t).trans_lt hr.1,hr.2.trans_le (hz t)⟩ hrD (Or.inl ⟨t,hr⟩)
  filter_upwards [hcella,NativeSelectedMask.cells_eventually_subset_open p _ _ hdiam ht
    (Ioo (a t) (z t)) isOpen_Ioo hr] with j hj hcap
  obtain ⟨i,hi,hil,hri⟩ := hj
  have hriCap : comparisonConstructedRowRadius hc hk hkc hm hM q α (as j) i∈Ioo (a t) (z t) := by
    rw [comparisonConstructedRowRadius_eq]
    exact hcap i.val hil hri (left_mem_Icc.mpr (hri.1.le.trans hri.2))
  rw [finiteSupport_mem_iff_of_original_cell (p j)
    (fun i k hik=>(comparisonSweepQuantile_monotone hc hk hkc hm hM α)
      (partitionPoint_mono (as j) (ho j) hik)) _ i hri,
    comparisonConstructedBin_cap_label_iff hc hk hkc hm hM n bins hbins q α (as j)
      a z H D ag zg (w j) U hcaps t b i hi hriCap,hlabels j t]

theorem comparisonConstructedSupport_measurable {τ : Type*} [Fintype τ]
    (a z : τ → ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H (Icc (0:ℝ) 1))
    {ag zg : ℝ} (hag : 0 ≤ ag) (hzg : zg ≤ 1) :
    MeasurableSet (Ioo ag zg ∩ NativeSelectedMask.fixedSupport a z H) := by
  have he : Ioo ag zg ∩ NativeSelectedMask.fixedSupport a z H=
      Ioo ag zg ∩ (Ioo (0:ℝ) 1 ∩ NativeSelectedMask.fixedSupport a z H) := by
    ext r
    constructor
    · exact fun hr=>⟨hr.1,⟨hag.trans_lt hr.1.1,hr.1.2.trans_le hzg⟩,hr.2⟩
    · exact fun hr=>⟨hr.1,hr.2.2⟩
  rw [he]
  exact measurableSet_Ioo.inter (NativeSelectedMask.fixedSupport_band_measurable a z H hH)

theorem comparisonConstructedRows_support_ae {ι : Type} {τ : Type*} [Fintype τ]
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hlim : Tendsto mesh atTop (𝓝 0))
    (a z : τ → ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H (Icc (0:ℝ) 1)) (D : Finset ℝ)
    {ag zg : ℝ} (hag : 0 ≤ ag) (hzg : zg ≤ 1) :
    ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
      (r∈NativeSelectedMask.finiteSupport
        (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i))
        (comparisonConstructedRows hc hk hkc hm hM q α (as j) a z H D ag zg) ↔
          r∈Ioo ag zg ∩ NativeSelectedMask.fixedSupport a z H) := by
  have hD : ∀ᵐ r : ℝ,r∉D := by apply ae_iff.mpr; simpa using D.measure_zero volume
  have hz : ∀ᵐ r : ℝ,∀t,r≠z t := ae_all_iff.mpr (fun t=>volume.ae_ne (z t))
  filter_upwards [ae_restrict_of_ae hD,ae_restrict_of_ae hz,
    ae_restrict_of_ae (volume.ae_ne ag),ae_restrict_of_ae (volume.ae_ne zg)] with r hrD hrz hra hrb
  exact comparisonConstructedRows_support_eventually hc hk hkc hm hM q α as mesh ho he
    hmesh hlim a z H hH D hag hzg hrD hrz hra hrb

theorem comparisonConstructedBins_geometry {τ : Type*} [Fintype τ]
    (n bins : ℕ) (q : ℝ → FeatureIndex n → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hlim : Tendsto mesh atTop (𝓝 0))
    (a z : τ → ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H (Icc (0:ℝ) 1)) (D : Finset ℝ)
    {ag zg : ℝ} (hag : 0 ≤ ag) (hzg : zg ≤ 1)
    (w : ℕ → ℝ) (hw : ∀j,0<w j) (U : Set ℝ) :
    let J := fun j b=>comparisonConstructedBin hc hk hkc hm hM n bins q α (as j) a z H D ag zg (w j) U b
    let p := fun j i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)
    let F := Ioo ag zg ∩ NativeSelectedMask.fixedSupport a z H
    ∃l u : Fin bins → Icc (0:ℝ) 1,∃φ : ℕ → ℕ,StrictMono φ ∧ ∀b,
      ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
        (r∈NativeSelectedMask.finiteSupport (p (φ j)) (J (φ j) b) ↔
          r∈F ∩ Ioo (l b).val (u b).val) := by
  dsimp only
  let A := fun j=>comparisonConstructedRows hc hk hkc hm hM q α (as j) a z H D ag zg
  let J := fun j b=>comparisonConstructedBin hc hk hkc hm hM n bins q α (as j) a z H D ag zg (w j) U b
  let p := fun j i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)
  let F := Ioo ag zg ∩ NativeSelectedMask.fixedSupport a z H
  have hinterval j b : ∃l u : Icc (0:ℝ) 1,
      NativeSelectedMask.finiteSupport (p j) (J j b)=
        NativeSelectedMask.finiteSupport (p j) (A j) ∩ Ioc l.val u.val := by
    apply NativeSelectedMask.native_bin_physical_interval (p j)
      (fun i l hil=>(comparisonSweepQuantile_monotone hc hk hkc hm hM α)
        (partitionPoint_mono (as j) (ho j) hil))
      (fun i=>comparisonSweepQuantile_bounds hc hk hkc hm hM α _)
      _ (A j) _
      (physicalProfile_monotone_on_rows n _ (sampleClockSteps_ordered q (as j) (ho j)) (q 0))
      ((firstWholeUnitCell_monotone U (comparisonConstructedRowRadius hc hk hkc hm hM q α (as j))
        (comparisonConstructedRowRadius_monotone hc hk hkc hm hM q α (as j) (ho j))).monotoneOn _)
      (hw j) b
  obtain ⟨l,u,φ,hφ,hmem⟩ := NativeSelectedMask.finite_bin_limits
    (fun j=>NativeSelectedMask.finiteSupport (p j) (A j))
    (fun j b=>NativeSelectedMask.finiteSupport (p j) (J j b)) F
    (comparisonConstructedSupport_measurable a z H hH hag hzg)
    (fun j b=>NativeSelectedMask.finiteSupport_measurable _ _) hinterval
    (comparisonConstructedRows_support_ae hc hk hkc hm hM q α as mesh ho he hmesh hlim a z H hH D hag hzg)
  exact ⟨l,u,φ,hφ,fun b=>(hmem b).1⟩

theorem comparisonConstructedBins_common_subsequence {τ : Type*} [Fintype τ]
    (n bins : ℕ) (q : ℝ → FeatureIndex n → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hlim : Tendsto mesh atTop (𝓝 0))
    (a z : τ → ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H (Icc (0:ℝ) 1)) (D : Finset ℝ)
    {ag zg : ℝ} (hag : 0 ≤ ag) (hzg : zg ≤ 1)
    (w : ℕ → ℝ) (hw : ∀j,0<w j) (U : Set ℝ) :
    let J := fun j b=>comparisonConstructedBin hc hk hkc hm hM n bins q α (as j) a z H D ag zg (w j) U b
    let p := fun j i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)
    let F := Ioo ag zg ∩ NativeSelectedMask.fixedSupport a z H
    ∃l u : Fin bins → Icc (0:ℝ) 1,∃f : Fin bins → (Icc (0:ℝ) 1 →ᵇ ℝ),∃φ : ℕ → ℕ,
      StrictMono φ ∧ ∀b,
      Tendsto (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM q α
        (as (φ j)) (ho (φ j)) (J (φ j) b)) atTop (𝓝 (f b)) ∧
      (∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
        (r∈NativeSelectedMask.finiteSupport (p (φ j)) (J (φ j) b) ↔
          r∈F ∩ Ioo (l b).val (u b).val)) := by
  dsimp only
  let J := fun j b=>comparisonConstructedBin hc hk hkc hm hM n bins q α (as j) a z H D ag zg (w j) U b
  obtain ⟨l,u,φ,hφ,hgeom⟩ := comparisonConstructedBins_geometry hc hk hkc hm hM n bins q α
    as mesh ho he hmesh hlim a z H hH D hag hzg w hw U
  obtain ⟨f,ψ,hψ,hcdf⟩ := comparisonSelectedCumulative_finite_exists_uniform_subseq
    hc hk hkc hm hM q α (fun j=>as (φ j)) (fun j=>ho (φ j)) (fun j b=>J (φ j) b)
  refine ⟨l,u,f,φ∘ψ,hφ.comp hψ,?_⟩
  intro b
  refine ⟨hcdf b,?_⟩
  filter_upwards [hgeom b] with r hr
  exact hψ.tendsto_atTop.eventually hr

theorem comparisonConstructedCoordinates_width_tendsto {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1)
    (J : ∀j,Finset (Fin ((sampleClockSteps q 0 (as j)).length+1)))
    (U : Set ℝ)
    (C : ∀j,NativeConstructedCoordinates (sampleClockSteps q 0 (as j)) (J j)
      (comparisonConstructedRowRadius hc hk hkc hm hM q α (as j)) U)
    (f : Icc (0:ℝ) 1 →ᵇ ℝ)
    (hf : Tendsto (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM q α (as j) (ho j) (J j))
      atTop (𝓝 f)) :
    Tendsto (fun j=>(C j).x (C j).K) atTop (𝓝 (f ⟨1,by simp⟩)) := by
  have hh := selectedCumulative_uniform_moving_eval_tendsto _ f hf
    (fun _=>(⟨1,by simp⟩ : Icc (0:ℝ) 1)) ⟨1,by simp⟩ tendsto_const_nhds
  have heq j := comparison_selected_cumulative_at_one_eq_width hc hk hkc hm hM q α (as j)
    (ho j) (he j) (J j) (C j).unit (C j).x (C j).start (C j).mass
  simpa only [heq] using hh

theorem comparisonConstructedBin_mass_mask_limit {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1)
    (J : ∀j,Finset (Fin ((sampleClockSteps q 0 (as j)).length+1)))
    (hJ : ∀j,∀i∈J j,i.val<(as j).length) (U : Set ℝ)
    (C : ∀j,NativeConstructedCoordinates (sampleClockSteps q 0 (as j)) (J j)
      (comparisonConstructedRowRadius hc hk hkc hm hM q α (as j)) U)
    (F : Set ℝ)
    (hmem : ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
      (r∈NativeSelectedMask.finiteSupport
        (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)) (J j) ↔ r∈F)) :
    Tendsto (fun j=>∫u in Icc (0:ℝ) 1,
      |massStepFunction (as j) (nativeSelectedColumn (J j) (C j).unit (fun _=>1)) u-
        F.indicator (fun _=>1) (comparisonSweepQuantile hc hk hkc hm hM α u)|) atTop (𝓝 0) := by
  have hpoint := (comparisonNativeMask_tendsto_of_support_eventually hc hk hkc hm hM q α
    as ho he (fun j=>(C j).K) J (fun j=>(C j).unit) hJ F hmem).1
  apply comparisonNativeMask_mass_L1_tendsto_of_radius_ae hc hk hkc hm hM q α as ho he
    (fun j=>(C j).K) J (fun j=>(C j).unit) (F.indicator (fun _=>1))
  simpa only [Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ:=volume) (a:=(0:ℝ)) (b:=1))] using hpoint

theorem comparisonConstructedBins_exists_common_family {τ : Type*} [Fintype τ]
    (n bins : ℕ) (hbins : 0<bins) (q : ℝ → FeatureIndex n → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0))
    (a z : τ → ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H (Icc (0:ℝ) 1)) (D : Finset ℝ)
    {ag zg : ℝ} (hag : 0 ≤ ag) (hzg : zg ≤ 1)
    (w : ℕ → ℝ) (hw : ∀j,0<w j) (U : Set ℝ) (δ : ℝ) :
    let J := fun j b=>comparisonConstructedBin hc hk hkc hm hM n bins q α (as j) a z H D ag zg (w j) U b
    let p := fun j i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)
    let F := Ioo ag zg ∩ NativeSelectedMask.fixedSupport a z H
    ∃C : ∀j b,NativeConstructedCoordinates (sampleClockSteps q 0 (as j)) (J j b)
      (comparisonConstructedRowRadius hc hk hkc hm hM q α (as j)) U,
    ∃l u : Fin bins → Icc (0:ℝ) 1,∃f : Fin bins → (Icc (0:ℝ) 1 →ᵇ ℝ),
    ∃labels : τ → Fin bins,∃keep : Fin bins → Bool,∃φ : ℕ → ℕ,
      StrictMono φ ∧
      (∀j t,comparisonConstructedCapLabel hc hk hkc hm hM n bins hbins q α (as (φ j))
        a z H D ag zg (w (φ j)) U t=labels t) ∧
      (∀j b,(2*δ ≤ (C (φ j) b).x (C (φ j) b).K ↔ keep b=true)) ∧
      ∀b,
        Tendsto (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM q α
          (as (φ j)) (ho (φ j)) (J (φ j) b)) atTop (𝓝 (f b)) ∧
        (∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
          (r∈NativeSelectedMask.finiteSupport (p (φ j)) (J (φ j) b) ↔ r∈F ∩ Ioo (l b).val (u b).val)) ∧
        Tendsto (fun j=>(C (φ j) b).x (C (φ j) b).K) atTop (𝓝 (f b ⟨1,by simp⟩)) ∧
        Tendsto (fun j=>∫v in Icc (0:ℝ) 1,
          |massStepFunction (as (φ j)) (nativeSelectedColumn (J (φ j) b) (C (φ j) b).unit (fun _=>1)) v-
            (F ∩ Ioo (l b).val (u b).val).indicator (fun _=>1)
              (comparisonSweepQuantile hc hk hkc hm hM α v)|) atTop (𝓝 0) := by
  dsimp only
  let J := fun j b=>comparisonConstructedBin hc hk hkc hm hM n bins q α (as j) a z H D ag zg (w j) U b
  let C := fun j b=>Classical.choice
    (comparisonConstructedBin_exists_coordinates hc hk hkc hm hM n bins q α (as j) (ho j)
      a z H D ag zg (w j) U b)
  obtain ⟨l,u,f,ψ,hψ,hsub⟩ := comparisonConstructedBins_common_subsequence hc hk hkc hm hM
    n bins q α as mesh ho he hmesh hlim a z H hH D hag hzg w hw U
  let state : ℕ → (τ → Fin bins) × (Fin bins → Bool) := fun j=>
    (fun t=>comparisonConstructedCapLabel hc hk hkc hm hM n bins hbins q α (as (ψ j))
      a z H D ag zg (w (ψ j)) U t,
     fun b=>decide (2*δ ≤ (C (ψ j) b).x (C (ψ j) b).K))
  obtain ⟨s,χ,hχ,hs⟩ := finite_state_constant_subsequence state
  let φ := ψ∘χ
  refine ⟨C,l,u,f,s.1,s.2,φ,hψ.comp hχ,?_,?_,?_⟩
  · intro j t
    exact congrArg (fun v=>v.1 t) (hs j)
  · intro j b
    have hh : decide (2*δ ≤ (C (φ j) b).x (C (φ j) b).K)=s.2 b :=
      congrArg (fun v=>v.2 b) (hs j)
    exact eq_iff_iff.mp ((decide_eq_true_eq).symm.trans (congrArg (fun v=>v=true) hh))
  · intro b
    have hcdf := (hsub b).1.comp hχ.tendsto_atTop
    have hgeom : ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
        (r∈NativeSelectedMask.finiteSupport
          (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as (φ j)) i))
          (J (φ j) b) ↔ r∈(Ioo ag zg ∩ NativeSelectedMask.fixedSupport a z H) ∩ Ioo (l b).val (u b).val) := by
      filter_upwards [(hsub b).2] with r hr
      exact hχ.tendsto_atTop.eventually hr
    refine ⟨hcdf,hgeom,?_,?_⟩
    · exact comparisonConstructedCoordinates_width_tendsto hc hk hkc hm hM q α
        (fun j=>as (φ j)) (fun j=>ho (φ j)) (fun j=>he (φ j))
        (fun j=>J (φ j) b) U (fun j=>C (φ j) b) (f b) hcdf
    · apply comparisonConstructedBin_mass_mask_limit hc hk hkc hm hM q α
        (fun j=>as (φ j)) (fun j=>ho (φ j)) (fun j=>he (φ j))
        (fun j=>J (φ j) b) _ U (fun j=>C (φ j) b) _ hgeom
      intro j i hi
      have hrow := comparisonConstructedBin_subset hc hk hkc hm hM n bins q α (as (φ j))
        a z H D ag zg (w (φ j)) U b hi
      have hglobal := comparisonConstructedRows_subset hc hk hkc hm hM q α (as (φ j))
        a z H D ag zg hrow
      exact ((comparisonNativeSelectedRows_mem hc hk hkc hm hM q α (as (φ j)) a z H D i).mp hglobal).1

theorem constructed_stable_small_bin_ledger {bins : ℕ}
    (width : ℕ → Fin bins → ℝ) (keep : Fin bins → Bool) {δ : ℝ} (hδ : 0 ≤ δ)
    (hkeep : ∀j b,2*δ ≤ width j b ↔ keep b=true) :
    ∀j,(∑b : Fin bins,if keep b then 0 else width j b) ≤ 2*(bins:ℝ)*δ := by
  intro j
  have he b : (if keep b then 0 else width j b)=
      (if width j b<2*δ then width j b else 0) := by
    by_cases hk : keep b=true
    · have hh := (hkeep j b).mpr hk
      simp only [hk,ite_true,not_lt.mpr hh,ite_false]
    · have hh : width j b<2*δ := lt_of_not_ge (fun h=>hk ((hkeep j b).mp h))
      simp [hk,hh]
  simp_rw [he]
  exact constructed_small_bins_mass_le (width j) hδ

theorem comparisonConstructedBin_cap_coordinates_tendsto {τ : Type*}
    (n bins : ℕ) (hbins : 0<bins) (q : ℝ → FeatureIndex n → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M)
    (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ) (ag zg : ℝ) (U : Set ℝ)
    (hD : ∀d∈D,d∈Icc (0:ℝ) 1)
    (ms : ℕ → ℕ) (hms : Tendsto ms atTop atTop) (w : ℕ → ℝ)
    (t : τ) (b : Fin bins) (ha : a t∈D) (hz : z t∈D) (haz : a t<z t)
    (hinterior : ∀d∈D,d∉Ioo (a t) (z t)) (hag : ag ≤ a t) (hzg : z t ≤ zg)
    (hcap : ∀r∈Ioo (a t) (z t),wholeUnit U r=Ioo (a t) (z t))
    (C : ∀j,NativeConstructedCoordinates
      (sampleClockSteps q 0 (finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j)))
      (comparisonConstructedBin hc hk hkc hm hM n bins q α
        (finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j)) a z H D ag zg (w j) U b)
      (comparisonConstructedRowRadius hc hk hkc hm hM q α
        (finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j))) U)
    (hrep : ∀j,let as := finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j)
      let rep := comparisonConstructedCapRepresentative hc hk hkc hm hM q α as a z H D ag zg t
      rep∈comparisonConstructedRows hc hk hkc hm hM q α as a z H D ag zg ∧
        comparisonConstructedRowRadius hc hk hkc hm hM q α as rep∈Ioo (a t) (z t))
    (hlabel : ∀j,comparisonConstructedCapLabel hc hk hkc hm hM n bins hbins q α
      (finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j)) a z H D ag zg (w j) U t=b)
    (f : Icc (0:ℝ) 1 →ᵇ ℝ)
    (hf : Tendsto (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM q α
      (finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j))
      (finiteCutMasses_ordered _ (finiteBoundaryMassNodes_bound _ (fun d hd=>by
        obtain ⟨r,_,rfl⟩:=Finset.mem_image.mp hd;exact (α.val.property.1 r).2)) (ms j))
      (comparisonConstructedBin hc hk hkc hm hM n bins q α
        (finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j)) a z H D ag zg (w j) U b))
      atTop (𝓝 f)) :
    let as := fun j=>finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j)
    let rep := fun j=>comparisonConstructedCapRepresentative hc hk hkc hm hM q α (as j) a z H D ag zg t
    Tendsto (fun j=>(C j).x ((C j).unit (rep j)).val) atTop (𝓝 (f ⟨a t,hD _ ha⟩)) ∧
    Tendsto (fun j=>(C j).x (((C j).unit (rep j)).val+1)) atTop (𝓝 (f ⟨z t,hD _ hz⟩)) ∧
    f ⟨z t,hD _ hz⟩-f ⟨a t,hD _ ha⟩=α.val.val (z t)-α.val.val (a t) ∧
    f ⟨a t,hD _ ha⟩<f ⟨z t,hD _ hz⟩ := by
  dsimp only
  let Dm := D.image α.val.val
  let as := fun j=>finiteCutMasses (finiteBoundaryMassNodes Dm) (ms j)
  let J := fun j=>comparisonConstructedBin hc hk hkc hm hM n bins q α (as j) a z H D ag zg (w j) U b
  let rad := fun j=>comparisonConstructedRowRadius hc hk hkc hm hM q α (as j)
  let rep := fun j=>comparisonConstructedCapRepresentative hc hk hkc hm hM q α (as j) a z H D ag zg t
  have hDm : ∀d∈Dm,d∈Icc (0:ℝ) 1 := by
    intro d hd
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hd
    exact α.val.property.1 r
  have hrepJ j : rep j∈J j := by
    apply Finset.mem_filter.mpr
    refine ⟨(hrep j).1,?_⟩
    exact congrArg Fin.val (hlabel j)
  have hfilter j : (J j).filter (fun i=>(C j).unit i=(C j).unit (rep j))=
      (completeMassCapCells (sampleClockSteps q 0 (as j)) (α.val.val (a t)) (α.val.val (z t))).erase
        (finiteBoundaryClockCell q (as j) (α.val.val (a t))) := by
    have he : (J j).filter (fun i=>(C j).unit i=(C j).unit (rep j))=
        (J j).filter (fun i=>firstWholeUnitCell U (rad j) i=firstWholeUnitCell U (rad j) (rep j)) := by
      ext i
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hi,hu⟩
        exact ⟨hi,(firstWholeUnitCell_eq_iff U _ i (rep j)).mpr
          (((C j).classes i hi (rep j) (hrepJ j)).mp hu)⟩
      · rintro ⟨hi,hu⟩
        exact ⟨hi,((C j).classes i hi (rep j) (hrepJ j)).mpr
          ((firstWholeUnitCell_eq_iff U _ i (rep j)).mp hu)⟩
    rw [he]
    exact comparisonConstructedBin_cap_fibre hc hk hkc hm hM n bins q α a z H D ag zg (w j) U
      (ms j) t b hD ha hz haz hinterior hag hzg hcap (rep j) (hrep j).2 (congrArg Fin.val (hlabel j))
  let T := fun j=>(J j).filter (fun i=>(C j).unit i=(C j).unit (rep j))
  have hT j : (T j).Nonempty := ⟨rep j,Finset.mem_filter.mpr ⟨hrepJ j,rfl⟩⟩
  let p := fun j=>(T j).min' (hT j)
  let qq := fun j=>(T j).max' (hT j)
  have hp j := Finset.mem_filter.mp (Finset.min'_mem (T j) (hT j))
  have hq j := Finset.mem_filter.mp (Finset.max'_mem (T j) (hT j))
  exact comparison_retained_cap_unit_endpoint_coordinates_tendsto hc hk hkc hm hM q α Dm hDm
    ms hms (hD _ ha) (hD _ hz) haz (Finset.mem_image.mpr ⟨a t,ha,rfl⟩)
    (Finset.mem_image.mpr ⟨z t,hz,rfl⟩) (fun j=>(C j).K) J (fun j=>(C j).unit)
    (fun j=>(C j).unit (rep j)) (fun j=>(C j).x) (fun j=>(C j).start)
    (fun j=>(C j).mass) (fun j=>(C j).order) hfilter p qq (fun j=>(hp j).1) (fun j=>(hq j).1)
    (fun j=>(hp j).2) (fun j=>(hq j).2)
    (fun j i hi hu=>Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hi,hu⟩))
    (fun j i hi hu=>Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hi,hu⟩)) f hf

theorem comparisonConstructedCapRepresentative_eventually {ι : Type} {τ : Type*}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0))
    (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ) {ag zg : ℝ}
    (hag : 0 ≤ ag) (hzg : zg ≤ 1) (t : τ) (hat : ag ≤ a t) (hzt : z t ≤ zg)
    (haz : a t<z t) (hinterior : ∀d∈D,d∉Ioo (a t) (z t)) :
    ∀ᶠ j in atTop,
      let rep := comparisonConstructedCapRepresentative hc hk hkc hm hM q α (as j) a z H D ag zg t
      rep∈comparisonConstructedRows hc hk hkc hm hM q α (as j) a z H D ag zg ∧
        comparisonConstructedRowRadius hc hk hkc hm hM q α (as j) rep∈Ioo (a t) (z t) := by
  let r := (a t+z t)/2
  have hr : r∈Ioo (a t) (z t) := by constructor <;> dsimp [r] <;> linarith
  have hrD : r∉D := fun hd=>hinterior r hd hr
  let p := fun j i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)
  obtain ⟨_,_,_,hdiam,ht⟩ := comparisonNativeSelectedRows_grid hc hk hkc hm hM α as mesh ho he hmesh hlim
  filter_upwards [comparisonConstructedRows_cell_eventually hc hk hkc hm hM q α as mesh ho he
    hmesh hlim a z H D hag hzg ⟨hat.trans_lt hr.1,hr.2.trans_le hzt⟩ hrD (Or.inl ⟨t,hr⟩),
    NativeSelectedMask.cells_eventually_subset_open p _ _ hdiam ht (Ioo (a t) (z t)) isOpen_Ioo hr]
    with j hj hjcap
  obtain ⟨i,hi,hil,hri⟩ := hj
  apply comparisonConstructedCapRepresentative_mem hc hk hkc hm hM q α (as j) a z H D ag zg t
  refine ⟨i,Finset.mem_filter.mpr ⟨hi,?_⟩⟩
  rw [comparisonConstructedRowRadius_eq]
  exact hjcap i.val hil hri (left_mem_Icc.mpr (hri.1.le.trans hri.2))

theorem comparisonConstructedContact_measurable (H : ℝ → ℝ)
    (hH : ContinuousOn H (Icc (0:ℝ) 1)) {ag zg l u : ℝ}
    (hag : 0 ≤ ag) (hzg : zg ≤ 1) :
    MeasurableSet ((Ioo ag zg ∩ {r | H r=0}) ∩ Ioo l u) := by
  have hh := comparisonConstructedSupport_measurable (fun t : Empty=>nomatch t)
    (fun t : Empty=>nomatch t) H hH hag hzg
  have hzero : MeasurableSet (Ioo ag zg ∩ {r | H r=0}) := by
    simpa [NativeSelectedMask.fixedSupport] using hh
  exact hzero.inter measurableSet_Ioo

theorem comparisonConstructedBin_column_geometry {τ : Type*} [Fintype τ]
    (n bins : ℕ) (hbins : 0<bins) (q : ℝ → FeatureIndex n → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0))
    (a z : τ → ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H (Icc (0:ℝ) 1))
    (D : Finset ℝ) {ag zg : ℝ} (hag : 0 ≤ ag) (hzg : zg ≤ 1)
    (ha : ∀t,ag ≤ a t) (hz : ∀t,z t ≤ zg) (w : ℕ → ℝ) (U : Set ℝ)
    (hneg : ∀t,∀r∈Ioo (a t) (z t),H r<0)
    (hcaps : ∀t,∀r∈Ioo (a t) (z t),wholeUnit U r=Ioo (a t) (z t))
    (labels : τ → Fin bins)
    (hlabels : ∀j t,comparisonConstructedCapLabel hc hk hkc hm hM n bins hbins q α (as j)
      a z H D ag zg (w j) U t=labels t)
    (hrep : ∀j t,let rep := comparisonConstructedCapRepresentative hc hk hkc hm hM q α (as j) a z H D ag zg t
      rep∈comparisonConstructedRows hc hk hkc hm hM q α (as j) a z H D ag zg ∧
        comparisonConstructedRowRadius hc hk hkc hm hM q α (as j) rep∈Ioo (a t) (z t))
    (b : Fin bins) (l u : ℝ)
    (C : ∀j,NativeConstructedCoordinates (sampleClockSteps q 0 (as j))
      (comparisonConstructedBin hc hk hkc hm hM n bins q α (as j) a z H D ag zg (w j) U b)
      (comparisonConstructedRowRadius hc hk hkc hm hM q α (as j)) U)
    (hgeom : ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
      (r∈NativeSelectedMask.finiteSupport
        (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i))
        (comparisonConstructedBin hc hk hkc hm hM n bins q α (as j) a z H D ag zg (w j) U b) ↔
       r∈(Ioo ag zg ∩ NativeSelectedMask.fixedSupport a z H) ∩ Ioo l u)) :
    let J := fun j=>comparisonConstructedBin hc hk hkc hm hM n bins q α (as j) a z H D ag zg (w j) U b
    let A := (Ioo ag zg ∩ {r | H r=0}) ∩ Ioo l u
    let rep := fun j t=>comparisonConstructedCapRepresentative hc hk hkc hm hM q α (as j) a z H D ag zg t
    (∀ᵐ r ∂volume.restrict A,∀ᶠ j in atTop,
      comparisonNativeContactCellWitness hc hk hkc hm hM q α (as j) (J j) (C j).unit H U r) ∧
    (∀ᵐ r ∂volume.restrict (Ioo ag zg),∀t : {t : τ // labels t=b},r∈Ioo (a t.val) (z t.val) →
      ∀ᶠ j in atTop,∃i : Fin ((sampleClockSteps q 0 (as j)).length+1),
        i∈J j ∧ i.val<(as j).length ∧ (C j).unit i=(C j).unit (rep j t.val) ∧
        r∈Ioc (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i.val))
          (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) (i.val+1)))) ∧
    (∀ᵐ r ∂volume.restrict (Ioo ag zg),(∀t : {t : τ // labels t=b},r∉Ioo (a t.val) (z t.val)) → r∉A →
      Tendsto (fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
        (J j) (C j).unit (fun _=>1) r) atTop (𝓝 0)) := by
  dsimp only
  let J := fun j=>comparisonConstructedBin hc hk hkc hm hM n bins q α (as j) a z H D ag zg (w j) U b
  let A := (Ioo ag zg ∩ {r | H r=0}) ∩ Ioo l u
  let F := (Ioo ag zg ∩ NativeSelectedMask.fixedSupport a z H) ∩ Ioo l u
  let p := fun j i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)
  let rep := fun j t=>comparisonConstructedCapRepresentative hc hk hkc hm hM q α (as j) a z H D ag zg t
  have hA : MeasurableSet A := comparisonConstructedContact_measurable H hH hag hzg
  have hband : Ioo ag zg ⊆ Ioo (0:ℝ) 1 := fun r hr=>⟨hag.trans_lt hr.1,hr.2.trans_le hzg⟩
  have hJ' j : J j⊆comparisonNativeSelectedRows hc hk hkc hm hM q α (as j) a z H D := by
    intro i hi
    exact comparisonConstructedRows_subset hc hk hkc hm hM q α (as j) a z H D ag zg
      (comparisonConstructedBin_subset hc hk hkc hm hM n bins q α (as j) a z H D ag zg (w j) U b hi)
  have hindex j i (hi : i∈J j) : i.val<(as j).length :=
    ((comparisonNativeSelectedRows_mem hc hk hkc hm hM q α (as j) a z H D i).mp (hJ' j hi)).1
  have hD : ∀ᵐ r : ℝ,r∉D := by apply ae_iff.mpr;simpa using D.measure_zero volume
  refine ⟨?_,?_,?_⟩
  · apply comparisonNativeSelectedRows_contact_witness_ae hc hk hkc hm hM q α as mesh ho he hmesh hlim
      a z H D U hneg hcaps (fun j=>(C j).K) J (fun j=>(C j).unit) hJ'
      (fun m i hi j hj hij=>((C m).classes i hi j hj).mp hij) A hA (fun r hr=>hr.1.2)
    filter_upwards [ae_mono (Measure.restrict_mono (fun r hr=>hband hr.1.1) le_rfl) hgeom,
      ae_restrict_mem hA] with r hr hrA
    exact hr.mono (fun j hj=>hj.mpr ⟨⟨hrA.1.1,Or.inr hrA.1.2⟩,hrA.2⟩)
  · filter_upwards [ae_restrict_of_ae hD] with r hrD
    intro t hrt
    obtain ⟨_,_,_,hdiam,ht⟩ := comparisonNativeSelectedRows_grid hc hk hkc hm hM α as mesh ho he hmesh hlim
    filter_upwards [comparisonConstructedRows_cell_eventually hc hk hkc hm hM q α as mesh ho he
      hmesh hlim a z H D hag hzg ⟨(ha t.val).trans_lt hrt.1,hrt.2.trans_le (hz t.val)⟩ hrD
      (Or.inl ⟨t.val,hrt⟩),
      NativeSelectedMask.cells_eventually_subset_open p _ _ hdiam ht (Ioo (a t.val) (z t.val)) isOpen_Ioo hrt]
      with j hj hjcap
    obtain ⟨i,hi,hil,hri⟩ := hj
    have hriCap : comparisonConstructedRowRadius hc hk hkc hm hM q α (as j) i∈Ioo (a t.val) (z t.val) := by
      rw [comparisonConstructedRowRadius_eq]
      exact hjcap i.val hil hri (left_mem_Icc.mpr (hri.1.le.trans hri.2))
    have hiJ : i∈J j := (comparisonConstructedBin_cap_label_iff hc hk hkc hm hM n bins hbins q α
      (as j) a z H D ag zg (w j) U hcaps t.val b i hi hriCap).mpr ((hlabels j t.val).trans t.property)
    have hrJ : rep j t.val∈J j := (comparisonConstructedBin_cap_label_iff hc hk hkc hm hM n bins hbins q α
      (as j) a z H D ag zg (w j) U hcaps t.val b (rep j t.val) (hrep j t.val).1 (hrep j t.val).2).mpr
        ((hlabels j t.val).trans t.property)
    exact ⟨i,hiJ,hil,((C j).classes i hiJ (rep j t.val) hrJ).mpr
      ((hcaps t.val _ hriCap).trans (hcaps t.val _ (hrep j t.val).2).symm),hri⟩
  · have hpoint := (comparisonNativeMask_tendsto_of_support_eventually hc hk hkc hm hM q α as ho he
      (fun j=>(C j).K) J (fun j=>(C j).unit) hindex F hgeom).1
    filter_upwards [ae_mono (Measure.restrict_mono hband le_rfl) hpoint,
      ae_mono (Measure.restrict_mono hband le_rfl) hgeom,ae_restrict_of_ae hD] with r hrpoint hrgeom hrD
    intro hncap hnA
    have hnF : r∉F := by
      intro hrF
      rcases hrF.1.2 with ⟨t,hrt⟩ | hrzero
      · have hc := comparisonConstructedBin_cap_support_eventually hc hk hkc hm hM n bins hbins q α
          as mesh ho he hmesh hlim a z H D hag hzg ha hz w U hcaps labels hlabels t b hrt hrD
        have hevent : ∀ᶠ j : ℕ in atTop,labels t=b := by
          filter_upwards [hrgeom,hc] with j hj hcap
          exact hcap.mp (hj.mpr hrF)
        exact hncap ⟨t,hevent.exists.choose_spec⟩ hrt
      · exact hnA ⟨⟨hrF.1.1,hrzero⟩,hrF.2⟩
    simpa only [Set.indicator_of_notMem hnF] using hrpoint

end
end OAI.SKFluctuations.LaplaceWindowFormalization
