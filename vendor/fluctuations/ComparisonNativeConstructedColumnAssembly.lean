module

public import ComparisonNativeConstructedColumnLimit
public import ComparisonNativeKeptUnionMass

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 12000000
attribute [local instance] Classical.propDecidable

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

def NativeConstructedBinLimit {τ : Type*} [Fintype τ]
    (n bins : ℕ) (q : ℝ → FeatureIndex n → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : ℕ → List PositiveMass)
    (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ) (ag zg δ : ℝ)
    (w : ℕ → ℝ) (U : Set ℝ) (b : Fin bins)
    (C : ∀j,NativeConstructedCoordinates (sampleClockSteps q 0 (as j))
      (comparisonConstructedBin hc hk hkc hm hM n bins q α (as j) a z H D ag zg (w j) U b)
      (comparisonConstructedRowRadius hc hk hkc hm hM q α (as j)) U)
    (labels : τ → Fin bins) (l u : ℝ) (f : Icc (0:ℝ) 1 →ᵇ ℝ) : Prop :=
  let B := {t : τ // labels t=b}
  let A := (Ioo ag zg ∩ {r | H r=0}) ∩ Ioo l u
  let width := f ⟨1,by simp⟩
  let wcontact := fun r=>pointSideColumn δ width (comparisonContactLimitCoordinate f r)
  let moving := fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
    (comparisonConstructedBin hc hk hkc hm hM n bins q α (as j) a z H D ag zg (w j) U b)
    (C j).unit (fun v=>sideSquareColumn (C j).x δ ((C j).x (C j).K) v.val)
  ∃cl cr : B → ℝ,
    (∀t,cl t=comparisonContactLimitCoordinate f (a t.val) ∧
      cr t=comparisonContactLimitCoordinate f (z t.val) ∧
      cr t-cl t=α.val.val (z t.val)-α.val.val (a t.val) ∧ cl t<cr t) ∧
    let fixed := fixedCapContactWeight (fun t : B=>a t.val) (fun t=>z t.val)
      (fun t=>sideSquareColumnLR δ width (cl t) (cr t)) A wcontact
    Tendsto (fun j=>(C j).x (C j).K) atTop (𝓝 width) ∧ 2*δ ≤ width ∧
    (∀ᵐ r ∂volume.restrict (Ioo ag zg),Tendsto (fun j=>moving j r) atTop (𝓝 (fixed r))) ∧
    Tendsto (fun j=>∫r in Ioo ag zg,|moving j r-fixed r|) atTop (𝓝 0) ∧
    Tendsto (fun j=>∫r in Ioo ag zg,
      |deriv α.val.val r*moving j r-deriv α.val.val r*fixed r|) atTop (𝓝 0) ∧
    (∫r in A,deriv α.val.val r*wcontact r) ≤ 2*Real.log (width/δ)

theorem comparisonConstructedBin_full_L1 {τ : Type*} [Fintype τ]
    (n bins : ℕ) (hbins : 0<bins) (q : ℝ → FeatureIndex n → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M)
    (a z : τ → ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H (Icc (0:ℝ) 1))
    (D : Finset ℝ) {ag zg δ : ℝ} (hag : 0<ag) (hzg : zg ≤ 1) (hδ : 0<δ)
    (hD : ∀d∈D,d∈Icc (0:ℝ) 1) (haD : ∀t,a t∈D) (hzD : ∀t,z t∈D)
    (haz : ∀t,a t<z t) (hinterior : ∀t,∀d∈D,d∉Ioo (a t) (z t))
    (ha : ∀t,ag ≤ a t) (hz : ∀t,z t ≤ zg)
    (U : Set ℝ) (hopen : IsOpen U) (hU : U ⊆ Ioo (0:ℝ) 1) (hnegU : ∀r∈U,H r<0)
    (hneg : ∀t,∀r∈Ioo (a t) (z t),H r<0)
    (hcaps : ∀t,∀r∈Ioo (a t) (z t),wholeUnit U r=Ioo (a t) (z t))
    (hdisjoint : Pairwise (fun s t=>Disjoint (Ioo (a s) (z s)) (Ioo (a t) (z t))))
    (ms : ℕ → ℕ) (hms : Tendsto ms atTop atTop) (w : ℕ → ℝ)
    (labels : τ → Fin bins) (b : Fin bins) (l u : ℝ) (f : Icc (0:ℝ) 1 →ᵇ ℝ)
    (C : ∀j,NativeConstructedCoordinates
      (sampleClockSteps q 0 (finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j)))
      (comparisonConstructedBin hc hk hkc hm hM n bins q α
        (finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j)) a z H D ag zg (w j) U b)
      (comparisonConstructedRowRadius hc hk hkc hm hM q α
        (finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j))) U)
    (hwidth : ∀j,2*δ ≤ (C j).x (C j).K)
    (hlabels : ∀j t,comparisonConstructedCapLabel hc hk hkc hm hM n bins hbins q α
      (finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j)) a z H D ag zg (w j) U t=labels t)
    (hrep : ∀j t,let as := finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j)
      let rep := comparisonConstructedCapRepresentative hc hk hkc hm hM q α as a z H D ag zg t
      rep∈comparisonConstructedRows hc hk hkc hm hM q α as a z H D ag zg ∧
        comparisonConstructedRowRadius hc hk hkc hm hM q α as rep∈Ioo (a t) (z t))
    (hgeom : ∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
      (r∈NativeSelectedMask.finiteSupport
        (fun i=>comparisonSweepQuantile hc hk hkc hm hM α
          (partitionPoint 0 (finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j)) i))
        (comparisonConstructedBin hc hk hkc hm hM n bins q α
          (finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j)) a z H D ag zg (w j) U b) ↔
       r∈(Ioo ag zg ∩ NativeSelectedMask.fixedSupport a z H) ∩ Ioo l u))
    (hf : Tendsto (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM q α
      (finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j))
      (finiteCutMasses_ordered _ (finiteBoundaryMassNodes_bound _ (fun d hd=>by
        obtain ⟨r,_,rfl⟩:=Finset.mem_image.mp hd;exact (α.val.property.1 r).2)) (ms j))
      (comparisonConstructedBin hc hk hkc hm hM n bins q α
        (finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j)) a z H D ag zg (w j) U b)) atTop (𝓝 f)) :
    NativeConstructedBinLimit hc hk hkc hm hM n bins q α
      (fun j=>finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j))
      a z H D ag zg δ w U b C labels l u f := by
  let as := fun j=>finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j)
  have hnodes := finiteBoundaryMassNodes_bound (D.image α.val.val) (fun d hd=>by
    obtain ⟨r,_,rfl⟩:=Finset.mem_image.mp hd;exact (α.val.property.1 r).2)
  have ho j : MassOrdered 0 (as j) := finiteCutMasses_ordered _ hnodes (ms j)
  have he j : partitionEnd 0 (as j)=1 := finiteCutMasses_end _ hnodes (ms j)
  let mesh := fun j=>((ms j+1:ℕ):ℝ)⁻¹
  have hmesh j : PartitionMesh (mesh j) 0 (as j) := finiteCutMasses_mesh _ hnodes (ms j)
  have hlim : Tendsto mesh atTop (𝓝 0) := uniformMasses_mesh_tendsto.comp hms
  let J := fun j=>comparisonConstructedBin hc hk hkc hm hM n bins q α (as j) a z H D ag zg (w j) U b
  let B := {t : τ // labels t=b}
  let A := (Ioo ag zg ∩ {r | H r=0}) ∩ Ioo l u
  let rep := fun j t=>comparisonConstructedCapRepresentative hc hk hkc hm hM q α (as j) a z H D ag zg t
  let cl := fun t : B=>f ⟨a t.val,hD _ (haD t.val)⟩
  let cr := fun t : B=>f ⟨z t.val,hD _ (hzD t.val)⟩
  have hcoords (t : B) := comparisonConstructedBin_cap_coordinates_tendsto hc hk hkc hm hM n bins hbins
    q α a z H D ag zg U hD ms hms w t.val b (haD t.val) (hzD t.val) (haz t.val)
    (hinterior t.val) (ha t.val) (hz t.val) (hcaps t.val) C
    (fun j=>hrep j t.val) (fun j=>(hlabels j t.val).trans t.property) f hf
  have hgeometry := comparisonConstructedBin_column_geometry hc hk hkc hm hM n bins hbins q α
    as mesh ho he hmesh hlim a z H hH D hag.le hzg ha hz w U hneg hcaps labels hlabels hrep b l u C hgeom
  refine ⟨cl,cr,?_,?_⟩
  · intro t
    refine ⟨?_,?_,(hcoords t).2.2.1,(hcoords t).2.2.2⟩
    · simp [cl,comparisonContactLimitCoordinate,projIcc_of_mem _ (hD _ (haD t.val))]
    · simp [cr,comparisonContactLimitCoordinate,projIcc_of_mem _ (hD _ (hzD t.val))]
  · apply comparisonNativeSideColumn_full_L1_from_uniform_cumulative hc hk hkc hm hM q α hag hzg hδ
      A (comparisonConstructedContact_measurable H hH hag.le hzg) (fun r hr=>hr.1.1)
      H hopen hU hnegU as mesh ho he hmesh hlim (fun j=>(C j).K) J (fun j=>(C j).unit)
      (fun j=>(C j).x) (fun j=>(C j).start) (fun j=>(C j).strict_of_width hδ (hwidth j))
      (fun j=>(C j).mass) (fun j=>(C j).order) hwidth ?_ ?_ (fun j=>(C j).classes) hgeometry.1
      f hf (fun t : B=>a t.val) (fun t=>z t.val) cl cr (fun j t=>(C j).unit (rep j t.val))
      (fun t=>(hcoords t).2.2.2) (fun t=>(hcoords t).1) (fun t=>(hcoords t).2.1) ?_ ?_
      hgeometry.2.1 hgeometry.2.2
    · intro j
      rw [(C j).width]
      exact (physicalWindowMass_mem_Icc_one _ (sampleClockSteps_ordered q (as j) (ho j)) (J j)).2
    · intro j i hi
      exact (Finset.mem_filter.mp (comparisonConstructedBin_subset hc hk hkc hm hM n bins q α
        (as j) a z H D ag zg (w j) U b hi)).2.1
    · intro s t hst
      exact hdisjoint (fun h=>hst (Subtype.ext h))
    · intro t
      apply Set.disjoint_left.mpr
      intro r hr hrA
      have hh := hneg t.val r hr
      rw [hrA.1.2] at hh
      exact (lt_irrefl 0) hh

theorem comparisonConstructedBins_exists_full_limits {τ : Type*} [Fintype τ]
    (n bins : ℕ) (hbins : 0<bins) (q : ℝ → FeatureIndex n → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M)
    (a z : τ → ℝ) (H : ℝ → ℝ) (hH : ContinuousOn H (Icc (0:ℝ) 1))
    (D : Finset ℝ) {ag zg δ : ℝ} (hag : 0<ag) (hzg : zg ≤ 1) (hδ : 0<δ)
    (hD : ∀d∈D,d∈Icc (0:ℝ) 1) (haD : ∀t,a t∈D) (hzD : ∀t,z t∈D)
    (haz : ∀t,a t<z t) (hinterior : ∀t,∀d∈D,d∉Ioo (a t) (z t))
    (ha : ∀t,ag ≤ a t) (hz : ∀t,z t ≤ zg)
    (U : Set ℝ) (hopen : IsOpen U) (hU : U ⊆ Ioo (0:ℝ) 1) (hnegU : ∀r∈U,H r<0)
    (hneg : ∀t,∀r∈Ioo (a t) (z t),H r<0)
    (hcaps : ∀t,∀r∈Ioo (a t) (z t),wholeUnit U r=Ioo (a t) (z t))
    (hdisjoint : Pairwise (fun s t=>Disjoint (Ioo (a s) (z s)) (Ioo (a t) (z t))))
    (w : ℕ → ℝ) (hw : ∀j,0<w j) :
    ∃ms : ℕ → ℕ,StrictMono ms ∧
    let as := fun j=>finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) (ms j)
    let J := fun j b=>comparisonConstructedBin hc hk hkc hm hM n bins q α (as j) a z H D ag zg (w (ms j)) U b
    let F := Ioo ag zg ∩ NativeSelectedMask.fixedSupport a z H
    ∃C : ∀j b,NativeConstructedCoordinates (sampleClockSteps q 0 (as j)) (J j b)
      (comparisonConstructedRowRadius hc hk hkc hm hM q α (as j)) U,
    ∃l u : Fin bins → Icc (0:ℝ) 1,∃f : Fin bins → (Icc (0:ℝ) 1 →ᵇ ℝ),
    ∃labels : τ → Fin bins,∃keep : Fin bins → Bool,
      (∀j t,comparisonConstructedCapLabel hc hk hkc hm hM n bins hbins q α (as j)
        a z H D ag zg (w (ms j)) U t=labels t) ∧
      (∀j b,2*δ ≤ (C j b).x (C j b).K ↔ keep b=true) ∧
      (∀j,(∑b : Fin bins,if keep b then 0 else (C j b).x (C j b).K) ≤ 2*(bins:ℝ)*δ) ∧
      (∀b,
        (keep b=true → NativeConstructedBinLimit hc hk hkc hm hM n bins q α as a z H D
          ag zg δ (fun j=>w (ms j)) U b (fun j=>C j b) labels (l b).val (u b).val (f b)) ∧
        (∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
          (r∈NativeSelectedMask.finiteSupport
            (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)) (J j b) ↔
            r∈F ∩ Ioo (l b).val (u b).val)) ∧
        Tendsto (fun j=>(C j b).x (C j b).K) atTop (𝓝 (f b ⟨1,by simp⟩)) ∧
        Tendsto (fun j=>∫v in Icc (0:ℝ) 1,
          |massStepFunction (as j) (nativeSelectedColumn (J j b) (C j b).unit (fun _=>1)) v-
            (F ∩ Ioo (l b).val (u b).val).indicator (fun _=>1)
              (comparisonSweepQuantile hc hk hkc hm hM α v)|) atTop (𝓝 0)) ∧
      Tendsto (fun j=>∫v in Icc (0:ℝ) 1,
        |massStepFunction (as j) (nativeSelectedColumn (nativeKeptRows (J j) keep) (fun _=>(0:Fin 1))
          (fun _=>1)) v-
          (nativeKeptSupport (fun b=>F ∩ Ioo (l b).val (u b).val) keep).indicator (fun _=>1)
            (comparisonSweepQuantile hc hk hkc hm hM α v)|) atTop (𝓝 0) ∧
      Tendsto (fun j=>physicalWindowMass (sampleClockSteps q 0 (as j)) 0 (nativeKeptRows (J j) keep))
        atTop (𝓝 (∫v in Icc (0:ℝ) 1,
          (nativeKeptSupport (fun b=>F ∩ Ioo (l b).val (u b).val) keep).indicator (fun _=>1)
            (comparisonSweepQuantile hc hk hkc hm hM α v))) := by
  let grid := fun j=>finiteCutMasses (finiteBoundaryMassNodes (D.image α.val.val)) j
  have hnodes := finiteBoundaryMassNodes_bound (D.image α.val.val) (fun d hd=>by
    obtain ⟨r,_,rfl⟩:=Finset.mem_image.mp hd;exact (α.val.property.1 r).2)
  have ho j : MassOrdered 0 (grid j) := finiteCutMasses_ordered _ hnodes j
  have he j : partitionEnd 0 (grid j)=1 := finiteCutMasses_end _ hnodes j
  let mesh := fun j : ℕ=>((j+1:ℕ):ℝ)⁻¹
  have hmesh j : PartitionMesh (mesh j) 0 (grid j) := finiteCutMasses_mesh _ hnodes j
  have hlim : Tendsto mesh atTop (𝓝 0) := uniformMasses_mesh_tendsto
  have hrepEventually : ∀ᶠ j in atTop,∀t,
      let rep := comparisonConstructedCapRepresentative hc hk hkc hm hM q α (grid j) a z H D ag zg t
      rep∈comparisonConstructedRows hc hk hkc hm hM q α (grid j) a z H D ag zg ∧
        comparisonConstructedRowRadius hc hk hkc hm hM q α (grid j) rep∈Ioo (a t) (z t) := by
    apply Filter.eventually_all.mpr
    intro t
    exact comparisonConstructedCapRepresentative_eventually hc hk hkc hm hM q α grid mesh ho he
      hmesh hlim a z H D hag.le hzg t (ha t) (hz t) (haz t) (hinterior t)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hrepEventually
  have hshift : StrictMono (fun j : ℕ=>j+N) := fun i j hij=>Nat.add_lt_add_right hij N
  let as := fun j=>grid (j+N)
  obtain ⟨C,l,u,f,labels,keep,φ,hφ,hlabels,hkeep,hsub⟩ :=
    comparisonConstructedBins_exists_common_family hc hk hkc hm hM n bins hbins q α as
      (fun j=>mesh (j+N)) (fun j=>ho (j+N)) (fun j=>he (j+N)) (fun j=>hmesh (j+N))
      (hlim.comp hshift.tendsto_atTop) a z H hH D hag.le hzg (fun j=>w (j+N)) (fun j=>hw (j+N)) U δ
  let ms := fun j=>φ j+N
  have hms : StrictMono ms := hshift.comp hφ
  let J := fun j b=>comparisonConstructedBin hc hk hkc hm hM n bins q α (grid (ms j))
    a z H D ag zg (w (ms j)) U b
  have hJ j b i (hi : i∈J j b) : i.val<(grid (ms j)).length := by
    have hh := comparisonConstructedRows_subset hc hk hkc hm hM q α (grid (ms j)) a z H D ag zg
      (comparisonConstructedBin_subset hc hk hkc hm hM n bins q α (grid (ms j)) a z H D ag zg
        (w (ms j)) U b hi)
    exact ((comparisonNativeSelectedRows_mem hc hk hkc hm hM q α (grid (ms j)) a z H D i).mp hh).1
  refine ⟨ms,hms,fun j b=>C (φ j) b,l,u,f,labels,keep,hlabels,hkeep,?_,?_,?_,?_⟩
  · exact constructed_stable_small_bin_ledger (fun j b=>(C (φ j) b).x (C (φ j) b).K) keep hδ.le hkeep
  · intro b
    refine ⟨?_,(hsub b).2.1,(hsub b).2.2.1,(hsub b).2.2.2⟩
    intro hb
    exact comparisonConstructedBin_full_L1 hc hk hkc hm hM n bins hbins q α a z H hH D hag hzg hδ
      hD haD hzD haz hinterior ha hz U hopen hU hnegU hneg hcaps hdisjoint ms hms.tendsto_atTop
      (fun j=>w (ms j)) labels b (l b).val (u b).val (f b) (fun j=>C (φ j) b)
      (fun j=>(hkeep j b).mpr hb) hlabels (fun j=>hN (φ j+N) (by omega))
      (hsub b).2.1 (hsub b).1
  · exact comparisonNativeKeptUnion_mass_L1 hc hk hkc hm hM q α (fun j=>grid (ms j))
      (fun j=>ho (ms j)) (fun j=>he (ms j)) J hJ (fun _=>1) (fun _ _=>0) keep
      (fun b=>(Ioo ag zg ∩ NativeSelectedMask.fixedSupport a z H) ∩ Ioo (l b).val (u b).val)
      (fun b=>(hsub b).2.1)
  · exact comparisonNativeKeptUnion_mass_tendsto hc hk hkc hm hM q α (fun j=>grid (ms j))
      (fun j=>ho (ms j)) (fun j=>he (ms j)) J hJ (fun _=>1) (fun _ _=>0) keep
      (fun b=>(Ioo ag zg ∩ NativeSelectedMask.fixedSupport a z H) ∩ Ioo (l b).val (u b).val)
      (fun _=>(comparisonConstructedSupport_measurable a z H hH hag.le hzg).inter measurableSet_Ioo)
      (fun b=>(hsub b).2.1)

end
end OAI.SKFluctuations.LaplaceWindowFormalization
