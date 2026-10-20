module

public import ComparisonNativeMasterUnitEndpoints
public import ComparisonNativeConstructedColumnAssembly

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
theorem comparisonConstructedBin_cap_coordinates_tendsto_master {τ : Type*}
    (n bins : ℕ) (hbins : 0<bins) (q : ℝ → FeatureIndex n → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M)
    (a z : τ → ℝ) (H : ℝ → ℝ) (D : Finset ℝ)
    (us : List PositiveMass) (hnodes : ∀u∈us,u.val ≤ 1)
    (hretain : ∀d∈D,∀hp : 0<α.val.val d,(⟨α.val.val d,hp⟩ : PositiveMass)∈us) (ag zg : ℝ) (U : Set ℝ)
    (hD : ∀d∈D,d∈Icc (0:ℝ) 1)
    (ms : ℕ → ℕ) (hms : Tendsto ms atTop atTop) (w : ℕ → ℝ)
    (t : τ) (b : Fin bins) (ha : a t∈D) (hz : z t∈D) (haz : a t<z t)
    (hinterior : ∀d∈D,d∉Ioo (a t) (z t)) (hag : ag ≤ a t) (hzg : z t ≤ zg)
    (hcap : ∀r∈Ioo (a t) (z t),wholeUnit U r=Ioo (a t) (z t))
    (C : ∀j,NativeConstructedCoordinates
      (sampleClockSteps q 0 (finiteCutMasses us (ms j)))
      (comparisonConstructedBin hc hk hkc hm hM n bins q α
        (finiteCutMasses us (ms j)) a z H D ag zg (w j) U b)
      (comparisonConstructedRowRadius hc hk hkc hm hM q α
        (finiteCutMasses us (ms j))) U)
    (hrep : ∀j,let as := finiteCutMasses us (ms j)
      let rep := comparisonConstructedCapRepresentative hc hk hkc hm hM q α as a z H D ag zg t
      rep∈comparisonConstructedRows hc hk hkc hm hM q α as a z H D ag zg ∧
        comparisonConstructedRowRadius hc hk hkc hm hM q α as rep∈Ioo (a t) (z t))
    (hlabel : ∀j,comparisonConstructedCapLabel hc hk hkc hm hM n bins hbins q α
      (finiteCutMasses us (ms j)) a z H D ag zg (w j) U t=b)
    (f : Icc (0:ℝ) 1 →ᵇ ℝ)
    (hf : Tendsto (fun j=>comparisonSelectedCumulativeMap hc hk hkc hm hM q α
      (finiteCutMasses us (ms j))
      (finiteCutMasses_ordered _ hnodes (ms j))
      (comparisonConstructedBin hc hk hkc hm hM n bins q α
        (finiteCutMasses us (ms j)) a z H D ag zg (w j) U b))
      atTop (𝓝 f)) :
    let as := fun j=>finiteCutMasses us (ms j)
    let rep := fun j=>comparisonConstructedCapRepresentative hc hk hkc hm hM q α (as j) a z H D ag zg t
    Tendsto (fun j=>(C j).x ((C j).unit (rep j)).val) atTop (𝓝 (f ⟨a t,hD _ ha⟩)) ∧
    Tendsto (fun j=>(C j).x (((C j).unit (rep j)).val+1)) atTop (𝓝 (f ⟨z t,hD _ hz⟩)) ∧
    f ⟨z t,hD _ hz⟩-f ⟨a t,hD _ ha⟩=α.val.val (z t)-α.val.val (a t) ∧
    f ⟨a t,hD _ ha⟩<f ⟨z t,hD _ hz⟩ := by
  dsimp only
  let Dm := D.image α.val.val
  let as := fun j=>finiteCutMasses us (ms j)
  let J := fun j=>comparisonConstructedBin hc hk hkc hm hM n bins q α (as j) a z H D ag zg (w j) U b
  let rad := fun j=>comparisonConstructedRowRadius hc hk hkc hm hM q α (as j)
  let rep := fun j=>comparisonConstructedCapRepresentative hc hk hkc hm hM q α (as j) a z H D ag zg t
  have hDm : ∀d∈Dm,d∈Icc (0:ℝ) 1 := by
    intro d hd
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hd
    exact α.val.property.1 r
  have hDmRetain : ∀d∈Dm,∀hp : 0<d,(⟨d,hp⟩ : PositiveMass)∈us := by
    intro d hd hp
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hd
    exact hretain r hr hp
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
    exact comparisonConstructedBin_cap_fibre_master hc hk hkc hm hM n bins q α a z H D us hnodes hretain ag zg (w j) U
      (ms j) t b hD ha hz haz hinterior hag hzg hcap (rep j) (hrep j).2 (congrArg Fin.val (hlabel j))
  let T := fun j=>(J j).filter (fun i=>(C j).unit i=(C j).unit (rep j))
  have hT j : (T j).Nonempty := ⟨rep j,Finset.mem_filter.mpr ⟨hrepJ j,rfl⟩⟩
  let p := fun j=>(T j).min' (hT j)
  let qq := fun j=>(T j).max' (hT j)
  have hp j := Finset.mem_filter.mp (Finset.min'_mem (T j) (hT j))
  have hq j := Finset.mem_filter.mp (Finset.max'_mem (T j) (hT j))
  exact comparison_retained_cap_unit_endpoint_coordinates_tendsto_master hc hk hkc hm hM q α Dm hDm us hnodes hDmRetain
    ms hms (hD _ ha) (hD _ hz) haz (Finset.mem_image.mpr ⟨a t,ha,rfl⟩)
    (Finset.mem_image.mpr ⟨z t,hz,rfl⟩) (fun j=>(C j).K) J (fun j=>(C j).unit)
    (fun j=>(C j).unit (rep j)) (fun j=>(C j).x) (fun j=>(C j).start)
    (fun j=>(C j).mass) (fun j=>(C j).order) hfilter p qq (fun j=>(hp j).1) (fun j=>(hq j).1)
    (fun j=>(hp j).2) (fun j=>(hq j).2)
    (fun j i hi hu=>Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hi,hu⟩))
    (fun j i hi hu=>Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hi,hu⟩)) f hf

end

end OAI.SKFluctuations.LaplaceWindowFormalization
