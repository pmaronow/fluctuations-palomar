module

public import ComparisonActualHighWallSelectedCommonFamily
public import ComparisonActualHighWallRetainedRaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 26000000
attribute [local instance] Classical.propDecidable
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

structure SelectedMasterFamily
    (a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (P : a.Potential) {ι : Type*} (c : ι→ShiftedCapInterval a P)
    (Dcuts : Finset ℝ) (ag zg : ℝ) (bins : ℕ) (hbins : 0< bins)
    (w cut : ℝ) (ell : ℕ) (Q : ℝ) where
  nodes : List PositiveMass
  bound : ∀u∈nodes,u.val ≤ 1
  retains : ∀d∈Dcuts,∀hp : 0< a.alpha.val.val d,
    (⟨a.alpha.val.val d,hp⟩:PositiveMass)∈nodes
  sampler : ℕ→ℕ
  strict : StrictMono sampler
  l : Fin bins→Icc (0:ℝ) 1
  u : Fin bins→Icc (0:ℝ) 1
  f : Fin bins→(Icc (0:ℝ) 1→ᵇℝ)
  labels : ι→Fin bins
  keep : Fin bins→Bool
  raw : ∀j,physicalRawRatio (n+1) ell
    (sampleClockSteps a.shiftedNativeModel.q 0 (finiteCutMasses nodes (sampler j))) 0 a.xs
    (Measure.pi fun k=> gaussianReal 0 (a.shiftedNativeModel.q 0 k)) id measurable_id ≤ Q
  representatives : ∀j t,
    let as:=finiteCutMasses nodes (sampler j)
    let rep:=P.retainedCapRepresentative c Dcuts ag zg as t
    rep∈P.retainedRows c Dcuts ag zg as ∧
      a.shiftedNativeModel.rowRadius as rep∈Ioo (c t).left (c t).right
  capLabels : ∀j t,P.retainedCapLabel c Dcuts ag zg
    (finiteCutMasses nodes (sampler j)) bins hbins w t=labels t
  cutoffs : ∀j b,2*cut ≤
    (P.retainedBinCoordinates c Dcuts ag zg (finiteCutMasses nodes (sampler j))
      (finiteCutMasses_ordered nodes bound (sampler j)) bins w b).x
        (P.retainedBinCoordinates c Dcuts ag zg (finiteCutMasses nodes (sampler j))
          (finiteCutMasses_ordered nodes bound (sampler j)) bins w b).K ↔ keep b=true
  coordinates : ∀b,Tendsto (fun j=> a.actualCDF (finiteCutMasses nodes (sampler j))
    (finiteCutMasses_ordered nodes bound (sampler j))
    (P.retainedBin c Dcuts ag zg (finiteCutMasses nodes (sampler j)) bins w b)) atTop (𝓝 (f b))
  geometry : ∀b,∀ᵐr∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠj in atTop,
    (r∈NativeSelectedMask.finiteSupport (fun i=> a.shiftedNativeModel.R
      (partitionPoint 0 (finiteCutMasses nodes (sampler j)) i))
      (P.retainedBin c Dcuts ag zg (finiteCutMasses nodes (sampler j)) bins w b) ↔
        r∈P.retainedSupport c ag zg∩Ioo (l b).val (u b).val)
  widths : ∀b,Tendsto (fun j=>
    (P.retainedBinCoordinates c Dcuts ag zg (finiteCutMasses nodes (sampler j))
      (finiteCutMasses_ordered nodes bound (sampler j)) bins w b).x
        (P.retainedBinCoordinates c Dcuts ag zg (finiteCutMasses nodes (sampler j))
          (finiteCutMasses_ordered nodes bound (sampler j)) bins w b).K)
      atTop (𝓝 (f b ⟨1,by simp⟩))

end ActualHighWallOverlapMinimum

theorem eventually_exists_actual_high_wall_selected_master
    (ell : ℕ) (hell : 2< ell) (Bclock : ℝ) {margin delta cl cu Az C0 Ct D : ℝ}
    (hm : 0< margin) (hdelta : 0< delta) (hroom : delta<3*margin)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0 ≤ Az) (hC0 : 0< C0) (hCt : 0 ≤ Ct) :
    ∃Q : ℝ,1 ≤ Q ∧ ∀ᶠn : ℕ in atTop,
      ∀(a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
        (P : a.Potential) (ι : Type*) [Fintype ι] (c : ι→ActualHighWallOverlapMinimum.ShiftedCapInterval a P)
        (Dcuts : Finset ℝ) (ag zg : ℝ) (bins : ℕ) (hbins : 0< bins) (w cut : ℝ),
        a.data.rmin< ag → zg ≤ 1 → 0< w →
        (∀t,ag ≤ (c t).left) → (∀t,(c t).right ≤ zg) →
        (∀t,∀d∈Dcuts,d∉Ioo (c t).left (c t).right) →
        Nonempty (ActualHighWallOverlapMinimum.SelectedMasterFamily a P c Dcuts ag zg bins hbins w cut ell Q) := by
  have horder : ell-1+1=ell:=by omega
  obtain ⟨Craw,hCraw,Hraw⟩:=eventually_actual_high_wall_original_boundary_raw (ell-1) Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  let Q:=max 1 (Real.sqrt (2*Craw))
  refine ⟨Q,le_max_left _ _,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually Hraw] with n hn
  intro a P ι inst c Dcuts ag zg bins hbins w cut hag hzg hw hleft hright hinterior
  let extra:=finiteBoundaryMassNodes (Dcuts.image a.alpha.val.val)
  have hextra : ∀u∈extra,u.val ≤ 1:=finiteBoundaryMassNodes_bound _ (fun d hd=> by
    obtain ⟨r,_,rfl⟩:=Finset.mem_image.mp hd
    exact (a.alpha.val.property.1 r).2)
  obtain ⟨us,hus,_,hretains,hraw⟩:=hn a (⟨1,by norm_num⟩:PositiveMass) le_rfl extra hextra
  have retain d (hd : d∈Dcuts) (hp : 0< a.alpha.val.val d) :
      (⟨a.alpha.val.val d,hp⟩:PositiveMass)∈us:=
    hretains _ (finiteBoundaryMassNodes_mem _
      (Finset.mem_image.mpr ⟨d,hd,rfl⟩) hp)
  have rawBound : ∀ᶠj in atTop,physicalRawRatio (n+1) ell
      (sampleClockSteps a.shiftedNativeModel.q 0 (finiteCutMasses us j)) 0 a.xs
      (Measure.pi fun k=> gaussianReal 0 (a.shiftedNativeModel.q 0 k)) id measurable_id ≤ Q:=by
    filter_upwards [hraw] with j hj
    dsimp only at hj
    rw [horder] at hj
    have HS:=Real.sq_sqrt (show 0 ≤ 2*Craw by positivity)
    have Hsqrt:=Real.sqrt_nonneg (2*Craw)
    apply le_trans _ (le_max_right 1 (Real.sqrt (2*Craw)))
    nlinarith [hj.1]
  let grid:=fun j=> finiteCutMasses us j
  let mesh:=fun j : ℕ=>((j+1:ℕ):ℝ)⁻¹
  have ho j : MassOrdered 0 (grid j):=finiteCutMasses_ordered _ hus j
  have he j : partitionEnd 0 (grid j)=1:=finiteCutMasses_end _ hus j
  have hmesh j : PartitionMesh (mesh j) 0 (grid j):=finiteCutMasses_mesh _ hus j
  have hm0 j : 0 ≤ mesh j:=by positivity
  have hlim : Tendsto mesh atTop (𝓝 0):=uniformMasses_mesh_tendsto
  have hrep : ∀ᶠj in atTop,∀t,
      let rep:=P.retainedCapRepresentative c Dcuts ag zg (grid j) t
      rep∈P.retainedRows c Dcuts ag zg (grid j) ∧
        a.shiftedNativeModel.rowRadius (grid j) rep∈Ioo (c t).left (c t).right:=by
    apply Filter.eventually_all.mpr
    intro t
    exact P.retainedCapRepresentative_eventually c Dcuts grid mesh ho he hmesh hm0 hlim hag hzg
      t (hleft t) (hright t) (hinterior t)
  obtain ⟨N,hN⟩:=eventually_atTop.mp (rawBound.and hrep)
  have hshift : StrictMono (fun j : ℕ=> j+N):=fun i j hij=> Nat.add_lt_add_right hij N
  obtain ⟨l,u,f,labels,keep,φ,hφ,hlabels,hkeep,hsub⟩:=P.retainedBins_exists_common_family c Dcuts
    (fun j=> grid (j+N)) (fun j=> mesh (j+N)) (fun j=> ho (j+N)) (fun j=> he (j+N))
    (fun j=> hmesh (j+N)) (fun j=> hm0 (j+N)) (hlim.comp hshift.tendsto_atTop) hag hzg
    bins hbins (fun _=> w) (fun _=> hw) cut
  exact ⟨{
    nodes := us
    bound := hus
    retains := retain
    sampler := fun j=>φ j+N
    strict := hshift.comp hφ
    l := l
    u := u
    f := f
    labels := labels
    keep := keep
    raw := fun j=>(hN (φ j+N) (by omega)).1
    representatives := fun j=>(hN (φ j+N) (by omega)).2
    capLabels := hlabels
    cutoffs := hkeep
    coordinates := fun b=>(hsub b).1
    geometry := fun b=>(hsub b).2.1
    widths := fun b=>(hsub b).2.2 }⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
