module

public import ComparisonActualHighWallThetaZeroSelectedBinsGeometry
public import ComparisonActualHighWallThetaZeroSelectedCapLabels
public import ComparisonActualHighWallSelectedCommonFamily

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option autoImplicit false
set_option maxHeartbeats 26000000
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem Potential.retainedBins_common_subsequence (P : Q.Potential) {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval Q P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ}
    (hag : Q.data.rmin < ag) (hzg : zg ≤ 1) (bins : ℕ)
    (w : ℕ→ℝ) (hw : ∀j,0<w j) :
    let m:=Q.shiftedNativeModel
    let Js:=fun j b=>P.retainedBin c Dcuts ag zg (as j) bins (w j) b
    let F:=P.retainedSupport c ag zg
    ∃l u : Fin bins→Icc (0:ℝ) 1,∃f : Fin bins→(Icc (0:ℝ) 1→ᵇℝ),
    ∃φ : ℕ→ℕ,StrictMono φ ∧ ∀b,
      Tendsto (fun j=>Q.actualCDF (as (φ j)) (ho (φ j)) (Js (φ j) b)) atTop (𝓝 (f b)) ∧
      (∀ᵐr∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠj in atTop,
        (r∈NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 (as (φ j)) i))
          (Js (φ j) b) ↔ r∈F∩Ioo (l b).val (u b).val)) := by
  dsimp only
  let Js:=fun j b=>P.retainedBin c Dcuts ag zg (as j) bins (w j) b
  obtain ⟨l,u,φ,hφ,hgeom⟩:=P.retainedBins_geometry c Dcuts as mesh ho he hmesh hm0 hlim hag hzg bins w hw
  obtain ⟨f,ψ,hψ,hcdf⟩:=Q.actualCDF_finite_exists_uniform_subseq
    (fun j=>as (φ j)) (fun j=>ho (φ j)) (fun j b=>Js (φ j) b)
  refine ⟨l,u,f,φ∘ψ,hφ.comp hψ,?_⟩
  intro b
  refine ⟨hcdf b,?_⟩
  filter_upwards [hgeom b] with r hr
  exact hψ.tendsto_atTop.eventually hr

theorem Potential.retainedBins_exists_common_family (P : Q.Potential) {ι : Type*} [Fintype ι]
    (c : ι→ShiftedCapInterval Q P) (Dcuts : Finset ℝ)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hm0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ}
    (hag : Q.data.rmin < ag) (hzg : zg ≤ 1) (bins : ℕ) (hbins : 0<bins)
    (w : ℕ→ℝ) (hw : ∀j,0<w j) (cut : ℝ) :
    let m:=Q.shiftedNativeModel
    let Js:=fun j b=>P.retainedBin c Dcuts ag zg (as j) bins (w j) b
    let co:=fun j b=>P.retainedBinCoordinates c Dcuts ag zg (as j) (ho j) bins (w j) b
    let F:=P.retainedSupport c ag zg
    ∃l u : Fin bins→Icc (0:ℝ) 1,∃f : Fin bins→(Icc (0:ℝ) 1→ᵇℝ),
    ∃labels : ι→Fin bins,∃keep : Fin bins→Bool,∃φ : ℕ→ℕ,StrictMono φ ∧
      (∀j t,P.retainedCapLabel c Dcuts ag zg (as (φ j)) bins hbins (w (φ j)) t=labels t) ∧
      (∀j b,2*cut ≤ (co (φ j) b).x (co (φ j) b).K ↔ keep b=true) ∧
      ∀b,Tendsto (fun j=>Q.actualCDF (as (φ j)) (ho (φ j)) (Js (φ j) b)) atTop (𝓝 (f b)) ∧
      (∀ᵐr∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠj in atTop,
        (r∈NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 (as (φ j)) i))
          (Js (φ j) b) ↔ r∈F∩Ioo (l b).val (u b).val)) ∧
      Tendsto (fun j=>(co (φ j) b).x (co (φ j) b).K) atTop (𝓝 (f b ⟨1,by simp⟩)) := by
  dsimp only
  let Js:=fun j b=>P.retainedBin c Dcuts ag zg (as j) bins (w j) b
  let co:=fun j b=>P.retainedBinCoordinates c Dcuts ag zg (as j) (ho j) bins (w j) b
  obtain ⟨l,u,f,ψ,hψ,hsub⟩:=P.retainedBins_common_subsequence c Dcuts as mesh ho he hmesh hm0 hlim hag hzg bins w hw
  let state : ℕ→(ι→Fin bins)×(Fin bins→Bool):=fun j=>
    (fun t=>P.retainedCapLabel c Dcuts ag zg (as (ψ j)) bins hbins (w (ψ j)) t,
      fun b=>decide (2*cut ≤ (co (ψ j) b).x (co (ψ j) b).K))
  obtain ⟨s,χ,hχ,hs⟩:=finite_state_constant_subsequence state
  let φ:=ψ∘χ
  refine ⟨l,u,f,s.1,s.2,φ,hψ.comp hχ,?_,?_,?_⟩
  · intro j t
    exact congrArg (fun v=>v.1 t) (hs j)
  · intro j b
    have hh : decide (2*cut ≤ (co (φ j) b).x (co (φ j) b).K)=s.2 b:=
      congrArg (fun v=>v.2 b) (hs j)
    exact eq_iff_iff.mp ((decide_eq_true_eq).symm.trans (congrArg (fun v=>v=true) hh))
  · intro b
    have hcdf:=(hsub b).1.comp hχ.tendsto_atTop
    have hgeom : ∀ᵐr∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠj in atTop,
        (r∈NativeSelectedMask.finiteSupport (fun i=>Q.shiftedNativeModel.R
          (partitionPoint 0 (as (φ j)) i)) (Js (φ j) b) ↔
            r∈P.retainedSupport c ag zg∩Ioo (l b).val (u b).val):=by
      filter_upwards [(hsub b).2] with r hr
      exact hχ.tendsto_atTop.eventually hr
    refine ⟨hcdf,hgeom,?_⟩
    have HE j : Q.actualCDF (as (φ j)) (ho (φ j)) (Js (φ j) b) ⟨1,by simp⟩=
        (co (φ j) b).x (co (φ j) b).K:=by
      rw [Q.actualCDF_one (as (φ j)) (ho (φ j)) (he (φ j)) (Js (φ j) b) ?_,(co (φ j) b).width]
      intro i hi
      exact ((P.retainedRows_mem c Dcuts ag zg (as (φ j)) i).mp
        (P.retainedBin_subset c Dcuts ag zg (as (φ j)) bins (w (φ j)) b hi)).2.2.2.1
    have HT:=selectedCumulative_uniform_moving_eval_tendsto _ (f b) hcdf
      (fun _=>(⟨1,by simp⟩:Icc (0:ℝ) 1)) ⟨1,by simp⟩ tendsto_const_nhds
    change Tendsto (fun j=>Q.actualCDF (as (φ j)) (ho (φ j)) (Js (φ j) b) ⟨1,by simp⟩)
      atTop (𝓝 (f b ⟨1,by simp⟩)) at HT
    simpa only [HE] using HT
end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
