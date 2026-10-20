module

public import PhysicalFilledCellIncrement
public import PhysicalSampledNodeOverlapError
public import PhysicalComparisonRadiusSampling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 1000000
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparisonSweepQuantile_mass_spec (α : inverseIntegralConstraints 0 0 k M)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    α.val.val (comparisonSweepQuantile hc hk hkc hm hM α u)=u := by
  rw [comparisonSweepQuantile_eq hc hk hkc hm hM α hu]
  exact constrainedQuantile_spec zero_le_one hc hk hkc hm hM α ⟨u,hu⟩

theorem physicalComparisonSampledCell_increment
    {N d lam z : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N)
    (hd : 0 < d) (hnd : 1/N ≤ d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (before after : List PositiveMass) (v : PositiveMass)
    (ho : MassOrdered 0 (before++v::after))
    (hvorder : MassOrdered (partitionEnd 0 before) (v::after))
    (hz : z ≤ 1) (hRz : comparisonSweepQuantile hc hk hkc hm hM α v.val ≤ z) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let q := completedPathClock (n+1) bf hf
    let steps := sampleClockSteps q 0 (before++v::after)
    let ha : OrderedSteps 0 (steps++[]) := by
      simpa only [List.append_nil] using sampleClockSteps_ordered q _ ho
    ((R v.val-R (partitionEnd 0 before)).toNNReal:ℝ)*
      physicalRootedCapCellTrace n dphys e (q 0) steps [] ha before.length ≤
      (physicalPathSecondMoment (n+1) steps (q 0) (before.length+1)-
        physicalPathSecondMoment (n+1) steps (q 0) before.length)/
          ((n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let q := completedPathClock (n+1) bf hf
  let u := partitionEnd 0 before
  let common := sampleClockSteps q 0 before
  let st : GaussianStep (FeatureIndex (n+1)) := (v.val,fun j=>q v.val j-q u j)
  let extra := sampleClockSteps q v.val after
  have hsteps : sampleClockSteps q 0 (before++v::after)=(common++[st])++extra := by
    rw [sampleClockSteps_append]
    simp only [sampleClockSteps]
    dsimp only [common,st,extra,u]
    simp only [List.append_assoc,List.singleton_append]
  have hu01 : u∈Icc (0:ℝ) 1 := massOrdered_bounds hvorder
  have hv01 : v.val∈Icc (0:ℝ) 1 := ⟨v.property.le,(massOrdered_bounds hvorder.2.2).2⟩
  have hg : 0 < ((1/3)/Real.log N)*laplaceComparisonStrength d lam z :=
    mul_pos (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos d hlam z)
  let w : ℝ≥0 := (R v.val-R u).toNNReal
  have hsl : (((1/3)/Real.log N)*laplaceComparisonStrength d lam z)*(w:ℝ) ≤ st.2 (Sum.inl 0) := by
    have hh' := comparisonVariableEndpointField_radius_gap hc hk hkc hm hM
      hN hlog hd hnd hlam hld h hh hh0 α hu01 hv01 hvorder.2.1 hz hRz
    change _ ≤ _ at hh'
    change _ ≤ ((q v.val (Sum.inl 0)-q u (Sum.inl 0):ℝ≥0):ℝ)
    dsimp only [w]
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr
      (comparisonSweepQuantile_monotone hc hk hkc hm hM α hvorder.2.1))]
    exact hh'
  have ha' : OrderedSteps 0 (((common++[st])++extra)++[]) := by
    rw [List.append_nil,←hsteps]
    exact sampleClockSteps_ordered q _ ho
  have hi := physicalRootedCapCellTrace_full_mul_duration_le_increment n dphys e (q 0)
    common st extra [] ha' w hg (fun j=>by rfl) hsl
  simp only [←hsteps,List.append_nil] at hi
  simpa only [common,sampleClockSteps_length,List.append_nil,w,u,R,q,bf,hf] using hi

theorem physicalComparisonSampledNode_radius_error (n : ℕ) (b h : ℝ→ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (j : ℕ) (hj : j ≤ as.length)
    (hu : 0 < partitionPoint 0 as j) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let q := completedPathClock (n+1) b h
    let steps := sampleClockSteps q 0 as
    |physicalPathSecondMoment (n+1) steps (q 0) j-
      orderedPathS (n+1) b h (α.val.val (R (partitionPoint 0 as j)))| ≤
      mesh*(2*ClockTree.errorJetVariation 2 0 0*
        clockVariationBound (physicalFeatureCoordinateBound n) q) := by
  dsimp only
  rw [comparisonSweepQuantile_mass_spec hc hk hkc hm hM α (partitionPoint_mem as ho j)]
  exact physicalSampledNodeSecondMoment_error n b h hb hh as ho he hmesh j hj hu

theorem physicalComparisonSampledCell_increment_at_index
    {N d lam z : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N)
    (hd : 0 < d) (hnd : 1/N ≤ d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (j : ℕ) (hj : j < as.length)
    (hz : z ≤ 1) (hRz : comparisonSweepQuantile hc hk hkc hm hM α
      (partitionPoint 0 as (j+1)) ≤ z) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let q := completedPathClock (n+1) bf hf
    let steps := sampleClockSteps q 0 as
    let ha : OrderedSteps 0 (steps++[]) := by
      simpa only [List.append_nil] using sampleClockSteps_ordered q _ ho
    ((R (partitionPoint 0 as (j+1))-R (partitionPoint 0 as j)).toNNReal:ℝ)*
      physicalRootedCapCellTrace n dphys e (q 0) steps [] ha j ≤
      (physicalPathSecondMoment (n+1) steps (q 0) (j+1)-
        physicalPathSecondMoment (n+1) steps (q 0) j)/
          ((n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)) := by
  have hdecomp : as.take j++as[j]::as.drop (j+1)=as := by
    rw [←List.drop_eq_getElem_cons hj,List.take_append_drop]
  have hov : MassOrdered (partitionEnd 0 (as.take j)) (as[j]::as.drop (j+1)) := by
    rw [massPartition_take_end,←List.drop_eq_getElem_cons hj]
    exact massPartition_drop_ordered as ho j
  have hRz' : comparisonSweepQuantile hc hk hkc hm hM α as[j].val ≤ z := by
    simpa only [massPartition_point_succ_eq_getElem 0 as hj] using hRz
  have ht := physicalComparisonSampledCell_increment hc hk hkc hm hM hN hlog hd hnd
    hlam hld n dphys e b h hh hh0 α (as.take j) (as.drop (j+1)) as[j]
    (by simpa only [hdecomp] using ho) hov hz hRz'
  simp only [hdecomp,List.length_take,min_eq_left hj.le,massPartition_take_end,
    ←massPartition_point_succ_eq_getElem 0 as hj] at ht
  exact ht

theorem comparisonSampledRadius_point_mesh (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) {mesh : ℝ}
    (hmesh : PartitionMesh mesh 0 as) (j : ℕ) (hj : j < as.length) :
    comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as (j+1))-
      comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as j) ≤ mesh/c := by
  have hmass := partitionPoint_mono as ho (Nat.le_succ j)
  have hrad := comparisonSweepQuantile_monotone hc hk hkc hm hM α hmass
  have ht := (comparisonSweepQuantile_lipschitz hc hk hkc hm hM α).dist_le_mul
    (partitionPoint 0 as (j+1)) (partitionPoint 0 as j)
  simp only [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hmass),
    abs_of_nonneg (sub_nonneg.mpr hrad)] at ht
  change _ ≤ (1/c)*(partitionPoint 0 as (j+1)-partitionPoint 0 as j) at ht
  have hh := mul_le_mul_of_nonneg_left (massPartition_point_next_mesh as hmesh hj)
    (by positivity : 0 ≤ 1/c)
  exact ht.trans (by convert hh using 1 <;> ring)

theorem physicalSampledSecondMoment_monotoneOn (n : ℕ)
    (b h : ℝ→ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as) :
    MonotoneOn (fun j=>physicalPathSecondMoment n
      (sampleClockSteps (completedPathClock n b h) 0 as) (completedPathClock n b h 0) j)
      (Icc (0:ℕ) as.length) := by
  intro i hi j hj hij
  exact physicalPathSecondMoment_mono n _ (sampleClockSteps_ordered _ _ ho) _ hij
    (by simpa only [sampleClockSteps_length] using hj.2)
end
end OAI.SKFluctuations.LaplaceWindowFormalization
