module

public import ComparisonSignedCavityCurrentGOriginalLawRestoration
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQActualGProjectedRowLaw

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators

def nativeActualCoupledGProjectedResampling_original_q
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : NativeGeneratedTest T) (star U : ℕ)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock)
    (q : ℕ→RestCoordinate n→ℝ) : ℝ :=
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
  let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
  nativeActualOriginalGProjectedResampling T P.target star U K b C 0
    (cutFullVariance n q U 1 1 b h K) 0 (fun u v=>R u.1 v.1)
    (P.value (fun u v=>R u.1 v.1) C)

theorem native_actual_current_G_coupled_eq_decoupled_add_restoration_original_q
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star) (hs : star<U)
    (ho : MassOrdered 0 as)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock) :
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
      (fun _=>((M.sweepBf (partitionPoint 0 as j)):ℝ)) (fun _=>((M.sweepHf (partitionPoint 0 as j)):ℝ))
    nativeActualCoupledGProjectedResampling_original_q T P.live.test star U M q=
      nativeActualDecoupledGProjectedResampling_original_q T P.live.test star U M q+
      2*nativeActualGProjectedRestoration_original_q T P.live.test star U M q := by
  dsimp only
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.sweepHf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.sweepBf M.sweepHf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.sweepBf M.sweepHf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.sweepBf M.sweepHf
    (M.inherited_bf_monotone) (M.inherited_hf_monotone) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepBf u:ℝ) ≤ M.sweepBf v from M.inherited_bf_monotone hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.sweepHf u:ℝ) ≤ M.sweepHf v from M.inherited_hf_monotone hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.sweepBf M.sweepHf (M.inherited_bf_monotone) (M.inherited_hf_monotone)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HC j : S j=C j:=native_ordered_source_center_eq_completed n M.sweepBf M.sweepHf
    (M.inherited_bf_monotone) (M.inherited_hf_monotone) (partitionPoint_mem as ho j)
  have H:=native_generated_G_projected_resampling_law_restoration hP hi hs ho q b h K C
    (fun j=>by dsimp only [K];rw [HC]) R (nativeRestGeneratedTestValue T P.live.test R C)
    (fun j v=>by cases v <;> exact NNReal.coe_nonneg _)
    (fun v=>by cases v <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm
  simp only [native_rest_generated_value_eq_full] at H
  exact H

end OAI.SKFluctuations.Cavity
