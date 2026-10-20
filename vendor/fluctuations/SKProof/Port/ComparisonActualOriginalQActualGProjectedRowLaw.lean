module

public import SKProof.Port.ComparisonActualOriginalQGTripleRowAlgebra
public import ComparisonSignedCavityActualGProjectedRowLaw
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQGTripleRowSupport

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeActualDecoupledGProjectedResampling_original_q
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
    (cutFullVariance n q U 0 0 b h K) 0 (fun u v=>R u.1 v.1)
    (P.value (fun u v=>R u.1 v.1) C)

theorem native_actual_decoupled_G_projected_resampling_eq_spine_row_original_q
    {n : ℕ} {pre mid tail : List PositiveMass}
    {B T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T}
    (spine : NativeProjectionSpine base (pre.length+mid.length) P)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock)
    (ho : MassOrdered 0 (pre++(mid++tail))) (U : ℕ)
    (hs : pre.length+mid.length<U) (hU : U≤(pre++(mid++tail)).length)
    (V : ℝ) (hV : V≤M.sweepRadius (partitionPoint 0 (pre++(mid++tail)) U))
    (q : ℕ→RestCoordinate n→ℝ) :
    nativeActualDecoupledGProjectedResampling_original_q T P (pre.length+mid.length) U M q=
      nativeActualTripleSpineGRow_original_q spine M U V q := by
  have HC (j) :=native_ordered_source_center_eq_completed n M.sweepBf M.sweepHf
    (M.inherited_bf_monotone) (M.inherited_hf_monotone)
    (partitionPoint_mem (pre++(mid++tail)) ho j)
  unfold nativeActualDecoupledGProjectedResampling_original_q
  dsimp only
  rw [native_decoupled_G_spine_resampling_eq_conditional_word spine ho U hs hU q _ _ _ _
    (by intro j;rw [HC])
    (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
    (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))]
  rw [native_observed_high_word_sum_three]
  exact native_actual_triple_spine_G_high_sum_eq_row_original_q spine M ho U hs hU V hV q

end OAI.SKFluctuations.Cavity
