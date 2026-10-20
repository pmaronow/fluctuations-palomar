module

public import ComparisonSignedCavityGTripleRowSupport

@[expose] public section

noncomputable section
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeActualDecoupledGProjectedResampling
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : NativeGeneratedTest T) (star U : ℕ)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock)
    (q : ℕ→RestCoordinate n→ℝ) : ℝ :=
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let C:=fun j=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)
  let R:=fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))
  nativeActualOriginalGProjectedResampling T P.target star U K b C 0
    (cutFullVariance n q U 0 0 b h K) 0 (fun u v=>R u.1 v.1)
    (P.value (fun u v=>R u.1 v.1) C)

theorem native_actual_decoupled_G_projected_resampling_eq_spine_row
    {n : ℕ} {pre mid tail : List PositiveMass}
    {B T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T}
    (spine : NativeProjectionSpine base (pre.length+mid.length) P)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock)
    (ho : MassOrdered 0 (pre++(mid++tail))) (U : ℕ)
    (hs : pre.length+mid.length<U) (hU : U≤(pre++(mid++tail)).length)
    (V : ℝ) (hV : V≤M.R (partitionPoint 0 (pre++(mid++tail)) U))
    (q : ℕ→RestCoordinate n→ℝ) :
    nativeActualDecoupledGProjectedResampling T P (pre.length+mid.length) U M q=
      nativeActualTripleSpineGRow spine M U V q := by
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have HC (j) :=native_ordered_source_center_eq_completed n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
    (partitionPoint_mem (pre++(mid++tail)) ho j)
  unfold nativeActualDecoupledGProjectedResampling
  dsimp only
  rw [native_decoupled_G_spine_resampling_eq_conditional_word spine ho U hs hU q _ _ _ _
    (by intro j;rw [HC])
    (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))
    (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false)))]
  rw [native_observed_high_word_sum_three]
  exact native_actual_triple_spine_G_high_sum_eq_row spine M ho U hs hU V hV q

end OAI.SKFluctuations.Cavity
