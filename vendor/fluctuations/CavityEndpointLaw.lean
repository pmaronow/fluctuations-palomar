module

public import CavityEndpointCoordinates
public import CavitySpinRelabel

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

 theorem fullEndpointExpect_eq_nullCompleted (n U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as)
    (P : (T.relabelSpin (spinEquiv n)).Assignment → ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j => Sum.elim (fun _ => b j) (fun _ => h j)) b h K)
      (fun σ => P (T.relabelAssignment (spinEquiv n) σ)) 0 =
    (T.relabelSpin (spinEquiv n)).disorderExpect (uniformWeight (n+1)) (finiteFeature (n+1))
      0 (nullCompletedClock (n+1) b h) P 0 := by
  let R := T.relabelSpin (spinEquiv n)
  let Test := fun σ => P (T.relabelAssignment (spinEquiv n) σ)
  have he1 := T.disorderExpect_reindex (endpointCoordinateEquiv n) (fullWeight n) (fullFeature n)
    0 (cavityPath n U 1 1 (fun j => Sum.elim (fun _ => b j) (fun _ => h j)) b h K) Test 0
  simp only [map_zero,Pi.zero_apply] at he1
  rw [endpointClock_reindex] at he1
  have hv : Sum.elim (0 : BareCoordinate (n+1) → ℝ) (fun _ : Fin 1 => (0:ℝ)) = 0 := by
    funext i; cases i <;> rfl
  have hz1 := T.disorderExpect_zeroRow (fullWeight n)
    (reindexFeature (endpointCoordinateEquiv n) (fullFeature n)) 0 (bareClock (n+1) b h) Test 0
  rw [hv,map_zero] at hz1
  change T.disorderExpect _ _ 0 _ Test 0 = _ at he1
  rw [hz1] at he1
  have hf1 : (fun σ => (reindexFeature (endpointCoordinateEquiv n) (fullFeature n) σ).comp cavityEmbed) =
      bareFeature (n+1) ∘ spinEquiv n := funext (endpoint_restrict_bare n)
  rw [hf1] at he1
  have hw : fullWeight n = uniformWeight (n+1) ∘ spinEquiv n := by
    funext σ
    exact fullWeight_eq n σ
  rw [hw] at he1
  have hSpin := T.disorderExpect_relabelSpin (spinEquiv n) (uniformWeight (n+1))
    (bareFeature (n+1)) 0 (bareClock (n+1) b h) P 0
  have he2 := R.disorderExpect_reindex (completedCoordinateEquiv (n+1)) (uniformWeight (n+1))
    (finiteFeature (n+1)) 0 (nullCompletedClock (n+1) b h) P 0
  simp only [map_zero,Pi.zero_apply] at he2
  rw [nullCompletedClock_reindex] at he2
  have hz2 := R.disorderExpect_zeroRow (uniformWeight (n+1))
    (reindexFeature (completedCoordinateEquiv (n+1)) (finiteFeature (n+1))) 0 (bareClock (n+1) b h) P 0
  rw [hv,map_zero] at hz2
  change R.disorderExpect _ _ 0 _ P 0 = _ at he2
  rw [hz2] at he2
  have hf2 : (fun σ => (reindexFeature (completedCoordinateEquiv (n+1)) (finiteFeature (n+1)) σ).comp
      cavityEmbed) = bareFeature (n+1) := funext (completed_restrict_bare (n+1))
  rw [hf2] at he2
  rw [hw]
  exact he1.symm.trans (hSpin.trans he2)

 theorem fullEndpoint_overlap_moment_eq_nullCompletedPair (n m U : ℕ) (b h K : ℕ → ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (s t : T.Slot) (hst : s ≠ t) (S : ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cavityPath n U 1 1 (fun j => Sum.elim (fun _ => b j) (fun _ => h j)) b h K)
      (fun σ => |orderedOverlap (n+1) (joinSpin (T.atSlot σ s))
        (joinSpin (T.atSlot σ t))-S|^m) 0 =
    (ClockTree.pairClock as (T.splitIndex s t)).disorderExpect (uniformWeight (n+1))
      (finiteFeature (n+1)) 0 (nullCompletedClock (n+1) b h)
      (fun σ => |orderedOverlap (n+1) (ClockTree.pairSpin as (T.splitIndex s t) σ).1
        (ClockTree.pairSpin as (T.splitIndex s t) σ).2-S|^m) 0 := by
  let e := spinEquiv n
  let R := T.relabelSpin e
  let s' := T.relabelSlot e s
  let t' := T.relabelSlot e t
  have hst' : s' ≠ t' := fun H => hst ((T.relabelSlot e).injective H)
  have H := fullEndpointExpect_eq_nullCompleted n U b h K T
    (fun σ => |orderedOverlap (n+1) (R.atSlot σ s') (R.atSlot σ t')-S|^m)
  dsimp only [R,s',t',e] at H
  simp only [ClockTree.atSlot_relabel] at H
  change T.disorderExpect _ _ _ _ _ _ = R.disorderExpect _ _ _ _
    (fun σ => |orderedOverlap (n+1) (R.atSlot σ s') (R.atSlot σ t')-S|^m) 0 at H
  rw [R.disorderExpect_pairAtSlot_actual (uniformWeight_pos (n+1)) (finiteFeature (n+1)) ho
    0 (nullCompletedClock (n+1) b h) 0 s' t' hst'
    (fun σ τ => |orderedOverlap (n+1) σ τ-S|^m)] at H
  dsimp only [R,s',t',e] at H
  rw [ClockTree.splitIndex_relabel] at H
  exact H

end OAI.SKFluctuations.Cavity
