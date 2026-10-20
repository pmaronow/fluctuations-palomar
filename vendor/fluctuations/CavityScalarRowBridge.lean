module

public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalProjection
public import SKFluctuationsOAI.Probability.SKFluctuations.MarkedAttachPreserves

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def scalarPlacementGamma {steps : List (GaussianStep (Fin 1))}
    (T : ReplicaTree (Fin 1) Bool steps) (s : T.Slot)
    (p : ReplicaTree.MarkedPlacement T) (x : ℝ) : ℝ :=
  p.tree.expect (fun _ => (1/2 : ℝ)) scalarFeature
    (fun σ => scalarFeature (p.tree.atSlot σ (p.embed s)) (fun _ => 1) *
      scalarFeature (p.tree.atSlot σ p.mark) (fun _ => 1)) (fun _ => x)

theorem scalarPlacementGamma_eq_eval {steps : List (GaussianStep (Fin 1))}
    (T : ReplicaTree (Fin 1) Bool steps) (s : T.Slot)
    (p : ReplicaTree.MarkedPlacement T) (x : ℝ) :
    scalarPlacementGamma T s p x = p.toPlacement.eval (fun _ => (1/2 : ℝ)) scalarFeature
      (fun σ => scalarFeature (T.atSlot σ s) (fun _ => 1))
      (fun σ => scalarFeature σ (fun _ => 1)) (fun _ => x) := by
  unfold scalarPlacementGamma ReplicaTree.Placement.eval
  congr 1
  funext σ
  simp only [p.restrict_at, p.spin_at]

theorem scalar_marked_row_eq (cs : List HeatClock)
    (T : ReplicaTree (Fin 1) Bool (heatSteps cs)) (a : ℝ) (s : T.Slot) (x : ℝ) :
    ((T.markedAttach a).map (fun p => p.coeff*scalarPlacementGamma T s p x)).sum =
      scalarCavityRow cs T a s x := by
  simp_rw [scalarPlacementGamma_eq_eval]
  unfold scalarCavityRow ReplicaTree.row ReplicaTree.rowList
  rw [← T.markedAttach_forget a]
  simp only [List.map_map]
  rfl

theorem scalar_marked_row_zero (cs : List HeatClock)
    (T : ReplicaTree (Fin 1) Bool (heatSteps cs)) {a : ℝ}
    (ho : OrderedSteps a (heatSteps (ι:=Fin 1) cs)) (s : T.Slot) :
    ((T.markedAttach a).map (fun p => p.coeff*scalarPlacementGamma T s p 0)).sum =
      (scalarTerminal.schedule cs).H 0 0 := by
  rw [scalar_marked_row_eq, scalarCavityRow_zero cs T ho s]

theorem scalar_marked_row_zero_bounds (cs : List HeatClock)
    (T : ReplicaTree (Fin 1) Bool (heatSteps cs)) {a : ℝ}
    (ho : OrderedSteps a (heatSteps (ι:=Fin 1) cs)) (s : T.Slot) :
    Real.exp (-4*(cs.map (fun c => (c.time:ℝ))).sum) ≤
      ((T.markedAttach a).map (fun p => p.coeff*scalarPlacementGamma T s p 0)).sum ∧
    ((T.markedAttach a).map (fun p => p.coeff*scalarPlacementGamma T s p 0)).sum ≤ 1 := by
  rw [scalar_marked_row_eq]
  exact scalarCavityRow_zero_bounds cs T ho s

theorem scalar_marked_row_preserved_test (cs : List HeatClock)
    (T : ReplicaTree (Fin 1) Bool (heatSteps cs)) {a : ℝ}
    (ho : OrderedSteps a (heatSteps (ι:=Fin 1) cs)) (s : T.Slot)
    (P : T.Assignment → ℝ) (x y : ℝ) :
    ((T.markedAttach a).map (fun p => p.coeff*scalarPlacementGamma T s p x *
      p.tree.expect (fun _ => (1/2 : ℝ)) scalarFeature (fun σ => P (p.restrict σ))
        (fun _ => y))).sum =
      scalarCavityRow cs T a s x*T.expect (fun _ => (1/2 : ℝ)) scalarFeature P (fun _ => y) := by
  have he : ((T.markedAttach a).map (fun p => p.coeff*scalarPlacementGamma T s p x *
      p.tree.expect (fun _ => (1/2 : ℝ)) scalarFeature (fun σ => P (p.restrict σ))
        (fun _ => y))).sum =
      ((T.markedAttach a).map (fun p => p.coeff*scalarPlacementGamma T s p x *
        T.expect (fun _ => (1/2 : ℝ)) scalarFeature P (fun _ => y))).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    rw [T.markedAttach_preserves (by intro σ; norm_num) scalarFeature ho p hp]
  rw [he, List.sum_map_mul_right, scalar_marked_row_eq]

end OAI.SKFluctuations.Cavity
