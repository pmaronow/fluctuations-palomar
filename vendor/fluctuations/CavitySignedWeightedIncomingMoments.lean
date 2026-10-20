module

public import CavityProjectedPowerMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy

theorem physical_weighted_incoming_placement_abs_le (n k : ℕ)
    {steps : List (GaussianStep (FeatureIndex n))}
    (E : ReplicaTree (FeatureIndex n) (Spin n) steps)
    {a : ℝ} (ho : OrderedSteps a steps)
    (p : ReplicaTree.MarkedPlacement (ReplicaTree.single (S := Spin n) steps))
    (H : E.Assignment → ℝ) (s : E.Slot) (x : FeatureIndex n → ℝ) (center : ℝ) :
    let Y := physicalCenteredProjectedOverlap n steps x center
    let D := fun σ:p.tree.Assignment=>inner ℝ
      (WithLp.toLp 2 (normalizedSpin n
        (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ)))-
        WithLp.toLp 2 (normalizedSpin n (p.spin σ)))
      (physicalWeightedExteriorAnchor n E H s x)
    |p.tree.expect (uniformWeight n) (finiteFeature n) (fun σ=>
      (Y (p.spin σ)-Y (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ)))*
        Y (p.spin σ)^k*D σ) x| ≤
    Real.sqrt (Real.sqrt (
      p.tree.expect (uniformWeight n) (finiteFeature n) (fun σ=>
        (Y (p.spin σ)-Y (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ)))^4) x*
      p.tree.expect (uniformWeight n) (finiteFeature n) (fun σ=>(D σ)^4) x)*
      levelPairMean (uniformWeight n) (finiteFeature n)
        (fun σ τ=>|orderedOverlap n σ τ-center|^(2*k)) steps 0 x) := by
  dsimp only
  let Y := physicalCenteredProjectedOverlap n steps x center
  let A : p.tree.Assignment → ℝ := fun σ=>Y (p.spin σ)-
    Y (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ))
  let D : p.tree.Assignment → ℝ := fun σ=>inner ℝ
    (WithLp.toLp 2 (normalizedSpin n
      (ReplicaTree.singleEquiv (S := Spin n) steps (p.restrict σ)))-
      WithLp.toLp 2 (normalizedSpin n (p.spin σ)))
    (physicalWeightedExteriorAnchor n E H s x)
  have hfirst := p.tree.expect_mul_abs_le_sqrt (uniformWeight_pos n) (finiteFeature n) ho
    (fun σ=>A σ*D σ) (fun σ=>Y (p.spin σ)^k) x
  have hsecond := p.tree.expect_mul_abs_le_sqrt (uniformWeight_pos n) (finiteFeature n) ho
    (fun σ=>A σ^2) (fun σ=>D σ^2) x
  have hp : p.tree.expect (uniformWeight n) (finiteFeature n)
      (fun σ=>(Y (p.spin σ)^k)^2) x ≤
    levelPairMean (uniformWeight n) (finiteFeature n)
      (fun σ τ=>|orderedOverlap n σ τ-center|^(2*k)) steps 0 x := by
    convert physical_projected_target_power_moment_le n (2*k) p.tree ho p.mark x center using 1
    congr 1
    funext σ
    rw [p.spin_at]
    dsimp only [Y]
    rw [←pow_mul,Nat.mul_comm k 2]
    simp only [pow_mul,sq_abs]
  have hsecond' : p.tree.expect (uniformWeight n) (finiteFeature n)
      (fun σ=>(A σ*D σ)^2) x ≤
    Real.sqrt (p.tree.expect (uniformWeight n) (finiteFeature n) (fun σ=>A σ^4) x*
      p.tree.expect (uniformWeight n) (finiteFeature n) (fun σ=>D σ^4) x) := by
    have hn := p.tree.expect_nonneg (uniformWeight_pos n) (finiteFeature n) ho
      (fun σ=>mul_nonneg (sq_nonneg (A σ)) (sq_nonneg (D σ))) x
    rw [abs_of_nonneg hn] at hsecond
    simp only [←pow_mul,show 2*2=4 by norm_num] at hsecond
    simpa only [mul_pow] using hsecond
  have hraw0 : 0 ≤ levelPairMean (uniformWeight n) (finiteFeature n)
      (fun σ τ=>|orderedOverlap n σ τ-center|^(2*k)) steps 0 x :=
    (p.tree.expect_nonneg (uniformWeight_pos n) (finiteFeature n) ho
      (fun σ=>sq_nonneg (Y (p.spin σ)^k)) x).trans hp
  have hprod := mul_le_mul hsecond' hp
    (p.tree.expect_nonneg (uniformWeight_pos n) (finiteFeature n) ho
      (fun σ=>sq_nonneg (Y (p.spin σ)^k)) x) (Real.sqrt_nonneg _)
  have hfinal := hfirst.trans (Real.sqrt_le_sqrt hprod)
  convert hfinal using 1
  congr 2
  funext σ
  dsimp only [A,D,Y]
  ring

end OAI.SKFluctuations
