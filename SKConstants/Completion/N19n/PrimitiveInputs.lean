module

public import SKConstants.Completion.N19n.CoarseReplay
public import SKConstants.Completion.Blueprint4.NodesAt

@[expose] public section
noncomputable section
open Filter
open scoped NNReal Topology Matrix.Norms.L2Operator
namespace SKConstants.Completion.N19n
open GaussianProposal Blueprint Blueprint4 N19
set_option autoImplicit false

def ReplayPrimitiveBounds (δ : ℝ≥0) (r q : ℕ) (a b : ReplayAux δ r q)
    (M M' : Matrix (Fin (r+q)) (Fin (r+q)) ℝ) (η A : ℝ) : Prop :=
  (∀ i, ‖a.2.2 i-b.2.2 i‖ ≤ η) ∧
  scalarMeshPathGap (replayStart δ r q a) (replayStart δ r q b) ≤ η ∧
  (∀ j : Fin q, (∑ i, ‖a.1.2 (j.val+1) i-b.1.2 (j.val+1) i‖) ≤ η) ∧
  ‖M-M'‖ ≤ η ∧ ‖M'‖ ≤ A ∧
  (∀ j : Fin q, ‖WithLp.toLp 2 (fun i => paperNoiseTrace (r+q) q
    (paperCompletionReplayNoise (r+q) q a.2.1) j (.inl i))‖ ≤ A) ∧
  (∀ j : Fin q, ‖WithLp.toLp 2 (fun i =>
    paperNoiseTrace (r+q) q (paperCompletionReplayNoise (r+q) q a.2.1) j (.inl i) -
    paperNoiseTrace (r+q) q (paperCompletionReplayNoise (r+q) q b.2.1) j (.inl i))‖ ≤ η)

def CoarsePrimitiveInputBoundsStatement : Prop :=
  ∀ (p : Parameters), FineExponents p → ∀ hb : CoarseCommon p, 0 ≤ p.D →
    ∀ (CB CD : ℝ), 0 < CB → 0 < CD →
    ∃ u : ℝ, 0 < u ∧ ∀ᶠ n : ℕ in atTop, ∀ (θ φ : ℝ)
      (z : Outer n × Internal p n), z ∈ experimentCap p n CB CD n →
      ReplayPrimitiveBounds (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)
        (coarseReplayAux p n hb.2.1.le (angleAux p n θ z.2))
        (coarseReplayAux p n hb.2.1.le (angleAux p n φ z.2))
        (coarseReplayMatrix p n (angleMatrix p n θ z.1 z.2))
        (coarseReplayMatrix p n (angleMatrix p n φ z.1 z.2))
        ((n : ℝ)^u*|θ-φ|) ((n : ℝ)^u)

end SKConstants.Completion.N19n
