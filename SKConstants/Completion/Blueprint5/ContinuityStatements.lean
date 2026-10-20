module

public import SKConstants.Completion.N19n.PrimitiveInputs

@[expose] public section
noncomputable section
open Filter
open scoped NNReal Topology Matrix.Norms.L2Operator
namespace SKConstants.Completion.Blueprint5
open GaussianProposal Blueprint Blueprint4 N19 N19n
set_option autoImplicit false

def CoarseDPathBoundsStatement : Prop :=
  ∀ (p : Parameters), FineExponents p → ∀ hb : CoarseCommon p, 0 ≤ p.D →
    ∀ (CB CD : ℝ), 0 < CB → 0 < CD →
    ∃ u : ℝ, 0 < u ∧ ∀ᶠ n : ℕ in atTop, ∀ (θ φ : ℝ)
      (z : Outer n × Internal p n), z ∈ experimentCap p n CB CD n →
      ∀ i, ‖(coarseReplayAux p n hb.2.1.le (angleAux p n θ z.2)).2.2 i -
        (coarseReplayAux p n hb.2.1.le (angleAux p n φ z.2)).2.2 i‖ ≤
          (n : ℝ)^u*|θ-φ|

def CoarseStartGapBoundsStatement : Prop :=
  ∀ (p : Parameters), FineExponents p → ∀ hb : CoarseCommon p, 0 ≤ p.D →
    ∀ (CB CD : ℝ), 0 < CB → 0 < CD →
    ∃ u : ℝ, 0 < u ∧ ∀ᶠ n : ℕ in atTop, ∀ (θ φ : ℝ)
      (z : Outer n × Internal p n), z ∈ experimentCap p n CB CD n →
      scalarMeshPathGap
          (replayStart (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)
            (coarseReplayAux p n hb.2.1.le (angleAux p n θ z.2)))
          (replayStart (meshSize p.a n) (rankCount p.a p.b n) (queryCount p.a p.b n)
            (coarseReplayAux p n hb.2.1.le (angleAux p n φ z.2))) ≤
        (n : ℝ)^u*|θ-φ|

def CoarseBridgeBoundsStatement : Prop :=
  ∀ (p : Parameters), FineExponents p → ∀ hb : CoarseCommon p, 0 ≤ p.D →
    ∀ (CB CD : ℝ), 0 < CB → 0 < CD →
    ∃ u : ℝ, 0 < u ∧ ∀ᶠ n : ℕ in atTop, ∀ (θ φ : ℝ)
      (z : Outer n × Internal p n), z ∈ experimentCap p n CB CD n →
      ∀ j : Fin (queryCount p.a p.b n),
        (∑ i, ‖(coarseReplayAux p n hb.2.1.le (angleAux p n θ z.2)).1.2 (j.val+1) i -
          (coarseReplayAux p n hb.2.1.le (angleAux p n φ z.2)).1.2 (j.val+1) i‖) ≤
          (n : ℝ)^u*|θ-φ|

def CoarseMatrixBoundsStatement : Prop :=
  ∀ (p : Parameters), FineExponents p → ∀ _hb : CoarseCommon p, 0 ≤ p.D →
    ∀ (CB CD : ℝ), 0 < CB → 0 < CD →
    ∃ u : ℝ, 0 < u ∧ ∀ᶠ n : ℕ in atTop, ∀ (θ φ : ℝ)
      (z : Outer n × Internal p n), z ∈ experimentCap p n CB CD n →
      ‖coarseReplayMatrix p n (angleMatrix p n θ z.1 z.2) -
          coarseReplayMatrix p n (angleMatrix p n φ z.1 z.2)‖ ≤ (n : ℝ)^u*|θ-φ| ∧
      ‖coarseReplayMatrix p n (angleMatrix p n φ z.1 z.2)‖ ≤ (n : ℝ)^u

def CoarseCompletionBoundsStatement : Prop :=
  ∀ (p : Parameters), FineExponents p → ∀ hb : CoarseCommon p, 0 ≤ p.D →
    ∀ (CB CD : ℝ), 0 < CB → 0 < CD →
    ∃ u : ℝ, 0 < u ∧ ∀ᶠ n : ℕ in atTop, ∀ (θ φ : ℝ)
      (z : Outer n × Internal p n), z ∈ experimentCap p n CB CD n →
      (∀ j : Fin (queryCount p.a p.b n), ‖WithLp.toLp 2 (fun i =>
        paperNoiseTrace (rankCount p.a p.b n + queryCount p.a p.b n) (queryCount p.a p.b n)
          (paperCompletionReplayNoise (rankCount p.a p.b n + queryCount p.a p.b n)
            (queryCount p.a p.b n)
            (coarseReplayAux p n hb.2.1.le (angleAux p n θ z.2)).2.1) j (.inl i))‖ ≤
          (n : ℝ)^u) ∧
      (∀ j : Fin (queryCount p.a p.b n), ‖WithLp.toLp 2 (fun i =>
        paperNoiseTrace (rankCount p.a p.b n + queryCount p.a p.b n) (queryCount p.a p.b n)
          (paperCompletionReplayNoise (rankCount p.a p.b n + queryCount p.a p.b n)
            (queryCount p.a p.b n)
            (coarseReplayAux p n hb.2.1.le (angleAux p n θ z.2)).2.1) j (.inl i) -
        paperNoiseTrace (rankCount p.a p.b n + queryCount p.a p.b n) (queryCount p.a p.b n)
          (paperCompletionReplayNoise (rankCount p.a p.b n + queryCount p.a p.b n)
            (queryCount p.a p.b n)
            (coarseReplayAux p n hb.2.1.le (angleAux p n φ z.2)).2.1) j (.inl i))‖ ≤
          (n : ℝ)^u*|θ-φ|)

end SKConstants.Completion.Blueprint5
