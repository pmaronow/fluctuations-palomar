module

-- Modified for this distribution (2026): module/header visibility port only;
-- existing proof text preserved.

public import OAI.Probability.SKBarriers.Replicas.MatrixChain
public import OAI.Probability.SKBarriers.Scalar.ScalarGeneralTerminal
public import SKOptimized.OvershootAlgebra

@[expose] public section

/-! Frozen finite overshoot window from `LEAD_DESIGN.md` §§A–B.

The five manuscript stages are common, shared, singleton I, singleton II, and repair.
Each scalar interval uses `N` left-endpoint substeps. Simultaneous rank-one directions
are adjacent at the same mass, rather than being concatenated as separate time intervals.
An independent padding interval ends at the fixed time `T* = s + 4*h`.

Upstream conventions: `vectorIncrementChain` is ordered outer to inner; its masses are
unscaled real numbers, while its vectors carry the factor `β`. `matrixChainPenalty` uses
the unscaled vectors and an initial covariance matrix. Bounds on masses, their ordering,
and nonnegative durations are hypotheses for later comparison theorems, not restrictions
on these total definitions. The intended range is `0 < p ≤ 1/2`, `h ≥ 0`, `|k| ≤ 1/2`,
and `0 ≤ s ≤ s + 4*h ≤ 1`, with an increasing `[0,1]`-valued profile and the stage mass
separation specified in manuscript lines 566–568.

The repair vectors use the packet's `rampVector p 0`, `sharedVector p 0`, and `contrast`;
their outer products sum to its `repairMatrix`. The repair length uses the packet's
`varianceCoefficient`. No all-lean library is imported.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set
open OAI.SK.Analytic

namespace SKBarriers2.OW

/-- The positive covariance path of `StrengthenedSKBarriers.tex`, lines 542–595:
five relative-grid stages and independent padding from `T` to `T* = s + 4*h`.
There are `12*N` rank-one steps: `N + N + N + 3*N + 3*N + 3*N`. -/
def window (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ) : List (ℝ × (Fin 3 → ℝ)) :=
  let grid := fun (a len c : ℝ) (vs : List (Fin 3 → ℝ)) =>
    (List.range N).flatMap fun j =>
      vs.map fun v =>
        (α (s + h * (a + len * (j : ℝ) / (N : ℝ))) / c,
          Real.sqrt (h * len / (N : ℝ)) • v)
  let repairLen := 4 * k ^ 2 * SKOptimized.Overshoot.varianceCoefficient p
  -- Repair entries are `k * √(4 h L / N) • w` (math memo `S3_OVERSHOOT_MEMO.md` §1): equal to the
  -- `√(ℓ/N) • w` form with `ℓ = 4 h k² L` up to the sign symmetry `g ↦ -g`, but polynomial in `k`.
  let repairGrid := fun (vs : List (Fin 3 → ℝ)) =>
    (List.range N).flatMap fun j =>
      vs.map fun v =>
        (α (s + h * (2 + repairLen * (j : ℝ) / (N : ℝ))) / 1,
          (k * Real.sqrt (h * (4 * SKOptimized.Overshoot.varianceCoefficient p) / (N : ℝ))) • v)
  grid 0 1 3 [SKOptimized.Overshoot.commonVector p k] ++
    grid 1 p 2 [SKOptimized.Overshoot.sharedVector p k] ++
    grid 1 p 1 [SKOptimized.Overshoot.rampVector p k] ++
    grid (1 + p) (1 - p) 1
      [SKOptimized.Overshoot.rampVector p k, SKOptimized.Overshoot.postXVector p k,
        SKOptimized.Overshoot.postYVector p k] ++
    repairGrid
      [SKOptimized.Overshoot.rampVector p 0,
        (1 / Real.sqrt 2) • SKOptimized.Overshoot.sharedVector p 0,
        (1 / 2 : ℝ) • SKOptimized.Overshoot.contrast] ++
    grid (2 + repairLen) (2 - repairLen) 1
      [Pi.single 0 1, Pi.single 1 1, Pi.single 2 1]

/-- The diagonal local boundary `B(s,h,k,z)` of `StrengthenedSKBarriers.tex`,
lines 634–638, with the independent tail split at the fixed time `s + 4*h`
as in lines 613–616. The terminal below is definitionally `∑ i, Phi β α (s+4*h) (x i)`. -/
def boundary (β : ℝ) (α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  vectorIncrementChain ((window α p s h k N).map (fun step => (step.1, β • step.2)))
    (fun x => ∑ i : Fin 3,
      scalarCDFOperator β α (s + 4 * h) (Real.toNNReal (1 - (s + 4 * h)))
        scalarSpinTerminal (x i))
    (fun _ => z)

/-- The full squared-covariance penalty `∫ m d‖Q‖²` of
`StrengthenedSKBarriers.tex`, lines 597–607: common prefix, exact finite window,
and independent tail. The prefix uses `γ/3`; window and tail use `α`. -/
def penalty (γ α : ℝ → ℝ) (p s h k : ℝ) (N : ℕ) : ℝ :=
  6 * (∫ t in Icc (0 : ℝ) s, t * γ t) +
    matrixChainPenalty (window α p s h k N) (fun _ _ => s) +
    6 * (∫ t in Icc (s + 4 * h) 1, t * α t)

/-- The trial `T(s,h,k)` of `StrengthenedSKBarriers.tex`, lines 597–612,
in the local-gap coordinates `p=1/2`, `s=r-2d`, `h=2d`, `k=δ/(2d)`
(lines 534–536), allowing the prefix profile `γ` used in lines 1196–1207. -/
def trialValue (β : ℝ) (γ α : ℝ → ℝ) (r d δ : ℝ) (N : ℕ) : ℝ :=
  scalarCDFOperator β (fun t => γ t / 3) 0 (Real.toNNReal (r - 2 * d))
    (boundary β α (1 / 2) (r - 2 * d) (2 * d) (δ / (2 * d)) N) 0 -
    β ^ 2 / 4 * penalty γ α (1 / 2) (r - 2 * d) (2 * d) (δ / (2 * d)) N

end SKBarriers2.OW
