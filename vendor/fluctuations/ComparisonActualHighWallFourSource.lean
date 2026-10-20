module

public import ComparisonActualGeneralFourSource
public import ComparisonActualHighWallSourceIdentification

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighWallData
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree Cavity
open scoped BigOperators NNReal
set_option maxHeartbeats 32000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {delta : ℝ} (a : ActualHighWallData (n+1) delta)
  {as : List PositiveMass} {i star U : ℕ}

theorem four_resource_finite_iteration
    (alpha : a.Profile)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length) (ho : MassOrdered 0 as)
    (W : ℝ) (hW : W ≠ 0)
    (hstarK : 0 < nativeContinuumMixedClock n (a.bf alpha) (a.hf alpha) as star)
    (depth : ℕ) :
    ((xs.flatMap (fun Q=>[Q,Q.freeze])).map
      (actualGeneralFourStateResponse (a.bf alpha) (a.hf alpha) U W)).sum=
    actualGeneralFourResidualSum (a.bf alpha) (a.hf alpha) hs hU W depth xs+
    ((actualGeneralFourCenteredForest (a.bf alpha) (a.hf alpha) hs hU W depth xs).map
      (actualGeneralFourStateResponse (a.bf alpha) (a.hf alpha) U W)).sum :=
  actual_general_four_resource_finite_iteration (a.bf alpha) (a.hf alpha)
    (a.bf_monotone alpha) (a.hf_monotone alpha) xs hxs hi hs hU ho W hW hstarK depth

theorem four_denominator_bounds
    (alpha : a.Profile) {W cK : ℝ} (hW : 0<W) (hcK : 0<cK)
    (ho : MassOrdered 0 as) (hs : star<U) (hU : U≤as.length)
    (hstarK : cK*W≤nativeContinuumMixedClock n (a.bf alpha) (a.hf alpha) as star) :
    let K:=nativeContinuumMixedClock n (a.bf alpha) (a.hf alpha) as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    0<chi*K star ∧ chi≤1 ∧ Real.exp (-4*a.T)*cK*W≤chi*K star :=
  actual_general_four_denominator_bounds (a.bf alpha) (a.hf alpha)
    (a.bf_monotone alpha) (a.hf_monotone alpha) (a.total_clock_le alpha)
    hW hcK ho hs hU hstarK

end OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighWallData
