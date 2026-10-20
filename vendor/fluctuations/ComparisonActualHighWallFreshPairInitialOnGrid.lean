module

public import ComparisonActualHighWallFreshPairForestOnGrid

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_high_wall_initial_fresh_pair_forest_abs_le_on_grid
    {n degree : ℕ} {m delta cl cu Az C0 Ct D Bclock A saving Cmass cK : ℝ}
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {u : PositiveMass} {as : List PositiveMass}
    (H : ActualHighWallSquareResourcePairBudgetsOnGrid degree A saving Cmass M u as)
    (hA : 1≤A) (ho : MassOrdered 0 as)
    {i U : ℕ} (hi : i≤retainedMassPrefixIndex u.val as)
    (hs : retainedMassPrefixIndex u.val as<U) (hU : U≤as.length)
    (hcK : 0<cK)
    (hstarK : cK*M.data.d≤nativeContinuumMixedClock n M.bf M.hf as
      (retainedMassPrefixIndex u.val as))
    (depth : ℕ) (hdegree : 1+depth≤degree)
    (seedMass : ℝ) (hmass : partitionPoint 0 as i≤Cmass*M.data.d) :
    let epsilon:=((n+1:ℕ):ℝ)^(-saving)
    |actualGeneralFourPairSum M.bf M.hf U M.data.d
      (actualGeneralFourCenteredForest M.bf M.hf hs hU M.data.d depth
        [nativeActualInitialState (S:=Spin n×Bool) as i (retainedMassPrefixIndex u.val as) seedMass
          (hi.trans (hs.le.trans hU))])| ≤
      6*nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
        (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 depth*A^(depth+2)*
        epsilon^(depth+1)*M.data.d^2 := by
  dsimp only
  let root:=nativeActualInitialState (S:=Spin n×Bool) as i (retainedMassPrefixIndex u.val as)
    seedMass (hi.trans (hs.le.trans hU))
  have HV : NativeActualResourceGenerated i (retainedMassPrefixIndex u.val as) U [.initial]
      root.generation root.tree root.term:=
    .physical (.seed as hU seedMass .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
  have HH:=actual_high_wall_four_fresh_pair_forest_abs_le_on_grid H (by omega) hA ho
    (seed:=[.initial]) (Or.inr rfl) hs hU hcK hstarK depth 2 0 [root]
    (by intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact HV)
    (by intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;rfl)
    (by intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact nativeActualInitialState_leaves_le _ _ _ _ _)
    (by simpa only [List.length_singleton,add_zero] using hdegree) hi hmass
  convert HH using 1
  simp only [nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    List.sum_cons,List.sum_nil,add_zero,List.length_singleton,NativeResourceMark.savedScale,
    root,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,mul_one]
  ring

end OAI.SKFluctuations.Cavity
