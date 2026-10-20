module

public import ComparisonActualHighWallFreshPairForestOnGrid

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_high_wall_constant_children_fresh_pair_forest_abs_le_on_grid
    {n degree : ℕ} {m delta cl cu Az C0 Ct D Bclock A saving Cmass cK : ℝ}
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {u : PositiveMass} {as : List PositiveMass}
    (H : ActualHighWallSquareResourcePairBudgetsOnGrid degree A saving Cmass M u as)
    (hA : 1≤A) (ho : MassOrdered 0 as) (hCm : 0≤Cmass)
    {U : ℕ} (hs : retainedMassPrefixIndex u.val as<U) (hU : U≤as.length)
    (hcK : 0<cK)
    (hstarK : cK*M.data.d≤nativeContinuumMixedClock n M.bf M.hf as
      (retainedMassPrefixIndex u.val as))
    (depth : ℕ) (hdegree : 1+depth≤degree) :
    let epsilon:=((n+1:ℕ):ℝ)^(-saving)
    |actualGeneralFourPairSum M.bf M.hf U M.data.d
      (actualGeneralFourCenteredForest M.bf M.hf hs hU M.data.d depth
        (actualGeneralConstantSourceChildren (n:=n) M.bf M.hf as
          (retainedMassPrefixIndex u.val as) U hs hU))| ≤
      36*nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
        (Bclock/(Real.exp (-4*Bclock)*cK)) 3 3 depth*A^(depth+2)*
        epsilon^(depth+2)*M.data.d := by
  dsimp only
  let roots:=actualGeneralConstantSourceChildren (n:=n) M.bf M.hf as
    (retainedMassPrefixIndex u.val as) U hs hU
  have HH:=actual_high_wall_four_fresh_pair_forest_abs_le_on_grid H (by omega) hA ho
    (seed:=[]) (Or.inl rfl) hs hU hcK hstarK depth 3 1 roots
    (fun Q hQ=>actualGeneralConstantSourceChildren_valid M.bf M.hf hs hU Q hQ)
    (fun Q hQ=>actualGeneralConstantSourceChildren_generation M.bf M.hf hs hU Q hQ)
    (fun Q hQ=>actualGeneralConstantSourceChildren_leaves M.bf M.hf hs hU Q hQ)
    (by simpa only [List.length_nil,zero_add] using hdegree) (Nat.zero_le _)
    (by simpa only [partitionPoint,partitionValues_zero,id_eq] using mul_nonneg hCm M.data.hd.le)
  have HC:=actualGeneralConstantSourceChildren_coefficient_variation (n:=n) M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) ho hs hU
  have hBc : 0≤Bclock:=M.data.hTpos.le.trans M.hT
  have hV:=nativeActualWeightedFrontierCost_nonneg nativeActualOriginalFourGCenteredBranches
    (show 0≤Bclock/(Real.exp (-4*Bclock)*cK) from by positivity) 3 3 depth
  have hdpos : 0<M.data.d:=M.data.hd
  apply HH.trans
  have HB:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left HC (mul_nonneg (by norm_num : (0:ℝ)≤2) hV))
    (show 0≤3*A^(depth+2)*(((n+1:ℕ):ℝ)^(-saving))^(depth+2)*M.data.d from by positivity)
  convert HB using 1 <;>
    (try dsimp only [roots]) <;>
    (try simp only [nativeResourceScale,List.map_nil,List.prod_nil,List.length_nil,zero_add,
      Nat.add_comm,Nat.add_left_comm]) <;> ring

end OAI.SKFluctuations.Cavity
