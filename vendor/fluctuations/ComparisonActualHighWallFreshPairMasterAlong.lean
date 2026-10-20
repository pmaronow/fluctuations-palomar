module

public import ComparisonActualHighWallFreshPairRootsOnGrid
public import ComparisonActualHighWallFreshPairInitialOnGrid
public import ComparisonActualHighWallSquarePairAtWindowAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

def ActualHighWallFreshPairForestBudgetsOnGrid
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (depth : ℕ) (A saving Cmass cK : ℝ)
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (u : PositiveMass) (as : List PositiveMass) : Prop :=
  ActualHighWallSquareResourcePairBudgetsOnGrid (1+depth) A saving Cmass M u as ∧
    ∀level : ℕ,level ≤ depth → ∀_ho : MassOrdered 0 as,
    ∀(U : ℕ) (hs : retainedMassPrefixIndex u.val as < U) (hU : U ≤ as.length),
      cK*M.data.d ≤ nativeContinuumMixedClock n M.bf M.hf as (retainedMassPrefixIndex u.val as) →
    let epsilon:=((n+1:ℕ):ℝ)^(-saving)
    (|actualGeneralFourPairSum M.bf M.hf U M.data.d
      (actualGeneralFourCenteredForest (n:=n) M.bf M.hf hs hU M.data.d level
        (actualGeneralConstantSourceChildren (n:=n) M.bf M.hf as
          (retainedMassPrefixIndex u.val as) U hs hU))| ≤
      36*nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
        (Bclock/(Real.exp (-4*Bclock)*cK)) 3 3 level*A^(level+2)*epsilon^(level+2)*M.data.d) ∧
    ∀(i : ℕ) (hi : i ≤ retainedMassPrefixIndex u.val as),
      partitionPoint 0 as i ≤ Cmass*M.data.d → ∀seedMass : ℝ,
    |actualGeneralFourPairSum M.bf M.hf U M.data.d
      (actualGeneralFourCenteredForest (n:=n) M.bf M.hf hs hU M.data.d level
        [nativeActualInitialState (S:=Spin n×Bool) as i (retainedMassPrefixIndex u.val as)
          seedMass (hi.trans (hs.le.trans hU))])| ≤
      6*nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
        (Bclock/(Real.exp (-4*Bclock)*cK)) 3 2 level*A^(level+2)*epsilon^(level+1)*M.data.d^2

theorem actual_high_wall_fresh_pair_forest_budgets_of_pair_grid
    {n depth : ℕ} {m delta cl cu Az C0 Ct D Bclock A saving Cmass cK : ℝ}
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {u : PositiveMass} {as : List PositiveMass}
    (H : ActualHighWallSquareResourcePairBudgetsOnGrid (1+depth) A saving Cmass M u as)
    (hA : 1 ≤ A) (hCm : 0 ≤ Cmass) (hcK : 0 < cK) :
    ActualHighWallFreshPairForestBudgetsOnGrid depth A saving Cmass cK M u as := by
  refine ⟨H,?_⟩
  intro level hlevel ho U hs hU hK
  exact ⟨actual_high_wall_constant_children_fresh_pair_forest_abs_le_on_grid
      H hA ho hCm hs hU hcK hK level (by omega),
    fun i hi hmass seedMass=>actual_high_wall_initial_fresh_pair_forest_abs_le_on_grid
      H hA ho hi hs hU hcK hK level (by omega) seedMass hmass⟩

theorem actual_high_wall_fresh_pair_master_at_calibrated_star_along
    {m delta cl cu Az C0 Ct D Bclock L cK : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hL : 0 < L) (Cmass : ℝ) (hCm : 0 ≤ Cmass) (hcK : 0 < cK)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hdlim : Tendsto (fun n=>(M n).data.d) atTop (𝓝 0))
    (Cs : ℝ) (hCs : 0 < Cs) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow
      (M n) ((M n).data.d) L Cs (w n))
    (depth : ℕ) :
    ∃A : ℝ,1 ≤ A ∧ ∀ᶠn in atTop,
      ∀Lnet : ℕ,((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀extra : List PositiveMass,(∀u∈extra,u.val ≤ 1) →
      ∃us : List PositiveMass,(∀u∈us,u.val ≤ 1) ∧ (∀u∈extra,u∈us) ∧
        (∀u∈uniformMasses Lnet,u∈us) ∧ (w n).star∈us ∧
        ∀ᶠjGrid in atTop,ActualHighWallFreshPairForestBudgetsOnGrid depth A
          (actualSlowWindowExponent m delta/128) Cmass cK (M n) (w n).star (finiteCutMasses us jGrid) := by
  obtain ⟨A,hA,HA⟩:=actual_high_wall_square_pair_budgets_at_calibrated_star_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hL Cmass hCm dim hdim M hfixed hdlim Cs hCs w hw
    (1+depth) (by omega)
  refine ⟨A,hA,?_⟩
  filter_upwards [HA] with n hn
  intro Lnet hmesh extra hextra
  obtain ⟨us,hus,hret,huniform,hstar,Hgrid⟩:=hn Lnet hmesh extra hextra
  refine ⟨us,hus,hret,huniform,hstar,?_⟩
  filter_upwards [Hgrid] with jGrid hj
  exact actual_high_wall_fresh_pair_forest_budgets_of_pair_grid hj hA hCm hcK

end OAI.SKFluctuations.Cavity
