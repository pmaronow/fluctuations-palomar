module

public import ComparisonSignedCavityRetainedPairedHighBudget
public import ComparisonActualHighWallHighProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped NNReal

theorem actual_high_wall_retained_first_high_rest_L2_bound
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U rBound : ℕ) (hT : T.leaves ≤ rBound) (P : T.cavityLeft.Assignment → ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hP : T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0
      (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun _=>(M.hf (partitionPoint 0 as j):ℝ))) (fun σ=>P σ^2) 0 ≤ C^2) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let R:=M.data.highErrorEnvelope M.alpha as U
    |retainedSignedJets n q U b h K [restHighKernel n U b h K] T P []| ≤
      pairForkVariation rBound*C*(T.forkCost R+edgeBudget 0 as R) := by
  dsimp only
  apply (native_retained_first_high_rest_L2_bound n U rBound _ _ _ _ T ho hT P hC hP).trans
  have HE:=M.data.current_high_profile_le_original M.alpha T ho U
    (l:=0) (t:=0) (by norm_num) (by norm_num) (exponent:=1) (by norm_num)
  simp only [Real.rpow_one] at HE
  exact mul_le_mul_of_nonneg_left HE (mul_nonneg (pairForkVariation_nonneg _) hC)

end OAI.SKFluctuations.Cavity
