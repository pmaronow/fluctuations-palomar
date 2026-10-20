module

public import ComparisonSignedCavityInheritedTwoHighRestPayloadL2
public import ComparisonActualHighWallSourceClockBudget
public import ComparisonActualHighWallHighProfile

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def actualHighWallHighSecondL2Price (r : ℕ) (Bclock : ℝ) : ℝ:=
  pairForkVariation r*pairForkVariation (r+2)*(2*max Bclock 0)*
    Real.exp (wholeLawRowComparisonConstant r*(2*max Bclock 0))

theorem actualHighWallHighSecondL2Price_nonneg (r : ℕ) (Bclock : ℝ) :
    0 ≤ actualHighWallHighSecondL2Price r Bclock:=by
  dsimp only [actualHighWallHighSecondL2Price]
  have H1:=pairForkVariation_nonneg r
  have H2:=pairForkVariation_nonneg (r+2)
  positivity

theorem actual_high_wall_rest_high_second_integral_L2_bound
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (U rBound : ℕ) (hT : T.leaves ≤ rBound) (P : T.cavityLeft.Assignment→ℝ)
    {C : ℝ} (hC : 0 ≤ C)
    (hP : T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0
      (fun j=>Sum.elim (fun _=>(M.bf (partitionPoint 0 as j):ℝ))
        (fun _=>(M.hf (partitionPoint 0 as j):ℝ))) (fun σ=>P σ^2) 0 ≤ C^2) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
    let q:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    let R:=M.data.highErrorEnvelope M.alpha as U
    |nativeRestPayloadHighSecondIntegral n q U b h K T P| ≤
      actualHighWallHighSecondL2Price rBound Bclock*C*(T.forkCost R+edgeBudget 0 as R) := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=M.data.highErrorEnvelope M.alpha as U
  let V:=actualHighWallHighSecondL2Price rBound Bclock
  have hV : 0 ≤ V:=actualHighWallHighSecondL2Price_nonneg rBound Bclock
  have hR j : 0 ≤ R j := by
    dsimp only [R,ActualHighWallData.highErrorEnvelope,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ M.data.hTpos.le)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hcost : 0 ≤ T.forkCost R+edgeBudget 0 as R :=
    add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from M.data.bf_monotone M.alpha hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from M.data.hf_monotone M.alpha hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf
      (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have HT:=M.hT.trans (le_max_left Bclock 0)
  have Hb j : b j ≤ max Bclock 0:=by
    have HS:=M.data.total_clock_le M.alpha _ (partitionPoint_mem as ho j)
    have HH:=(M.hf (partitionPoint 0 as j)).coe_nonneg
    dsimp only [b]
    linarith
  have Hclock : K as.length+b as.length+h as.length ≤ 2*max Bclock 0:=by
    have HH:=M.data.total_clock_le M.alpha _ (partitionPoint_mem as ho as.length)
    have HM:=mul_le_mul_of_nonneg_left (HS as.length).2
      (M.bf (partitionPoint 0 as as.length)).coe_nonneg
    dsimp only [K,b,h,S]
    nlinarith only [HH,HM,HT]

  have Hjet t (ht : t∈Icc (0:ℝ) 1) :
      |cutFrozenLowHighJet n q U b h K T (fun σ=>P (T.cavityAssignment σ).1) 0 0 2 t| ≤
        V*C*(T.forkCost R+edgeBudget 0 as R) := by
    let law:=cutFullVariance n q U 0 t b h K
    let A:=cutTSlope n U 0 b h K
    have H:=cutFrozenLowHighJet_two_high_rest_L2_bound n q U b h K T ho P ht
      (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
      (fun i=>by cases i <;> first | exact hbm | exact hhm)
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm hT hC
      (show 0 ≤ 2*max Bclock 0 by positivity)
      Hclock hP
      (fun j _ σ τ=>native_centered_high_kernel_abs_le n U b h S
        (fun _=>NNReal.coe_nonneg _) Hb HS j σ τ)
      (nativeWholeLawErrorRadius_nonneg n as law A)
      (fun j=>le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law A j))
    have Hprofile:=M.data.current_high_profile_le_original M.alpha T ho U
      (l:=0) (t:=t) (by norm_num) ht (exponent:=1) (by norm_num)
    dsimp only at Hprofile
    rw [nativeWholeLawProfileCost_eq_budget n ho] at Hprofile
    simp only [Real.rpow_one] at Hprofile
    have Hprice : pairForkVariation rBound*pairForkVariation (rBound+2)*(2*max Bclock 0)*
        (Real.exp (wholeLawRowComparisonConstant rBound*(2*max Bclock 0))*C)=V*C := by
      dsimp only [V,actualHighWallHighSecondL2Price]
      ring
    rw [Hprice] at H
    exact H.trans (mul_le_mul_of_nonneg_left Hprofile (mul_nonneg hV hC))
  have H:=weighted_unit_integral_abs_le (mul_nonneg (mul_nonneg hV hC) hcost) Hjet 1
  simpa only [pow_one,nativeRestPayloadHighSecondIntegral,V,q,K,b,h,S,R] using H

end OAI.SKFluctuations.Cavity
