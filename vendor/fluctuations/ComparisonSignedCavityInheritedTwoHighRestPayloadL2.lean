module

public import ComparisonSignedCavityTwoHighRestPayloadL2
public import ComparisonSignedCavityInheritedErrorTransport
public import ComparisonSignedCavityMixedErrorCanonicalLedger

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeRestPayloadHighSecondIntegral (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.cavityLeft.Assignment→ℝ) : ℝ :=
  ∫t in (0:ℝ)..1,(1-t)*cutFrozenLowHighJet n q U b h K T
    (fun σ=>P (T.cavityAssignment σ).1) 0 0 2 t

def nativeInheritedHighSecondL2Price (r : ℕ) (Temp Cf : ℝ) : ℝ :=
  pairForkVariation r*pairForkVariation (r+2)*(2*Temp)*
    Real.exp (wholeLawRowComparisonConstant r*(4*Cf+2*Temp))

theorem nativeInheritedHighSecondL2Price_nonneg (r : ℕ) (Temp Cf : ℝ)
    (hTemp : 0 ≤ Temp) : 0 ≤ nativeInheritedHighSecondL2Price r Temp Cf := by
  unfold nativeInheritedHighSecondL2Price
  exact mul_nonneg (mul_nonneg
    (mul_nonneg (pairForkVariation_nonneg _) (pairForkVariation_nonneg _))
    (mul_nonneg (by norm_num) hTemp)) (Real.exp_pos _).le

theorem actual_minimum_inherited_rest_high_second_integral_L2_bound
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hsource : NativeActualSmallSourceClocks M Temp Cf) (hxs : M.xs ≤ 1)
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
    let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
    |nativeRestPayloadHighSecondIntegral n q U b h K T P| ≤
      nativeInheritedHighSecondL2Price rBound Temp Cf*C*(T.forkCost R+edgeBudget 0 as R) := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let V:=nativeInheritedHighSecondL2Price rBound Temp Cf
  have hV : 0 ≤ V:=nativeInheritedHighSecondL2Price_nonneg rBound Temp Cf hTemp
  have hR j : 0 ≤ R j := by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hcost : 0 ≤ T.forkCost R+edgeBudget 0 as R :=
    add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have HS j : S j∈Icc (0:ℝ) 1:=physicalOrderedPathS_mem_unit n M.bf M.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (partitionPoint_mem as ho j)
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.bf u:ℝ) ≤ M.bf v from toNNReal_monotoneOn had.1 hu hv huv) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>show (M.hf u:ℝ) ≤ M.hf v from toNNReal_monotoneOn had.2.1 hu hv huv) as ho
  have hSm : Monotone S:=comp_partitionPoint_monotone
    (physicalOrderedPathS_monotone_unit n M.bf M.hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)) as ho
  have hK0 j : 0 ≤ K j:=add_nonneg (NNReal.coe_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (HS j).1)
  have hKm : Monotone K:=by
    intro i j hij
    exact add_le_add (hhm hij) (mul_le_mul (hbm hij) (hSm hij) (HS i).1 (NNReal.coe_nonneg _))
  have Hb j : b j ≤ Temp:=(hsource _ (partitionPoint_mem as ho j)).1
  have Hjet t (ht : t∈Icc (0:ℝ) 1) :
      |cutFrozenLowHighJet n q U b h K T (fun σ=>P (T.cavityAssignment σ).1) 0 0 2 t| ≤
        V*C*(T.forkCost R+edgeBudget 0 as R) := by
    let law:=cutFullVariance n q U 0 t b h K
    let A:=cutTSlope n U 0 b h K
    have H:=cutFrozenLowHighJet_two_high_rest_L2_bound n q U b h K T ho P ht
      (fun j i=>by cases i <;> exact NNReal.coe_nonneg _)
      (fun i=>by cases i <;> first | exact hbm | exact hhm)
      (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hK0 hbm hhm hKm hT hC
      (show 0 ≤ 2*Temp by positivity)
      (native_small_source_continuum_square_clock_budget M Temp Cf hCf hsource hxs as ho) hP
      (fun j _ σ τ=>native_centered_high_kernel_abs_le n U b h S
        (fun _=>NNReal.coe_nonneg _) Hb HS j σ τ)
      (nativeWholeLawErrorRadius_nonneg n as law A)
      (fun j=>le_of_eq (nativeWholeLawErrorSecond_eq_radius_sq n ho law A j))
    have Hprofile:=actual_minimum_inherited_current_high_profile_le_original M Temp Cf
      hTemp hCf hsource hxs T ho U (l:=0) (t:=t) (by norm_num) ht (e:=1) (by norm_num)
    dsimp only at Hprofile
    rw [nativeWholeLawProfileCost_eq_budget n ho] at Hprofile
    simp only [Real.rpow_one] at Hprofile
    have Hprice : pairForkVariation rBound*pairForkVariation (rBound+2)*(2*Temp)*
        (Real.exp (wholeLawRowComparisonConstant rBound*(4*Cf+2*Temp))*C)=V*C := by
      dsimp only [V,nativeInheritedHighSecondL2Price]
      ring
    rw [Hprice] at H
    exact H.trans (mul_le_mul_of_nonneg_left Hprofile (mul_nonneg hV hC))
  have H:=weighted_unit_integral_abs_le (mul_nonneg (mul_nonneg hV hC) hcost) Hjet 1
  simpa only [pow_one,nativeRestPayloadHighSecondIntegral,V,q,K,b,h,S,R] using H

end OAI.SKFluctuations.Cavity
