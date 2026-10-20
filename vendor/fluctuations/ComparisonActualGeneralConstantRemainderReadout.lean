module

public import ComparisonActualGeneralConstantJointFourIteration
public import ComparisonActualGeneralTargetMeanReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem actual_general_constant_source_remainder_eq_original_mean_and_Taylor
    {n : ℕ} (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (star U : ℕ) (hs : star<U) (hU : U≤as.length) :
    actualGeneralConstantSourceRemainder (n:=n) bf hf as star U=
      actualGeneralTargetOriginalMeanCorrection (n:=n) bf hf as star U+
      (finitePhysicalMean (n+1) as (fun j=>(bf (partitionPoint 0 as j):ℝ))
        (fun j=>(hf (partitionPoint 0 as j):ℝ)) star-nativePhysicalResourceCenter n bf hf as star)+
      actualGeneralTargetOriginalTaylorPart (n:=n) bf hf as star U := by
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let C:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let T:=single (S:=Spin n×Bool) as
  let s:=singleSlot (S:=Spin n×Bool) as
  let g:=nativeFreshAtSlot T 0 s star
  have hbm : Monotone b:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (hbf hu hv huv)) as ho
  have hhm : Monotone h:=comp_partitionPoint_monotone
    (fun u hu v hv huv=>NNReal.coe_le_coe.mpr (hhf hu hv huv)) as ho
  have HK:=native_continuum_mixed_clock_nonneg n bf hf hbf hhf as ho
  have HKm:=native_continuum_mixed_clock_monotone n bf hf hbf hhf as ho
  have HKC:=native_continuum_mixed_clock_eq_original_center n bf hf hbf hhf as ho
  have H:=native_original_forward_longitudinal_joint_restoration n q U b h K C HKC g.tree ho
    (fun _=>1) (g.embed s) g.mark hU
    (by intro j z;cases z <;> exact NNReal.coe_nonneg _)
    (by intro z;cases z <;> first | exact hbm | exact hhm)
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) HK hbm hhm HKm
  dsimp only at H
  have Hsplit : g.tree.splitIndex (g.embed s) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,Nat.min_eq_left (hs.le.trans hU)]
  rw [Hsplit] at H
  have HQ : cutFullVariance n q U 1 1 b h K=finitePhysicalCavitySquareVariance n U as b h 1 1:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h K (finitePhysicalMixedClock (n+1) as b h)
  rw [HQ] at H
  unfold actualGeneralConstantSourceRemainder actualGeneralTargetOriginalMeanCorrection
    actualGeneralTargetOriginalConstantPart actualGeneralTargetOriginalTaylorPart
  dsimp only
  dsimp only [b,h,K,C,q,T,s,g] at H
  linear_combination -H

end OAI.SKFluctuations.Cavity
