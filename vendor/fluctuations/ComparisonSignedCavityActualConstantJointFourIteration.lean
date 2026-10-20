module

public import ComparisonSignedCavityActualConstantJointFourReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {star U : ℕ}

def nativeActualMinimumConstantJointSource
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (star U : ℕ) : ℝ :=
  nativeActualConstantJointStarSource n as star U
    (fun j=>(M.bf (partitionPoint 0 as j):ℝ)) (fun j=>(M.hf (partitionPoint 0 as j):ℝ))
    (nativeContinuumMixedClock n M.bf M.hf as) (nativePhysicalResourceCenter n M.bf M.hf as)

def nativeActualConstantSourceRemainder
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (star U : ℕ) : ℝ :=
  let T:=ClockTree.single (S:=Spin n×Bool) as
  let s:=singleSlot as
  let g:=nativeFreshAtSlot T 0 s star
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let S:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  chi*K star*(nativeRetainedLongitudinalPairing n q U b h K g.tree (fun _=>1) (g.embed s)+
    nativeRetainedLongitudinalPairing n q U b h K g.tree (fun _=>1) g.mark)+
  chi^2*b star*(finitePhysicalMean (n+1) as b h star-
    finitePhysicalMean (n+1) as b h star/(n+1:ℕ)-S star)+
  nativeActualJointRestoredForwardTaylorError n q U b h K S g.tree (fun _=>1) (g.embed s) g.mark

def nativeActualConstantSourceFrozenCorrection
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (star U : ℕ) (hs : star<U) (hU : U≤as.length) (W : ℝ) : ℝ :=
  nativeActualConstantSourceRemainder M as star U-
    (M.bf (partitionPoint 0 as star):ℝ)*W*
      ((nativeActualConstantSourceChildren M as star U hs hU).map
        (fun Q=>nativeActualMinimumFourStateResponse M U W Q.freeze)).sum

theorem actual_minimum_constant_joint_source_eq_children_and_remainder
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (W : ℝ) (hW : W≠0)
    (star U : ℕ) (hs : star<U) (hU : U≤as.length) :
    nativeActualMinimumConstantJointSource M as star U=
      (M.bf (partitionPoint 0 as star):ℝ)*W*
        ((nativeActualConstantSourceChildren M as star U hs hU).map
          (nativeActualMinimumFourStateResponse M U W)).sum+
      nativeActualConstantSourceRemainder M as star U := by
  have H:=actual_minimum_constant_source_children_response M as ho W hW star U hs hU
  dsimp only at H
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let S:=nativePhysicalResourceCenter n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have Hq : finitePhysicalCavitySquareVariance n U as b h 1 1=
      cutFullVariance n q U 1 1 b h K:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h _ K
  change _+nativeOriginalFreshPartnerLResponse n 0 (finitePhysicalCavitySquareVariance n U as b h 1 1)
    0 U K b S _ _ star _= _ at H
  rw [Hq] at H
  unfold nativeActualMinimumConstantJointSource nativeActualConstantJointStarSource
    nativeActualConstantSourceRemainder
  dsimp only
  linear_combination (M.bf (partitionPoint 0 as star):ℝ)*H

theorem actual_minimum_constant_joint_source_eq_centered_children_and_correction
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (W : ℝ) (hW : W≠0)
    (star U : ℕ) (hs : star<U) (hU : U≤as.length) :
    nativeActualMinimumConstantJointSource M as star U=
      (M.bf (partitionPoint 0 as star):ℝ)*W*
        (((nativeActualConstantSourceChildren M as star U hs hU).flatMap
          (fun Q=>[Q,Q.freeze])).map (nativeActualMinimumFourStateResponse M U W)).sum+
      nativeActualConstantSourceFrozenCorrection M as star U hs hU W := by
  rw [actual_minimum_constant_joint_source_eq_children_and_remainder M as ho W hW star U hs hU]
  unfold nativeActualConstantSourceFrozenCorrection
  simp only [List.map_flatMap,native_sum_flatMap,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,List.sum_map_add]
  ring

theorem actual_minimum_constant_joint_source_eq_finite_four_iteration
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (W : ℝ) (hW : W≠0)
    (star U : ℕ) (hs : star<U) (hU : U≤as.length)
    (hstarK : 0<nativeContinuumMixedClock n M.bf M.hf as star) (depth : ℕ) :
    let children:=nativeActualConstantSourceChildren M as star U hs hU
    nativeActualMinimumConstantJointSource M as star U=
      (M.bf (partitionPoint 0 as star):ℝ)*W*
        (nativeActualMinimumFourResidualSum M hs hU W depth children+
          ((nativeActualMinimumFourCenteredForest M hs hU W depth children).map
            (nativeActualMinimumFourStateResponse M U W)).sum)+
      nativeActualConstantSourceFrozenCorrection M as star U hs hU W := by
  dsimp only
  rw [actual_minimum_constant_joint_source_eq_centered_children_and_correction M as ho W hW star U hs hU]
  rw [actual_minimum_four_resource_finite_iteration M _
    (fun Q hQ=>nativeActualConstantSourceChildren_valid M hs hU Q hQ)
    (Nat.zero_le star) hs hU ho W hW hstarK depth]

end OAI.SKFluctuations.Cavity
