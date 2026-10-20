module

public import ComparisonActualGeneralConstantJointFourReadout
public import ComparisonSignedCavityActualConstantJointFourIteration

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {as : List PositiveMass} {star U : ℕ}
def actualGeneralConstantJointSource
    (bf hf : ℝ→ℝ≥0)
    (as : List PositiveMass) (star U : ℕ) : ℝ :=
  nativeActualConstantJointStarSource n as star U
    (fun j=>(bf (partitionPoint 0 as j):ℝ)) (fun j=>(hf (partitionPoint 0 as j):ℝ))
    (nativeContinuumMixedClock n bf hf as) (nativePhysicalResourceCenter n bf hf as)

def actualGeneralConstantSourceRemainder
    (bf hf : ℝ→ℝ≥0)
    (as : List PositiveMass) (star U : ℕ) : ℝ :=
  let T:=ClockTree.single (S:=Spin n×Bool) as
  let s:=singleSlot as
  let g:=nativeFreshAtSlot T 0 s star
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let S:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  chi*K star*(nativeRetainedLongitudinalPairing n q U b h K g.tree (fun _=>1) (g.embed s)+
    nativeRetainedLongitudinalPairing n q U b h K g.tree (fun _=>1) g.mark)+
  chi^2*b star*(finitePhysicalMean (n+1) as b h star-
    finitePhysicalMean (n+1) as b h star/(n+1:ℕ)-S star)+
  nativeActualJointRestoredForwardTaylorError n q U b h K S g.tree (fun _=>1) (g.embed s) g.mark

def actualGeneralConstantSourceFrozenCorrection
    (bf hf : ℝ→ℝ≥0)
    (as : List PositiveMass) (star U : ℕ) (hs : star<U) (hU : U≤as.length) (W : ℝ) : ℝ :=
  actualGeneralConstantSourceRemainder (n:=n) bf hf as star U-
    (bf (partitionPoint 0 as star):ℝ)*W*
      ((actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU).map
        (fun Q=>actualGeneralFourStateResponse bf hf U W Q.freeze)).sum

theorem actual_general_constant_joint_source_eq_children_and_remainder
    (bf hf : ℝ→ℝ≥0)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (W : ℝ) (hW : W≠0)
    (star U : ℕ) (hs : star<U) (hU : U≤as.length) :
    actualGeneralConstantJointSource (n:=n) bf hf as star U=
      (bf (partitionPoint 0 as star):ℝ)*W*
        ((actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU).map
          (actualGeneralFourStateResponse bf hf U W)).sum+
      actualGeneralConstantSourceRemainder (n:=n) bf hf as star U := by
  have H:=actual_general_constant_source_children_response (n:=n) bf hf as ho W hW star U hs hU
  dsimp only at H
  let b:=fun j=>(bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n bf hf as
  let S:=nativePhysicalResourceCenter n bf hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  have Hq : finitePhysicalCavitySquareVariance n U as b h 1 1=
      cutFullVariance n q U 1 1 b h K:=
    native_full_endpoint_clock_mixed_independent n q U 1 b h _ K
  change _+nativeOriginalFreshPartnerLResponse n 0 (finitePhysicalCavitySquareVariance n U as b h 1 1)
    0 U K b S _ _ star _= _ at H
  rw [Hq] at H
  unfold actualGeneralConstantJointSource nativeActualConstantJointStarSource
    actualGeneralConstantSourceRemainder
  dsimp only
  linear_combination (bf (partitionPoint 0 as star):ℝ)*H

theorem actual_general_constant_joint_source_eq_centered_children_and_correction
    (bf hf : ℝ→ℝ≥0)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (W : ℝ) (hW : W≠0)
    (star U : ℕ) (hs : star<U) (hU : U≤as.length) :
    actualGeneralConstantJointSource (n:=n) bf hf as star U=
      (bf (partitionPoint 0 as star):ℝ)*W*
        (((actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU).flatMap
          (fun Q=>[Q,Q.freeze])).map (actualGeneralFourStateResponse bf hf U W)).sum+
      actualGeneralConstantSourceFrozenCorrection (n:=n) bf hf as star U hs hU W := by
  rw [actual_general_constant_joint_source_eq_children_and_remainder (n:=n) bf hf as ho W hW star U hs hU]
  unfold actualGeneralConstantSourceFrozenCorrection
  simp only [List.map_flatMap,native_sum_flatMap,List.map_cons,List.map_nil,List.sum_cons,
    List.sum_nil,add_zero,List.sum_map_add]
  ring

theorem actual_general_constant_joint_source_eq_finite_four_iteration
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (W : ℝ) (hW : W≠0)
    (star U : ℕ) (hs : star<U) (hU : U≤as.length)
    (hstarK : 0<nativeContinuumMixedClock n bf hf as star) (depth : ℕ) :
    let children:=actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU
    actualGeneralConstantJointSource (n:=n) bf hf as star U=
      (bf (partitionPoint 0 as star):ℝ)*W*
        (actualGeneralFourResidualSum bf hf hs hU W depth children+
          ((actualGeneralFourCenteredForest bf hf hs hU W depth children).map
            (actualGeneralFourStateResponse bf hf U W)).sum)+
      actualGeneralConstantSourceFrozenCorrection (n:=n) bf hf as star U hs hU W := by
  dsimp only
  rw [actual_general_constant_joint_source_eq_centered_children_and_correction (n:=n) bf hf as ho W hW star U hs hU]
  rw [actual_general_four_resource_finite_iteration bf hf hbf hhf _
    (fun Q hQ=>actualGeneralConstantSourceChildren_valid bf hf hs hU Q hQ)
    (Nat.zero_le star) hs hU ho W hW hstarK depth]

end OAI.SKFluctuations.Cavity
