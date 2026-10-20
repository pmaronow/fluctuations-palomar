module

public import ComparisonSignedCavityActualConstantJointFourIteration
public import ComparisonSignedCavityActualFourFirstHighIteration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {star U : ℕ}

theorem actual_minimum_constant_joint_source_abs_le_of_four_budgets
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK terminal : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    (hW : 0<W) (hcK : 0<cK) (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U≤as.length)
    (hstarK : cK*W≤nativeContinuumMixedClock n M.bf M.hf as star)
    (depth : ℕ) (Bpair Bother Bfirst Bfrozen : ℕ→ℝ)
    (Hpair : ∀j<depth,|nativeActualFourPairSum M U W
      (nativeActualMinimumFourCenteredForest M hs hU W j
        (nativeActualConstantSourceChildren M as star U hs hU))|≤Bpair j)
    (Hother : ∀j<depth,|nativeActualFourOtherSourceErrorSum M U W
      (nativeActualMinimumFourCenteredForest M hs hU W j
        (nativeActualConstantSourceChildren M as star U hs hU))|≤Bother j)
    (Hfirst : ∀j<depth,|nativeActualFourFirstHighErrorSum M U W
      (nativeActualMinimumFourCenteredForest M hs hU W j
        (nativeActualConstantSourceChildren M as star U hs hU))|≤Bfirst j)
    (Hfrozen : ∀j<depth,|nativeActualFourFrozenChildSum M hs hU W
      (nativeActualMinimumFourCenteredForest M hs hU W j
        (nativeActualConstantSourceChildren M as star U hs hU))|≤Bfrozen j)
    (Hterminal : |((nativeActualMinimumFourCenteredForest M hs hU W depth
      (nativeActualConstantSourceChildren M as star U hs hU)).map
        (nativeActualMinimumFourStateResponse M U W)).sum|≤terminal) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |nativeActualMinimumConstantJointSource M as star U|≤
      (M.bf (partitionPoint 0 as star):ℝ)*W*
        (((List.range depth).map (fun j=>
          (|1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2| *Bpair j+Bother j)/
            (Real.exp (-4*Temp)*cK*W)+Bfrozen j+Bfirst j)).sum+terminal)+
      |nativeActualConstantSourceFrozenCorrection M as star U hs hU W| := by
  dsimp only
  let children:=nativeActualConstantSourceChildren M as star U hs hU
  have Hvalid : ∀Q∈children,NativeActualResourceGenerated 0 star U [] Q.generation Q.tree Q.term:=
    fun Q hQ=>nativeActualConstantSourceChildren_valid M hs hU Q hQ
  have Hlevel j (hj : j<depth):=
    actual_minimum_four_recursion_error_sum_first_high_abs_le M htotal hW hcK ho
      (Nat.zero_le star) hs hU hstarK
      (nativeActualMinimumFourCenteredForest M hs hU W j children)
      (nativeActualFourCenteredForest_valid _ hs (hs.le.trans hU) _ j children Hvalid)
      (Hpair j hj) (Hother j hj) (Hfirst j hj) (Hfrozen j hj)
  have Hres : |nativeActualMinimumFourResidualSum M hs hU W depth children|≤
      ((List.range depth).map (fun j=>
        (|1-(M.bf (partitionPoint 0 as star):ℝ)*
          (scalarTerminal.schedule (scalarBoundaryClocks as
            (relocatedClock U 0 (nativeContinuumMixedClock n M.bf M.hf as)))).H 0 0^2| *
          Bpair j+Bother j)/(Real.exp (-4*Temp)*cK*W)+Bfrozen j+Bfirst j)).sum := by
    unfold nativeActualMinimumFourResidualSum
    apply (native_abs_sum_map_le _ _).trans
    apply List.sum_le_sum
    intro j hj
    exact Hlevel j (List.mem_range.mp hj)
  rw [actual_minimum_constant_joint_source_eq_finite_four_iteration M as ho W hW.ne'
    star U hs hU ((mul_pos hcK hW).trans_le hstarK) depth]
  apply (abs_add_le _ _).trans
  apply add_le_add _ le_rfl
  rw [abs_mul,abs_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) hW.le)]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (NNReal.coe_nonneg _) hW.le)
  exact (abs_add_le _ _).trans (add_le_add Hres Hterminal)

theorem susceptibility_absorption_with_literal_correction
    {J W C Cbond feedback remainder : ℝ}
    (hsmall : feedback≤1/2)
    (H : |J|≤C*W^2+feedback*(|J|+Cbond*W^2)+remainder) :
    |J|≤2*(C+feedback*Cbond)*W^2+2*remainder := by
  have Hmul:=mul_le_mul_of_nonneg_right hsmall (abs_nonneg J)
  nlinarith

end OAI.SKFluctuations.Cavity
