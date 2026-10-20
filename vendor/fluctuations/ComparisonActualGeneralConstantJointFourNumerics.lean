module

public import ComparisonActualGeneralConstantJointFourIteration
public import ComparisonActualGeneralFourFirstHighIteration
public import ComparisonSignedCavityActualConstantJointFourNumerics

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {as : List PositiveMass} {star U : ℕ}
theorem actual_general_constant_joint_source_abs_le_of_four_budgets
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {Temp W cK terminal : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ)≤Temp)
    (hW : 0<W) (hcK : 0<cK) (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U≤as.length)
    (hstarK : cK*W≤nativeContinuumMixedClock n bf hf as star)
    (depth : ℕ) (Bpair Bother Bfirst Bfrozen : ℕ→ℝ)
    (Hpair : ∀j<depth,|actualGeneralFourPairSum bf hf U W
      (actualGeneralFourCenteredForest bf hf hs hU W j
        (actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU))|≤Bpair j)
    (Hother : ∀j<depth,|actualGeneralFourOtherSourceErrorSum bf hf U W
      (actualGeneralFourCenteredForest bf hf hs hU W j
        (actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU))|≤Bother j)
    (Hfirst : ∀j<depth,|actualGeneralFourFirstHighErrorSum bf hf U W
      (actualGeneralFourCenteredForest bf hf hs hU W j
        (actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU))|≤Bfirst j)
    (Hfrozen : ∀j<depth,|actualGeneralFourFrozenChildSum bf hf hs hU W
      (actualGeneralFourCenteredForest bf hf hs hU W j
        (actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU))|≤Bfrozen j)
    (Hterminal : |((actualGeneralFourCenteredForest bf hf hs hU W depth
      (actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU)).map
        (actualGeneralFourStateResponse bf hf U W)).sum|≤terminal) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |actualGeneralConstantJointSource (n:=n) bf hf as star U|≤
      (bf (partitionPoint 0 as star):ℝ)*W*
        (((List.range depth).map (fun j=>
          (|1-(bf (partitionPoint 0 as star):ℝ)*chi^2| *Bpair j+Bother j)/
            (Real.exp (-4*Temp)*cK*W)+Bfrozen j+Bfirst j)).sum+terminal)+
      |actualGeneralConstantSourceFrozenCorrection (n:=n) bf hf as star U hs hU W| := by
  dsimp only
  let children:=actualGeneralConstantSourceChildren (n:=n) bf hf as star U hs hU
  have Hvalid : ∀Q∈children,NativeActualResourceGenerated 0 star U [] Q.generation Q.tree Q.term:=
    fun Q hQ=>actualGeneralConstantSourceChildren_valid bf hf hs hU Q hQ
  have Hlevel j (hj : j<depth):=
    actual_general_four_recursion_error_sum_first_high_abs_le bf hf hbf hhf htotal hW hcK ho
      (Nat.zero_le star) hs hU hstarK
      (actualGeneralFourCenteredForest bf hf hs hU W j children)
      (nativeActualFourCenteredForest_valid _ hs (hs.le.trans hU) _ j children Hvalid)
      (Hpair j hj) (Hother j hj) (Hfirst j hj) (Hfrozen j hj)
  have Hres : |actualGeneralFourResidualSum bf hf hs hU W depth children|≤
      ((List.range depth).map (fun j=>
        (|1-(bf (partitionPoint 0 as star):ℝ)*
          (scalarTerminal.schedule (scalarBoundaryClocks as
            (relocatedClock U 0 (nativeContinuumMixedClock n bf hf as)))).H 0 0^2| *
          Bpair j+Bother j)/(Real.exp (-4*Temp)*cK*W)+Bfrozen j+Bfirst j)).sum := by
    unfold actualGeneralFourResidualSum
    apply (native_abs_sum_map_le _ _).trans
    apply List.sum_le_sum
    intro j hj
    exact Hlevel j (List.mem_range.mp hj)
  rw [actual_general_constant_joint_source_eq_finite_four_iteration (n:=n) bf hf hbf hhf as ho W hW.ne'
    star U hs hU ((mul_pos hcK hW).trans_le hstarK) depth]
  apply (abs_add_le _ _).trans
  apply add_le_add _ le_rfl
  rw [abs_mul,abs_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) hW.le)]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (NNReal.coe_nonneg _) hW.le)
  exact (abs_add_le _ _).trans (add_le_add Hres Hterminal)

end OAI.SKFluctuations.Cavity
