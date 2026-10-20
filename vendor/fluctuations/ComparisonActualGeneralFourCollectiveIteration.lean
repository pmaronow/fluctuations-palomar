module

public import ComparisonActualGeneralFourSource
public import ComparisonSignedCavityActualFourCollectiveIteration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {as : List PositiveMass} {i star U : ℕ}
def actualGeneralFourPairSum
    (bf hf : ℝ→ℝ≥0) (U : ℕ) (W : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  (xs.map (fun Q=>(W⁻¹)^Q.generation*actualGeneralFourPairContrast bf hf U Q)).sum

def actualGeneralFourSourceErrorSum
    (bf hf : ℝ→ℝ≥0) (U : ℕ) (W : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  (xs.map (fun Q=>(W⁻¹)^Q.generation*actualGeneralFourSourceErrorContrast bf hf U Q)).sum

def actualGeneralFourFrozenChildSum
    (bf hf : ℝ→ℝ≥0)
    (hs : star < U) (hU : U ≤ as.length) (W : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  (xs.map (actualGeneralFourFrozenChildCorrection bf hf hs hU W)).sum

theorem actual_general_four_recursion_error_sum_decomposition
    (bf hf : ℝ→ℝ≥0)
    (hs : star < U) (hU : U ≤ as.length) (W : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    (xs.map (actualGeneralFourRecursionError bf hf hs hU W)).sum=
      (1-(bf (partitionPoint 0 as star):ℝ)*chi^2)/(chi*K star)*
        actualGeneralFourPairSum bf hf U W xs-
      (1/(chi*K star))*actualGeneralFourSourceErrorSum bf hf U W xs-
        actualGeneralFourFrozenChildSum bf hf hs hU W xs := by
  dsimp only
  induction xs with
  | nil=>simp [actualGeneralFourPairSum,actualGeneralFourSourceErrorSum,actualGeneralFourFrozenChildSum]
  | cons Q xs ih=>
    simp only [List.map_cons,List.sum_cons]
    rw [actual_general_four_recursion_error_decomposition,ih]
    simp only [actualGeneralFourPairSum,actualGeneralFourSourceErrorSum,actualGeneralFourFrozenChildSum,
      List.map_cons,List.sum_cons]
    ring

theorem actual_general_four_recursion_error_sum_abs_le
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {Temp W cK Bpair Bsource Bfrozen : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    (hW : 0 < W) (hcK : 0 < cK) (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n bf hf as star)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    (Hpair : |actualGeneralFourPairSum bf hf U W xs| ≤ Bpair)
    (Hsource : |actualGeneralFourSourceErrorSum bf hf U W xs| ≤ Bsource)
    (Hfrozen : |actualGeneralFourFrozenChildSum bf hf hs hU W xs| ≤ Bfrozen) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |(xs.map (actualGeneralFourRecursionError bf hf hs hU W)).sum| ≤
      (|1-(bf (partitionPoint 0 as star):ℝ)*chi^2| *Bpair+Bsource)/
        (Real.exp (-4*Temp)*cK*W)+Bfrozen := by
  dsimp only
  rw [actual_general_four_recursion_error_sum_decomposition]
  obtain ⟨_,_,hden⟩:=actual_general_four_denominator_bounds bf hf hbf hhf htotal hW hcK ho hs hU hstarK
  exact four_collective_source_envelope (by positivity) hden Hpair Hsource Hfrozen

theorem actual_general_four_state_response_abs_le_of_collective_source_budgets
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {Temp W cK terminal : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    (hW : 0 < W) (hcK : 0 < cK) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n bf hf as star)
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hst : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (depth : ℕ) (Bpair Bsource Bfrozen : ℕ→ℝ)
    (Hpair : ∀j < depth,|actualGeneralFourPairSum bf hf U W
      (actualGeneralFourCenteredForest bf hf hs hU W j [st])| ≤ Bpair j)
    (Hsource : ∀j < depth,|actualGeneralFourSourceErrorSum bf hf U W
      (actualGeneralFourCenteredForest bf hf hs hU W j [st])| ≤ Bsource j)
    (Hfrozen : ∀j < depth,|actualGeneralFourFrozenChildSum bf hf hs hU W
      (actualGeneralFourCenteredForest bf hf hs hU W j [st])| ≤ Bfrozen j)
    (Hterminal : |((actualGeneralFourCenteredForest bf hf hs hU W depth [st]).map
      (actualGeneralFourStateResponse bf hf U W)).sum| ≤ terminal) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |actualGeneralFourStateResponse bf hf U W st+
      actualGeneralFourStateResponse bf hf U W st.freeze| ≤
      ((List.range depth).map (fun j=>
        (|1-(bf (partitionPoint 0 as star):ℝ)*chi^2| *Bpair j+Bsource j)/
          (Real.exp (-4*Temp)*cK*W)+Bfrozen j)).sum+terminal := by
  dsimp only
  have H:=actual_general_four_resource_finite_iteration bf hf hbf hhf [st]
    (seed:=seed) (by intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact hst)
    hi hs hU ho W hW.ne' ((mul_pos hcK hW).trans_le hstarK) depth
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero] at H
  rw [H]
  apply (abs_add_le _ _).trans
  apply add_le_add _ Hterminal
  unfold actualGeneralFourResidualSum
  apply (native_abs_sum_map_le _ _).trans
  apply List.sum_le_sum
  intro j hj
  exact actual_general_four_recursion_error_sum_abs_le bf hf hbf hhf htotal hW hcK ho hs hU hstarK _
    (Hpair j (List.mem_range.mp hj)) (Hsource j (List.mem_range.mp hj))
    (Hfrozen j (List.mem_range.mp hj))

end OAI.SKFluctuations.Cavity
