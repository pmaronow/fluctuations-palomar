module

public import ComparisonActualGeneralFourCollectiveIteration
public import ComparisonActualGeneralFourCategories
public import ComparisonSignedCavityActualFourFirstHighIteration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {as : List PositiveMass} {i star U : ℕ}
def actualGeneralFourFirstHighError
    {n : ℕ}
    (bf hf : ℝ→ℝ≥0)
    {as : List PositiveMass} {i star : ℕ} (U : ℕ) (W : ℝ)
    (st : NativeActualResourceState (Spin n×Bool) as i star) : ℝ :=
  let K:=nativeContinuumMixedClock n bf hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0;
  -((W⁻¹)^st.generation/(chi*K star))*actualGeneralFourFirstHighContrast bf hf U st

theorem actual_general_four_recursion_error_first_high_decomposition
    {n : ℕ}
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {as : List PositiveMass} {i star U : ℕ}
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hP : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as) (hU : U≤as.length) (W : ℝ) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    actualGeneralFourRecursionError bf hf hs hU W st=
      (1-(bf (partitionPoint 0 as star):ℝ)*chi^2)/(chi*K star)*
        ((W⁻¹)^st.generation*actualGeneralFourPairContrast bf hf U st)+
      actualGeneralFourFirstHighError bf hf U W st-
      (1/(chi*K star))*((W⁻¹)^st.generation*actualGeneralFourOtherSourceErrorContrast bf hf U st)-
      actualGeneralFourFrozenChildCorrection bf hf hs hU W st := by
  rw [actual_general_four_recursion_error_decomposition,
    actual_general_four_source_error_eq_first_high_add_other bf hf hbf hhf st hP hi hs ho]
  unfold actualGeneralFourFirstHighError
  dsimp only
  ring

def actualGeneralFourOtherSourceErrorSum
    (bf hf : ℝ→ℝ≥0) (U : ℕ) (W : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  (xs.map (fun Q=>(W⁻¹)^Q.generation*actualGeneralFourOtherSourceErrorContrast bf hf U Q)).sum

def actualGeneralFourFirstHighErrorSum
    (bf hf : ℝ→ℝ≥0) (U : ℕ) (W : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  (xs.map (actualGeneralFourFirstHighError bf hf U W)).sum

theorem actual_general_four_recursion_error_sum_first_high_decomposition
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as) (hU : U ≤ as.length) (W : ℝ) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    (xs.map (actualGeneralFourRecursionError bf hf hs hU W)).sum=
      (1-(bf (partitionPoint 0 as star):ℝ)*chi^2)/(chi*K star)*
        actualGeneralFourPairSum bf hf U W xs+
      actualGeneralFourFirstHighErrorSum bf hf U W xs-
      (1/(chi*K star))*actualGeneralFourOtherSourceErrorSum bf hf U W xs-
        actualGeneralFourFrozenChildSum bf hf hs hU W xs := by
  dsimp only
  induction xs with
  | nil=>simp [actualGeneralFourPairSum,actualGeneralFourFirstHighErrorSum,
      actualGeneralFourOtherSourceErrorSum,actualGeneralFourFrozenChildSum]
  | cons Q xs ih=>
    have HQ:=hxs Q (by simp)
    have HT : ∀R∈xs,NativeActualResourceGenerated i star U seed R.generation R.tree R.term:=by
      intro R hR;exact hxs R (List.mem_cons_of_mem Q hR)
    simp only [List.map_cons,List.sum_cons]
    rw [actual_general_four_recursion_error_first_high_decomposition bf hf hbf hhf Q HQ hi hs ho hU W,ih HT]
    simp only [actualGeneralFourPairSum,actualGeneralFourFirstHighErrorSum,
      actualGeneralFourOtherSourceErrorSum,actualGeneralFourFrozenChildSum,List.map_cons,List.sum_cons]
    ring

theorem actual_general_four_recursion_error_sum_first_high_abs_le
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    {Temp W cK Bpair Bother Bfirst Bfrozen : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,(hf u:ℝ)+(bf u:ℝ) ≤ Temp)
    (hW : 0 < W) (hcK : 0 < cK) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n bf hf as star)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (Hpair : |actualGeneralFourPairSum bf hf U W xs| ≤ Bpair)
    (Hother : |actualGeneralFourOtherSourceErrorSum bf hf U W xs| ≤ Bother)
    (Hfirst : |actualGeneralFourFirstHighErrorSum bf hf U W xs| ≤ Bfirst)
    (Hfrozen : |actualGeneralFourFrozenChildSum bf hf hs hU W xs| ≤ Bfrozen) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |(xs.map (actualGeneralFourRecursionError bf hf hs hU W)).sum| ≤
      (|1-(bf (partitionPoint 0 as star):ℝ)*chi^2| *Bpair+Bother)/
        (Real.exp (-4*Temp)*cK*W)+Bfrozen+Bfirst := by
  dsimp only
  rw [actual_general_four_recursion_error_sum_first_high_decomposition bf hf hbf hhf xs hxs hi hs ho hU W]
  obtain ⟨_,_,hden⟩:=actual_general_four_denominator_bounds bf hf hbf hhf htotal hW hcK ho hs hU hstarK
  have H:=four_collective_source_envelope
    (J:=1-(bf (partitionPoint 0 as star):ℝ)*
      (scalarTerminal.schedule (scalarBoundaryClocks as
        (relocatedClock U 0 (nativeContinuumMixedClock n bf hf as)))).H 0 0^2)
    (by positivity) hden Hpair Hother Hfrozen
  have HE (a b c d : ℝ) : a+b-c-d=(a-c-d)+b:=by ring
  rw [HE]
  exact (abs_add_le _ _).trans (add_le_add H Hfirst)

theorem actual_general_four_state_response_abs_le_of_first_high_and_other_budgets
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
    (depth : ℕ) (Bpair Bother Bfirst Bfrozen : ℕ→ℝ)
    (Hpair : ∀j < depth,|actualGeneralFourPairSum bf hf U W
      (actualGeneralFourCenteredForest bf hf hs hU W j [st])| ≤ Bpair j)
    (Hother : ∀j < depth,|actualGeneralFourOtherSourceErrorSum bf hf U W
      (actualGeneralFourCenteredForest bf hf hs hU W j [st])| ≤ Bother j)
    (Hfirst : ∀j < depth,|actualGeneralFourFirstHighErrorSum bf hf U W
      (actualGeneralFourCenteredForest bf hf hs hU W j [st])| ≤ Bfirst j)
    (Hfrozen : ∀j < depth,|actualGeneralFourFrozenChildSum bf hf hs hU W
      (actualGeneralFourCenteredForest bf hf hs hU W j [st])| ≤ Bfrozen j)
    (Hterminal : |((actualGeneralFourCenteredForest bf hf hs hU W depth [st]).map
      (actualGeneralFourStateResponse bf hf U W)).sum| ≤ terminal) :
    let K:=nativeContinuumMixedClock n bf hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |actualGeneralFourStateResponse bf hf U W st+
      actualGeneralFourStateResponse bf hf U W st.freeze| ≤
      ((List.range depth).map (fun j=>
        (|1-(bf (partitionPoint 0 as star):ℝ)*chi^2| *Bpair j+Bother j)/
          (Real.exp (-4*Temp)*cK*W)+Bfrozen j+Bfirst j)).sum+terminal := by
  dsimp only
  have Hvalid : ∀Q∈[st],NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term := by
    intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact hst
  have H:=actual_general_four_resource_finite_iteration bf hf hbf hhf [st] Hvalid
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
  let K:=nativeContinuumMixedClock n bf hf as
  let b:=fun l=>(bf (partitionPoint 0 as l):ℝ)
  have Hv:=nativeActualFourCenteredForest_valid (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    (fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)) j [st] Hvalid
  exact actual_general_four_recursion_error_sum_first_high_abs_le bf hf hbf hhf htotal hW hcK ho hi hs hU hstarK _ Hv
    (Hpair j (List.mem_range.mp hj)) (Hother j (List.mem_range.mp hj))
    (Hfirst j (List.mem_range.mp hj)) (Hfrozen j (List.mem_range.mp hj))

end OAI.SKFluctuations.Cavity
