module

public import ComparisonSignedCavityActualFourCollectiveIteration
public import ComparisonSignedCavityActualFourFirstHighDecomposition

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star U : ℕ}

def nativeActualFourOtherSourceErrorSum
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  (xs.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourOtherSourceErrorContrast M U Q)).sum

def nativeActualFourFirstHighErrorSum
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  (xs.map (nativeActualOriginalFourFirstHighError M U W)).sum

theorem actual_minimum_four_recursion_error_sum_first_high_decomposition
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (hi : i ≤ star) (hs : star < U) (ho : MassOrdered 0 as) (hU : U ≤ as.length) (W : ℝ) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    (xs.map (nativeActualOriginalFourRecursionError M hs hU W)).sum=
      (1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2)/(chi*K star)*
        nativeActualFourPairSum M U W xs+
      nativeActualFourFirstHighErrorSum M U W xs-
      (1/(chi*K star))*nativeActualFourOtherSourceErrorSum M U W xs-
        nativeActualFourFrozenChildSum M hs hU W xs := by
  dsimp only
  induction xs with
  | nil=>simp [nativeActualFourPairSum,nativeActualFourFirstHighErrorSum,
      nativeActualFourOtherSourceErrorSum,nativeActualFourFrozenChildSum]
  | cons Q xs ih=>
    have HQ:=hxs Q (by simp)
    have HT : ∀R∈xs,NativeActualResourceGenerated i star U seed R.generation R.tree R.term:=by
      intro R hR;exact hxs R (List.mem_cons_of_mem Q hR)
    simp only [List.map_cons,List.sum_cons]
    rw [actual_minimum_four_recursion_error_first_high_decomposition M Q HQ hi hs ho hU W,ih HT]
    simp only [nativeActualFourPairSum,nativeActualFourFirstHighErrorSum,
      nativeActualFourOtherSourceErrorSum,nativeActualFourFrozenChildSum,List.map_cons,List.sum_cons]
    ring

theorem actual_minimum_four_recursion_error_sum_first_high_abs_le
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK Bpair Bother Bfirst Bfrozen : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0 < W) (hcK : 0 < cK) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    {seed : List NativeResourceMark}
    (hxs : ∀Q∈xs,NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term)
    (Hpair : |nativeActualFourPairSum M U W xs| ≤ Bpair)
    (Hother : |nativeActualFourOtherSourceErrorSum M U W xs| ≤ Bother)
    (Hfirst : |nativeActualFourFirstHighErrorSum M U W xs| ≤ Bfirst)
    (Hfrozen : |nativeActualFourFrozenChildSum M hs hU W xs| ≤ Bfrozen) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |(xs.map (nativeActualOriginalFourRecursionError M hs hU W)).sum| ≤
      (|1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2| *Bpair+Bother)/
        (Real.exp (-4*Temp)*cK*W)+Bfrozen+Bfirst := by
  dsimp only
  rw [actual_minimum_four_recursion_error_sum_first_high_decomposition M xs hxs hi hs ho hU W]
  obtain ⟨_,_,hden⟩:=actual_minimum_four_denominator_bounds M htotal hW hcK ho hs hU hstarK
  have H:=four_collective_source_envelope
    (J:=1-(M.bf (partitionPoint 0 as star):ℝ)*
      (scalarTerminal.schedule (scalarBoundaryClocks as
        (relocatedClock U 0 (nativeContinuumMixedClock n M.bf M.hf as)))).H 0 0^2)
    (by positivity) hden Hpair Hother Hfrozen
  have HE (a b c d : ℝ) : a+b-c-d=(a-c-d)+b:=by ring
  rw [HE]
  exact (abs_add_le _ _).trans (add_le_add H Hfirst)

theorem actual_minimum_four_state_response_abs_le_of_first_high_and_other_budgets
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK terminal : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0 < W) (hcK : 0 < cK) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hst : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (depth : ℕ) (Bpair Bother Bfirst Bfrozen : ℕ→ℝ)
    (Hpair : ∀j < depth,|nativeActualFourPairSum M U W
      (nativeActualMinimumFourCenteredForest M hs hU W j [st])| ≤ Bpair j)
    (Hother : ∀j < depth,|nativeActualFourOtherSourceErrorSum M U W
      (nativeActualMinimumFourCenteredForest M hs hU W j [st])| ≤ Bother j)
    (Hfirst : ∀j < depth,|nativeActualFourFirstHighErrorSum M U W
      (nativeActualMinimumFourCenteredForest M hs hU W j [st])| ≤ Bfirst j)
    (Hfrozen : ∀j < depth,|nativeActualFourFrozenChildSum M hs hU W
      (nativeActualMinimumFourCenteredForest M hs hU W j [st])| ≤ Bfrozen j)
    (Hterminal : |((nativeActualMinimumFourCenteredForest M hs hU W depth [st]).map
      (nativeActualMinimumFourStateResponse M U W)).sum| ≤ terminal) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |nativeActualMinimumFourStateResponse M U W st+
      nativeActualMinimumFourStateResponse M U W st.freeze| ≤
      ((List.range depth).map (fun j=>
        (|1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2| *Bpair j+Bother j)/
          (Real.exp (-4*Temp)*cK*W)+Bfrozen j+Bfirst j)).sum+terminal := by
  dsimp only
  have Hvalid : ∀Q∈[st],NativeActualResourceGenerated i star U seed Q.generation Q.tree Q.term := by
    intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact hst
  have H:=actual_minimum_four_resource_finite_iteration M [st] Hvalid
    hi hs hU ho W hW.ne' ((mul_pos hcK hW).trans_le hstarK) depth
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero] at H
  rw [H]
  apply (abs_add_le _ _).trans
  apply add_le_add _ Hterminal
  unfold nativeActualMinimumFourResidualSum
  apply (native_abs_sum_map_le _ _).trans
  apply List.sum_le_sum
  intro j hj
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun l=>(M.bf (partitionPoint 0 as l):ℝ)
  have Hv:=nativeActualFourCenteredForest_valid (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    (fun parent tag=>nativeOriginalClockParentWeight W U K parent
      (nativeOriginalClockFourGBranchBeta U K b parent tag)) j [st] Hvalid
  exact actual_minimum_four_recursion_error_sum_first_high_abs_le M htotal hW hcK ho hi hs hU hstarK _ Hv
    (Hpair j (List.mem_range.mp hj)) (Hother j (List.mem_range.mp hj))
    (Hfirst j (List.mem_range.mp hj)) (Hfrozen j (List.mem_range.mp hj))

end OAI.SKFluctuations.Cavity
