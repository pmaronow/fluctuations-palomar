module

public import ComparisonSignedCavityActualFourForestNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star U : ℕ}

def nativeActualFourPairSum
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  (xs.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourPairContrast M U Q)).sum

def nativeActualFourSourceErrorSum
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (U : ℕ) (W : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  (xs.map (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourSourceErrorContrast M U Q)).sum

def nativeActualFourFrozenChildSum
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) : ℝ :=
  (xs.map (nativeActualOriginalFourFrozenChildCorrection M hs hU W)).sum

theorem native_actual_original_four_recursion_error_sum_decomposition
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hs : star < U) (hU : U ≤ as.length) (W : ℝ)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star)) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    (xs.map (nativeActualOriginalFourRecursionError M hs hU W)).sum=
      (1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2)/(chi*K star)*
        nativeActualFourPairSum M U W xs-
      (1/(chi*K star))*nativeActualFourSourceErrorSum M U W xs-
        nativeActualFourFrozenChildSum M hs hU W xs := by
  dsimp only
  induction xs with
  | nil=>simp [nativeActualFourPairSum,nativeActualFourSourceErrorSum,nativeActualFourFrozenChildSum]
  | cons Q xs ih=>
    simp only [List.map_cons,List.sum_cons]
    rw [native_actual_original_four_recursion_error_decomposition,ih]
    simp only [nativeActualFourPairSum,nativeActualFourSourceErrorSum,nativeActualFourFrozenChildSum,
      List.map_cons,List.sum_cons]
    ring

theorem four_collective_source_envelope
    {J denominator lower pair source frozen Bpair Bsource Bfrozen : ℝ}
    (hlower : 0 < lower) (hden : lower ≤ denominator)
    (Hpair : |pair| ≤ Bpair) (Hsource : |source| ≤ Bsource)
    (Hfrozen : |frozen| ≤ Bfrozen) :
    |J/denominator*pair-(1/denominator)*source-frozen| ≤
      (|J| *Bpair+Bsource)/lower+Bfrozen := by
  have hd : 0 < denominator:=hlower.trans_le hden
  have hp:=(abs_nonneg _).trans Hpair
  have hs:=(abs_nonneg _).trans Hsource
  have Hsub (a b : ℝ) : |a-b| ≤ |a|+|b| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le a (-b)
  apply (Hsub _ _).trans
  apply (add_le_add (Hsub _ _) Hfrozen).trans
  simp only [abs_mul,abs_div,abs_of_pos hd,abs_one]
  apply (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left Hpair (div_nonneg (abs_nonneg J) hd.le))
    (mul_le_mul_of_nonneg_left Hsource (div_nonneg zero_le_one hd.le))) le_rfl).trans
  apply add_le_add _ le_rfl
  calc
    _=(|J| *Bpair+Bsource)/denominator := by ring
    _≤_:=div_le_div_of_nonneg_left (by positivity) hlower hden

theorem actual_minimum_four_recursion_error_sum_abs_le
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK Bpair Bsource Bfrozen : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0 < W) (hcK : 0 < cK) (ho : MassOrdered 0 as)
    (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (xs : List (NativeActualResourceState (Spin n×Bool) as i star))
    (Hpair : |nativeActualFourPairSum M U W xs| ≤ Bpair)
    (Hsource : |nativeActualFourSourceErrorSum M U W xs| ≤ Bsource)
    (Hfrozen : |nativeActualFourFrozenChildSum M hs hU W xs| ≤ Bfrozen) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |(xs.map (nativeActualOriginalFourRecursionError M hs hU W)).sum| ≤
      (|1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2| *Bpair+Bsource)/
        (Real.exp (-4*Temp)*cK*W)+Bfrozen := by
  dsimp only
  rw [native_actual_original_four_recursion_error_sum_decomposition]
  obtain ⟨_,_,hden⟩:=actual_minimum_four_denominator_bounds M htotal hW hcK ho hs hU hstarK
  exact four_collective_source_envelope (by positivity) hden Hpair Hsource Hfrozen

theorem actual_minimum_four_state_response_abs_le_of_collective_source_budgets
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK terminal : ℝ}
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0 < W) (hcK : 0 < cK) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hst : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    (depth : ℕ) (Bpair Bsource Bfrozen : ℕ→ℝ)
    (Hpair : ∀j < depth,|nativeActualFourPairSum M U W
      (nativeActualMinimumFourCenteredForest M hs hU W j [st])| ≤ Bpair j)
    (Hsource : ∀j < depth,|nativeActualFourSourceErrorSum M U W
      (nativeActualMinimumFourCenteredForest M hs hU W j [st])| ≤ Bsource j)
    (Hfrozen : ∀j < depth,|nativeActualFourFrozenChildSum M hs hU W
      (nativeActualMinimumFourCenteredForest M hs hU W j [st])| ≤ Bfrozen j)
    (Hterminal : |((nativeActualMinimumFourCenteredForest M hs hU W depth [st]).map
      (nativeActualMinimumFourStateResponse M U W)).sum| ≤ terminal) :
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
    |nativeActualMinimumFourStateResponse M U W st+
      nativeActualMinimumFourStateResponse M U W st.freeze| ≤
      ((List.range depth).map (fun j=>
        (|1-(M.bf (partitionPoint 0 as star):ℝ)*chi^2| *Bpair j+Bsource j)/
          (Real.exp (-4*Temp)*cK*W)+Bfrozen j)).sum+terminal := by
  dsimp only
  have H:=actual_minimum_four_resource_finite_iteration M [st]
    (seed:=seed) (by intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact hst)
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
  exact actual_minimum_four_recursion_error_sum_abs_le M htotal hW hcK ho hs hU hstarK _
    (Hpair j (List.mem_range.mp hj)) (Hsource j (List.mem_range.mp hj))
    (Hfrozen j (List.mem_range.mp hj))

end OAI.SKFluctuations.Cavity
