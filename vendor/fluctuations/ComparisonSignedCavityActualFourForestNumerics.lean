module

public import ComparisonSignedCavityActualFourResidualDecomposition
public import ComparisonSignedCavityActualCenteredFourTerminalLaw

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open Cavity LaplaceWindowFormalization
set_option maxHeartbeats 14000000
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

theorem native_abs_sum_map_le {α : Type} (xs : List α) (F : α→ℝ) :
    |(xs.map F).sum| ≤ (xs.map (fun Q=>|F Q|)).sum := by
  induction xs with
  | nil=>simp
  | cons Q xs ih=>
    simp only [List.map_cons,List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

theorem nativeActualFourCenteredForest_singleton_abs_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0→|Γ st p| ≤ 1)
    (hs : star<U) (hl : star ≤ as.length)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀st tag,|weight st tag| ≤ C)
    (depth : ℕ) (st : NativeActualResourceState S as i star)
    {r : ℕ} (hr : st.tree.leaves ≤ r)
    (F : NativeActualResourceState S as i star→ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀Q∈nativeActualFourCenteredForest Γ hs hl weight depth [st],
      |F Q| ≤ |Q.term.coefficient| *B) :
    |((nativeActualFourCenteredForest Γ hs hl weight depth [st]).map F).sum| ≤
      2*|st.term.coefficient| *
        nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches C 3 r depth*B := by
  have Hraw:=nativeActualWeightedFrontier_terminal_abs_le ho Γ hΓ hs hl
    nativeActualOriginalFourGCenteredBranches weight hC (fun Q b _=>hw Q b.1)
    3 nativeActualOriginalFourGCenteredBranches_length depth st hr F hB (by
      intro Q hQ
      apply hF Q
      rw [nativeActualFourCenteredForest_singleton]
      exact List.mem_append_left _ hQ)
  have Hfrozen:=nativeActualWeightedFrontier_terminal_abs_le ho Γ hΓ hs hl
    nativeActualOriginalFourGCenteredBranches weight hC (fun Q b _=>hw Q b.1)
    3 nativeActualOriginalFourGCenteredBranches_length depth st.freeze hr F hB (by
      intro Q hQ
      apply hF Q
      rw [nativeActualFourCenteredForest_singleton]
      exact List.mem_append_right _ hQ)
  rw [nativeActualFourCenteredForest_singleton_response]
  apply (abs_add_le _ _).trans
  have H:=(add_le_add Hraw Hfrozen)
  simpa only [NativeActualResourceState.freeze,NativeResourceTerm.freeze,abs_neg,
    two_mul,add_mul] using H

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 16000000
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {as : List PositiveMass} {i star U : ℕ}

def nativeActualFourForestCost (Temp cK : ℝ) (depth : ℕ) : ℝ :=
  2*nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
    (Temp/(Real.exp (-4*Temp)*cK)) 3 2 depth

theorem nativeActualFourForestCost_nonneg {Temp cK : ℝ}
    (hTemp : 0 ≤ Temp) (hcK : 0<cK) (depth : ℕ) :
    0 ≤ nativeActualFourForestCost Temp cK depth := by
  apply mul_nonneg (by norm_num)
  exact nativeActualWeightedFrontierCost_nonneg _ (by positivity) _ _ _

theorem actual_minimum_four_state_forest_abs_le
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK B : ℝ} (hTemp : 0 ≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0<W) (hcK : 0<cK) (ho : MassOrdered 0 as)
    (hs : star<U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (depth : ℕ) (st : NativeActualResourceState (Spin n×Bool) as i star)
    {r : ℕ} (hr : st.tree.leaves ≤ r)
    (F : NativeActualResourceState (Spin n×Bool) as i star→ℝ) (hB : 0 ≤ B)
    (hF : ∀Q∈nativeActualMinimumFourCenteredForest M hs hU W depth [st],
      |F Q| ≤ |Q.term.coefficient| *B) :
    |((nativeActualMinimumFourCenteredForest M hs hU W depth [st]).map F).sum| ≤
      2*|st.term.coefficient| *
        nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
          (Temp/(Real.exp (-4*Temp)*cK)) 3 r depth*B := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  exact nativeActualFourCenteredForest_singleton_abs_le ho (nativeOriginalHighRowGamma U K)
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU)
    (fun Q tag=>nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag))
    (C:=Temp/(Real.exp (-4*Temp)*cK)) (by positivity)
    (fun Q tag=>actual_continuum_four_G_weight_bound_of_total_clock M htotal hW hcK as ho
      hs hU hstarK Q tag) depth st hr F hB hF

theorem actual_minimum_four_state_response_abs_le_of_level_budgets
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK terminal : ℝ} (hTemp : 0 ≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0<W) (hcK : 0<cK) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (st : NativeActualResourceState (Spin n×Bool) as i star)
    {seed : List NativeResourceMark}
    (hst : NativeActualResourceGenerated i star U seed st.generation st.tree st.term)
    {r : ℕ} (hr : st.tree.leaves ≤ r)
    (depth : ℕ) (B : ℕ→ℝ) (hB : ∀j<depth,0 ≤ B j)
    (hE : ∀j<depth,∀Q∈nativeActualMinimumFourCenteredForest M hs hU W j [st],
      |nativeActualOriginalFourRecursionError M hs hU W Q| ≤ |Q.term.coefficient| *B j)
    (hterminal : |((nativeActualMinimumFourCenteredForest M hs hU W depth [st]).map
      (nativeActualMinimumFourStateResponse M U W)).sum| ≤ terminal) :
    |nativeActualMinimumFourStateResponse M U W st+
      nativeActualMinimumFourStateResponse M U W st.freeze| ≤
      ((List.range depth).map (fun j=>2*|st.term.coefficient| *
        nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches
          (Temp/(Real.exp (-4*Temp)*cK)) 3 r j*B j)).sum+terminal := by
  have H:=actual_minimum_four_resource_finite_iteration M [st]
    (seed:=seed) (by intro Q hQ;obtain rfl:=List.mem_singleton.mp hQ;exact hst)
    hi hs hU ho W hW.ne' ((mul_pos hcK hW).trans_le hstarK) depth
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero] at H
  rw [H]
  apply (abs_add_le _ _).trans
  apply add_le_add _ hterminal
  unfold nativeActualMinimumFourResidualSum
  apply (native_abs_sum_map_le _ _).trans
  apply List.sum_le_sum
  intro j hj
  exact actual_minimum_four_state_forest_abs_le M hTemp htotal hW hcK ho hs hU hstarK j st hr
    _ (hB j (List.mem_range.mp hj)) (hE j (List.mem_range.mp hj))

theorem actual_minimum_four_initial_forest_abs_le
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK B : ℝ} (hTemp : 0 ≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0<W) (hcK : 0<cK) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (depth : ℕ) (F : NativeActualResourceState (Spin n×Bool) as i star→ℝ) (hB : 0 ≤ B)
    (hF : ∀Q∈nativeActualMinimumFourCenteredForest M hs hU W depth
      [nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU))],
      |F Q| ≤ |Q.term.coefficient| *B) :
    |((nativeActualMinimumFourCenteredForest M hs hU W depth
      [nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU))]).map F).sum| ≤
        nativeActualFourForestCost Temp cK depth*B := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  have H:=nativeActualFourCenteredForest_singleton_abs_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU)
    weight (C:=Temp/(Real.exp (-4*Temp)*cK)) (by positivity)
    (fun Q tag=>actual_continuum_four_G_weight_bound_of_total_clock M htotal hW hcK as ho
      hs hU hstarK Q tag) depth
    (nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU)))
    (nativeActualInitialState_leaves_le as i star 0 (hi.trans (hs.le.trans hU))) F hB hF
  simpa only [nativeActualMinimumFourCenteredForest,nativeActualFourForestCost,
    nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,mul_one] using H

theorem actual_minimum_four_residual_sum_abs_le
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK : ℝ} (hTemp : 0 ≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0<W) (hcK : 0<cK) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (depth : ℕ) (B : ℕ→ℝ) (hB : ∀j<depth,0 ≤ B j)
    (hE : ∀j<depth,∀Q∈nativeActualMinimumFourCenteredForest M hs hU W j
      [nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU))],
      |nativeActualOriginalFourRecursionError M hs hU W Q| ≤ |Q.term.coefficient| *B j) :
    |nativeActualMinimumFourResidualSum M hs hU W depth
      [nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU))]| ≤
        ((List.range depth).map (fun j=>nativeActualFourForestCost Temp cK j*B j)).sum := by
  unfold nativeActualMinimumFourResidualSum
  apply (native_abs_sum_map_le _ _).trans
  apply List.sum_le_sum
  intro j hj
  exact actual_minimum_four_initial_forest_abs_le M hTemp htotal hW hcK ho hi hs hU hstarK
    j _ (hB j (List.mem_range.mp hj)) (hE j (List.mem_range.mp hj))

theorem actual_minimum_four_response_abs_le_of_level_budgets
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {Temp W cK terminal : ℝ} (hTemp : 0 ≤ Temp)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ Temp)
    (hW : 0<W) (hcK : 0<cK) (ho : MassOrdered 0 as)
    (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length)
    (hstarK : cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star)
    (depth : ℕ) (B : ℕ→ℝ) (hB : ∀j<depth,0 ≤ B j)
    (hE : ∀j<depth,∀Q∈nativeActualMinimumFourCenteredForest M hs hU W j
      [nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU))],
      |nativeActualOriginalFourRecursionError M hs hU W Q| ≤ |Q.term.coefficient| *B j)
    (hterminal : |nativeActualOriginalContinuumCenteredFourGFrontier M as W i star U hi hs hU depth| ≤ terminal) :
    let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
    |nativeActualMinimumFourStateResponse M U W st+
      nativeActualMinimumFourStateResponse M U W st.freeze| ≤
      ((List.range depth).map (fun j=>nativeActualFourForestCost Temp cK j*B j)).sum+terminal := by
  dsimp only
  rw [actual_minimum_initial_four_resource_finite_iteration M as W i star U hi hs hU ho hW.ne'
    ((mul_pos hcK hW).trans_le hstarK) depth]
  exact (abs_add_le _ _).trans (add_le_add
    (actual_minimum_four_residual_sum_abs_le M hTemp htotal hW hcK ho hi hs hU hstarK depth B hB hE)
    hterminal)

end OAI.SKFluctuations.Cavity
