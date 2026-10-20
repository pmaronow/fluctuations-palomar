module

public import ComparisonActualGeneralTargetMeanReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Set Filter MeasureTheory ProbabilityTheory LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem actual_general_target_response_eq_initial_four_state
    (bf hf : ℝ→ℝ≥0)
    (as : List PositiveMass) (i star U : ℕ) (hi : i≤as.length) (W : ℝ) :
    actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i U=
      actualGeneralFourStateResponse (n:=n) bf hf U W (nativeActualInitialState (S:=Spin n×Bool) as i star 0 hi) := by
  unfold actualGeneralTargetLongitudinalResponse actualGeneralFourStateResponse
    nativeOriginalClockStateResponse nativeOriginalClockResourceResponse
  dsimp only [nativeActualInitialState,NativeResourceTerm.ofLive,nativeResourceSeed]
  simp only [pow_zero,one_mul]
  congr 1
  funext σ
  simp only [NativeResourceTerm.value,NativeResourceTerm.scalar,
    List.map_nil,List.prod_nil,one_mul,NativeResourceMark.cut,nativeGeneratedSeed,
    NativeGeneratedTest.value,NativeGeneratedTest.edges,nativeGeneratedEdgeProduct,
    List.map_nil,List.nil_append,List.map_singleton,List.prod_singleton]
  rw [splitIndex_symm,nativeFreshAtSlot_split,splitIndex_self,Nat.min_eq_left hi]
  rw [(nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i).restrict_at]
  rw [(nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i).spin_at]

theorem actual_general_target_response_eq_four_iteration
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (W : ℝ) (i star U : ℕ)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length) (ho : MassOrdered 0 as)
    (hW : W≠0) (hstarK : 0<nativeContinuumMixedClock n bf hf as star) (depth : ℕ) :
    let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
    actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i U=
      actualGeneralFourResidualSum bf hf hs hU W depth [st]+
      ((actualGeneralFourCenteredForest bf hf hs hU W depth [st]).map
        (actualGeneralFourStateResponse (n:=n) bf hf U W)).sum-
      actualGeneralFourStateResponse (n:=n) bf hf U W st.freeze := by
  dsimp only
  let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
  have hvalid : ∀Q∈[st],NativeActualResourceGenerated i star U [.initial] Q.generation Q.tree Q.term := by
    intro Q hQ
    simp only [List.mem_singleton] at hQ
    subst Q
    exact .physical (.seed as hU 0 .initial (Or.inl rfl) (by change i≤as.length;omega))
  have H:=actual_general_four_resource_finite_iteration bf hf hbf hhf [st] hvalid hi hs hU ho W hW hstarK depth
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,add_zero] at H
  rw [←actual_general_target_response_eq_initial_four_state (n:=n) bf hf as i star U
    (hi.trans (hs.le.trans hU)) W] at H
  linarith only [H]

theorem actual_general_target_response_bound_of_level_prices
    (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (W : ℝ) (i star U : ℕ)
    (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length) (ho : MassOrdered 0 as)
    (hW : W≠0) (hstarK : 0<nativeContinuumMixedClock n bf hf as star) (depth : ℕ)
    (budget : ℕ→ℝ) (terminalBudget frozenBudget : ℝ)
    (Hprice :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      ∀j∈List.range depth,
        |((actualGeneralFourCenteredForest bf hf hs hU W j [st]).map
          (actualGeneralFourRecursionError bf hf hs hU W)).sum|≤budget j)
    (Hterminal :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      |((actualGeneralFourCenteredForest bf hf hs hU W depth [st]).map
        (actualGeneralFourStateResponse (n:=n) bf hf U W)).sum|≤terminalBudget)
    (Hfrozen :
      let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (hi.trans (hs.le.trans hU))
      |actualGeneralFourStateResponse (n:=n) bf hf U W st.freeze|≤frozenBudget) :
    |actualGeneralTargetLongitudinalResponse (n:=n) bf hf as i U|≤
      ((List.range depth).map budget).sum+terminalBudget+frozenBudget := by
  rw [actual_general_target_response_eq_four_iteration (n:=n) bf hf hbf hhf as W i star U hi hs hU ho
    hW hstarK depth]
  exact (abs_sub _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add
      (actual_general_four_residual_sum_bound bf hf hs hU W depth _ budget Hprice) Hterminal)) Hfrozen)

end OAI.SKFluctuations.Cavity
