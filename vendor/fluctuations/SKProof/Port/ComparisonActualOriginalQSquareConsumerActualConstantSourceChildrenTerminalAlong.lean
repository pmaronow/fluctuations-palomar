module

public import ComparisonSignedCavityActualConstantSourceChildrenTerminalAlong
public import SKProof.Port.ComparisonActualOriginalQSquareConsumerActualConstantGeneratedFourTerminalAlong

@[expose] public section
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum (ActualSlowWindowChoice)
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open Cavity LaplaceWindowFormalization

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualThetaZeroOverlapMinimum
set_option maxHeartbeats 24000000

theorem actual_constant_source_children_centered_terminal_abs_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp B : ℝ}
    {as : List PositiveMass} {star U : ℕ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤ Temp)
    (ho : MassOrdered 0 as) (hs : star < U) (hU : U≤ as.length)
    (W : ℝ) (depth : ℕ) (hB : 0≤ B)
    (H : ∀Q∈nativeActualConstantSourceChildren_original_q M as star U hs hU,
      |((nativeActualMinimumFourCenteredForest_original_q M hs hU W depth [Q]).map
        (nativeActualMinimumFourStateResponse_original_q M U W)).sum| ≤ 2*|Q.term.coefficient| *B) :
    |((nativeActualMinimumFourCenteredForest_original_q M hs hU W depth
      (nativeActualConstantSourceChildren_original_q M as star U hs hU)).map
      (nativeActualMinimumFourStateResponse_original_q M U W)).sum| ≤ 12*B := by
  let xs:=nativeActualConstantSourceChildren_original_q M as star U hs hU
  let F:=fun (Q : NativeActualResourceState (Spin n×Bool) as 0 star)=>(nativeActualMinimumFourCenteredForest_original_q M hs hU W depth [Q]).map
    (nativeActualMinimumFourStateResponse_original_q M U W)
  have HD : nativeActualMinimumFourCenteredForest_original_q M hs hU W depth xs=
      xs.flatMap (fun Q=>nativeActualMinimumFourCenteredForest_original_q M hs hU W depth [Q]):=by
    unfold nativeActualMinimumFourCenteredForest_original_q
    exact nativeActualFourCenteredForest_eq_flatMap_singletons _ _ _ _ _ _
  change |((nativeActualMinimumFourCenteredForest_original_q M hs hU W depth xs).map
    (nativeActualMinimumFourStateResponse_original_q M U W)).sum| ≤ _
  rw [HD,List.map_flatMap,native_sum_flatMap]
  apply (native_abs_sum_map_le xs (fun Q=>(F Q).sum)).trans
  have Hsum : (xs.map (fun Q=>|(F Q).sum|)).sum ≤
      (xs.map (fun Q=>2*|Q.term.coefficient| *B)).sum:=List.sum_le_sum H
  have HE : (xs.map (fun Q=>2*|Q.term.coefficient| *B)).sum=
      2*((xs.map (fun Q=>|Q.term.coefficient|)).sum)*B:=by
    induction xs with
    | nil=>simp
    | cons Q qs ih=>simp only [List.map_cons,List.sum_cons,ih];ring
  apply Hsum.trans
  rw [HE]
  have HC:=nativeActualConstantSourceChildren_coefficient_variation_original_q M htotal ho hs hU
  change (xs.map (fun Q=>|Q.term.coefficient|)).sum≤6 at HC
  nlinarith [mul_le_mul_of_nonneg_right HC hB]

def ActualOriginalConstantSourceChildrenFourTerminalSavingAlong_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (saving : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn in atTop,∀us : List PositiveMass,
    (∀u∈us,u.val≤1)→(w n).star∈us→∀ᶠj in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀(U : ℕ) (hs : star < U) (hU : U≤ as.length),
      |((nativeActualMinimumFourCenteredForest_original_q (M n) hs hU (W n) depth
        (nativeActualConstantSourceChildren_original_q (M n) as star U hs hU)).map
        (nativeActualMinimumFourStateResponse_original_q (M n) U (W n))).sum| ≤
        12*(((dim n+1:ℕ):ℝ)^(-saving)*(M n).xs^2)

theorem ActualOriginalConstantGeneratedFourGCenteredTerminalSavingAlong_original_q.source_children_original_q
    {m delta cl cu Az C0 Ct D Bclock Temp saving : ℝ} {depth : ℕ} {dim : ℕ→ℕ}
    {M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (H : ActualOriginalConstantGeneratedFourGCenteredTerminalSavingAlong_original_q 3 depth saving M W w)
    (htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤ Temp) :
    ActualOriginalConstantSourceChildrenFourTerminalSavingAlong_original_q depth saving M W w := by
  filter_upwards [H,htotal] with n hn hntotal
  intro us hus hstar
  filter_upwards [hn us hus hstar] with j hj
  dsimp only at hj ⊢
  intro U hs hU
  apply actual_constant_source_children_centered_terminal_abs_le_original_q (M n) hntotal
    (finiteCutMasses_ordered us hus j) hs hU (W n) depth (by positivity)
  intro Q hQ
  exact hj U 0 (Nat.zero_le _) hs hU Q
    (nativeActualConstantSourceChildren_valid_original_q (M n) hs hU Q hQ)
    (nativeActualConstantSourceChildren_generation_original_q (M n) hs hU Q hQ)
    (nativeActualConstantSourceChildren_leaves_original_q (M n) hs hU Q hQ)

theorem exists_actual_constant_source_children_four_terminal_of_pair_budgets_along_original_q
    {m delta cl cu Az C0 Ct D Bclock Temp gamma cK : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hTemp : 0≤ Temp) (hgamma : 0 < gamma) (hcK : 0 < cK)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤ W n)
    (htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤ Temp)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,cK*W n≤ actualMixedClock (dim n+1) (M n).sweepBf (M n).sweepHf (w n).star.val)
    (Hp : ∀degree : ℕ,0 < degree→∃A : ℝ,1≤ A ∧
      ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong_original_q degree A gamma M W w) :
    ∃threshold : ℕ,0 < threshold ∧ ∃saving : ℝ,0 < saving ∧
      ∀depth : ℕ,threshold≤ depth→
        ActualOriginalConstantSourceChildrenFourTerminalSavingAlong_original_q depth saving M W w := by
  obtain ⟨threshold,hthreshold,saving,hsaving,H⟩:=
    exists_actual_original_constant_generated_four_G_centered_terminal_decay_of_pair_budgets_along_original_q
      hm hC0 hTemp hgamma hcK 3 dim hdim M W hxs htotal w hw Hp
  exact ⟨threshold,hthreshold,saving,hsaving,fun depth hd=>(H depth hd).source_children_original_q htotal⟩

end OAI.SKFluctuations.Cavity
