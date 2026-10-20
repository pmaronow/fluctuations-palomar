module

public import ComparisonSignedCavityActualConstantJointFourReadout
public import ComparisonSignedCavityActualConstantGeneratedFourTerminalAlong
public import ComparisonSignedCavityActualFourForestNumerics

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open Cavity LaplaceWindowFormalization

theorem nativeActualFourCenteredForest_eq_flatMap_singletons
    {S : Type} {as : List PositiveMass} {i star U : ℕ}
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hs : star < U) (hl : star≤as.length)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (depth : ℕ) (xs : List (NativeActualResourceState S as i star)) :
    nativeActualFourCenteredForest Γ hs hl weight depth xs=
      xs.flatMap (fun Q=>nativeActualFourCenteredForest Γ hs hl weight depth [Q]) := by
  induction depth with
  | zero=>simp only [nativeActualFourCenteredForest,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  | succ depth ih=>simp only [nativeActualFourCenteredForest,ih,List.flatMap_assoc]

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 24000000

theorem actual_constant_source_children_centered_terminal_abs_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Temp B : ℝ}
    {as : List PositiveMass} {star U : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Temp)
    (ho : MassOrdered 0 as) (hs : star < U) (hU : U≤as.length)
    (W : ℝ) (depth : ℕ) (hB : 0≤B)
    (H : ∀Q∈nativeActualConstantSourceChildren M as star U hs hU,
      |((nativeActualMinimumFourCenteredForest M hs hU W depth [Q]).map
        (nativeActualMinimumFourStateResponse M U W)).sum| ≤ 2*|Q.term.coefficient| *B) :
    |((nativeActualMinimumFourCenteredForest M hs hU W depth
      (nativeActualConstantSourceChildren M as star U hs hU)).map
      (nativeActualMinimumFourStateResponse M U W)).sum| ≤ 12*B := by
  let xs:=nativeActualConstantSourceChildren M as star U hs hU
  let F:=fun (Q : NativeActualResourceState (Spin n×Bool) as 0 star)=>(nativeActualMinimumFourCenteredForest M hs hU W depth [Q]).map
    (nativeActualMinimumFourStateResponse M U W)
  have HD : nativeActualMinimumFourCenteredForest M hs hU W depth xs=
      xs.flatMap (fun Q=>nativeActualMinimumFourCenteredForest M hs hU W depth [Q]):=by
    unfold nativeActualMinimumFourCenteredForest
    exact nativeActualFourCenteredForest_eq_flatMap_singletons _ _ _ _ _ _
  change |((nativeActualMinimumFourCenteredForest M hs hU W depth xs).map
    (nativeActualMinimumFourStateResponse M U W)).sum| ≤ _
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
  have HC:=nativeActualConstantSourceChildren_coefficient_variation M htotal ho hs hU
  change (xs.map (fun Q=>|Q.term.coefficient|)).sum≤6 at HC
  nlinarith [mul_le_mul_of_nonneg_right HC hB]

def ActualOriginalConstantSourceChildrenFourTerminalSavingAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (saving : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn in atTop,∀us : List PositiveMass,
    (∀u∈us,u.val≤1)→(w n).star∈us→∀ᶠj in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀(U : ℕ) (hs : star < U) (hU : U≤as.length),
      |((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
        (nativeActualConstantSourceChildren (M n) as star U hs hU)).map
        (nativeActualMinimumFourStateResponse (M n) U (W n))).sum| ≤
        12*(((dim n+1:ℕ):ℝ)^(-saving)*(M n).xs^2)

theorem ActualOriginalConstantGeneratedFourGCenteredTerminalSavingAlong.source_children
    {m delta cl cu Az C0 Ct D Bclock Temp saving : ℝ} {depth : ℕ} {dim : ℕ→ℕ}
    {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (H : ActualOriginalConstantGeneratedFourGCenteredTerminalSavingAlong 3 depth saving M W w)
    (htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤Temp) :
    ActualOriginalConstantSourceChildrenFourTerminalSavingAlong depth saving M W w := by
  filter_upwards [H,htotal] with n hn hntotal
  intro us hus hstar
  filter_upwards [hn us hus hstar] with j hj
  dsimp only at hj ⊢
  intro U hs hU
  apply actual_constant_source_children_centered_terminal_abs_le (M n) hntotal
    (finiteCutMasses_ordered us hus j) hs hU (W n) depth (by positivity)
  intro Q hQ
  exact hj U 0 (Nat.zero_le _) hs hU Q
    (nativeActualConstantSourceChildren_valid (M n) hs hU Q hQ)
    (nativeActualConstantSourceChildren_generation (M n) hs hU Q hQ)
    (nativeActualConstantSourceChildren_leaves (M n) hs hU Q hQ)

theorem exists_actual_constant_source_children_four_terminal_of_pair_budgets_along
    {m delta cl cu Az C0 Ct D Bclock Temp gamma cK : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hTemp : 0≤Temp) (hgamma : 0 < gamma) (hcK : 0 < cK)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n)
    (htotal : ∀ᶠn in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤Temp)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,cK*W n≤actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val)
    (Hp : ∀degree : ℕ,0 < degree→∃A : ℝ,1≤A ∧
      ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong degree A gamma M W w) :
    ∃threshold : ℕ,0 < threshold ∧ ∃saving : ℝ,0 < saving ∧
      ∀depth : ℕ,threshold≤depth→
        ActualOriginalConstantSourceChildrenFourTerminalSavingAlong depth saving M W w := by
  obtain ⟨threshold,hthreshold,saving,hsaving,H⟩:=
    exists_actual_original_constant_generated_four_G_centered_terminal_decay_of_pair_budgets_along
      hm hC0 hTemp hgamma hcK 3 dim hdim M W hxs htotal w hw Hp
  exact ⟨threshold,hthreshold,saving,hsaving,fun depth hd=>(H depth hd).source_children htotal⟩

end OAI.SKFluctuations.Cavity
