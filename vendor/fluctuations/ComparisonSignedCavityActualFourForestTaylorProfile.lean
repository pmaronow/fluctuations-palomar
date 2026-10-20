module

public import ComparisonSignedCavityActualFourForestTaylorVariation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open Cavity MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

theorem nativeActualFourCenteredForest_profile_and_constant_sum_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0→|Γ st p| ≤ 1)
    (hs : star<U) (hl : star ≤ as.length)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    {C W BH BL : ℝ} (hC : 0 ≤ C) (hw : ∀st tag,|weight st tag| ≤ C)
    (hW : 0 ≤ W) (hBH : 0 ≤ BH) (hBL : 0 ≤ BL)
    (depth : ℕ) (xs : List (NativeActualResourceState S as i star))
    (r : ℕ) (hr : ∀Q∈xs,Q.tree.leaves ≤ r)
    (f R : ℕ→ℝ) (hf : ∀j,0 ≤ f j) (hR : ∀j,0 ≤ R j)
    (hflo : ∀j,j<U→f j=0) (hRlo : ∀j,j<U→R j=0)
    (F : NativeActualResourceState S as i star→ℝ)
    (Hrows : ∀Q∈nativeActualFourCenteredForest Γ hs hl weight depth xs,
      |F Q| ≤ |Q.term.coefficient| *(BH*(Q.tree.forkCost f+edgeBudget 0 as f+
        W*(Q.tree.forkCost R+edgeBudget 0 as R))+BL)) :
    ((nativeActualFourCenteredForest Γ hs hl weight depth xs).map (fun Q=>|F Q|)).sum ≤
      2*BH*nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches C 3 r depth*
        ((xs.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum+
          W*(xs.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R))).sum)+
      2*BL*nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches C 3 r depth*
        (xs.map (fun Q=>|Q.term.coefficient|)).sum := by
  let rows:=nativeActualFourCenteredForest Γ hs hl weight depth xs
  have Hf:=nativeActualFourCenteredForest_wholeProfile_le ho Γ hΓ hs hl weight hC hw depth xs r hr f hf hflo
  have HR:=nativeActualFourCenteredForest_wholeProfile_le ho Γ hΓ hs hl weight hC hw depth xs r hr R hR hRlo
  have HC:=nativeActualFourCenteredForest_coefficient_variation_le ho Γ hΓ hs hl weight hC hw depth xs r hr
  have Hsum : (rows.map (fun Q=>|F Q|)).sum ≤
      BH*((rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum+
        W*(rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R))).sum)+
      BL*(rows.map (fun Q=>|Q.term.coefficient|)).sum:=by
    apply (List.sum_le_sum Hrows).trans_eq
    simp only [←List.sum_map_mul_left,←List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro Q hQ
    ring
  apply Hsum.trans
  have H:=add_le_add
    (mul_le_mul_of_nonneg_left (add_le_add Hf (mul_le_mul_of_nonneg_left HR hW)) hBH)
    (mul_le_mul_of_nonneg_left HC hBL)
  convert H using 1
  ring

end OAI.SKFluctuations.Hierarchy.ClockTree
