module

public import ComparisonSignedCavityActualWeightedVariation
public import ComparisonSignedCavityActualOriginalHighProfileHistory
public import ComparisonSignedCavityActualFourResourceForest

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

def nativeActualWeightedProfileBranchCost (branches : NativeActualWeightedBranches) (C : ℝ) (r : ℕ) : ℝ :=
  C*(branches.map (fun b=>nativeActualProfileVariation r b.2)).sum

def nativeActualWeightedProfileFrontierCost (branches : NativeActualWeightedBranches) (C : ℝ) (L r : ℕ) : ℕ→ℝ
  | 0=>1
  | depth+1=>nativeActualWeightedProfileFrontierCost branches C L r depth*
      nativeActualWeightedProfileBranchCost branches C (r+2*depth*L)

theorem nativeActualWeightedProfileBranchCost_nonneg
    (branches : NativeActualWeightedBranches) {C : ℝ} (hC : 0≤C) (r : ℕ) :
    0≤nativeActualWeightedProfileBranchCost branches C r := by
  apply mul_nonneg hC
  apply List.sum_nonneg
  intro x hx
  obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hx
  exact nativeActualProfileVariation_nonneg _ _

theorem nativeActualWeightedProfileFrontierCost_nonneg
    (branches : NativeActualWeightedBranches) {C : ℝ} (hC : 0≤C) (L r depth : ℕ) :
    0≤nativeActualWeightedProfileFrontierCost branches C L r depth := by
  induction depth with
  | zero=>exact zero_le_one
  | succ depth ih=>exact mul_nonneg ih (nativeActualWeightedProfileBranchCost_nonneg branches hC _)

theorem nativeActualWeightedBranchStep_wholeProfile_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0→|Γ st p|≤1)
    (hs : star<U) (hl : star≤as.length) (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    {C : ℝ} (hC : 0≤C) (hw : ∀st b,b∈branches→|weight st b.1|≤C)
    (st : NativeActualResourceState S as i star) {r : ℕ} (hr : st.tree.leaves≤r)
    (f : ℕ→ℝ) (hf : ∀j,0≤f j) (hlo : ∀j,j<U→f j=0) :
    ((nativeActualWeightedBranchStep Γ hs hl branches weight st).map
      (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum≤|st.term.coefficient| *nativeActualWeightedProfileBranchCost branches C r*(st.tree.forkCost f+edgeBudget 0 as f) := by
  simp only [nativeActualWeightedBranchStep,List.map_flatMap,native_sum_flatMap,List.map_map,
    Function.comp_def,NativeActualResourceState.reweight,NativeResourceTerm.reweight,abs_mul,mul_assoc,
    List.sum_map_mul_left]
  have HB b (hb : b∈branches) :
      |weight st b.1| *((nativeActualResourceExpansion Γ hs hl b.2 st).map
        (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum≤C*(|st.term.coefficient| *nativeActualProfileVariation r b.2*(st.tree.forkCost f+edgeBudget 0 as f)) := by
    have HP:=nativeActualResourceExpansion_wholeProfile_le ho Γ hΓ hs hl b.2 st r hr f hf hlo
    apply mul_le_mul (hw st b hb) HP _ hC
    apply List.sum_nonneg
    intro x hx
    obtain ⟨Q,hQ,rfl⟩:=List.mem_map.mp hx
    exact mul_nonneg (abs_nonneg _) (add_nonneg (Q.tree.forkCost_nonneg hf) (edgeBudget_nonneg ho hf))
  refine le_trans (List.sum_le_sum HB) ?_
  simp only [List.sum_map_mul_left,List.sum_map_mul_right,nativeActualWeightedProfileBranchCost]
  apply le_of_eq
  ring

theorem nativeActualWeightedFrontier_wholeProfile_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0→|Γ st p|≤1)
    (hs : star<U) (hl : star≤as.length) (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    {C : ℝ} (hC : 0≤C) (hw : ∀st b,b∈branches→|weight st b.1|≤C)
    (L : ℕ) (hL : ∀b∈branches,b.2.length≤L)
    (depth : ℕ) (st : NativeActualResourceState S as i star) {r : ℕ} (hr : st.tree.leaves≤r)
    (f : ℕ→ℝ) (hf : ∀j,0≤f j) (hlo : ∀j,j<U→f j=0) :
    ((nativeActualWeightedFrontier Γ hs hl branches weight depth st).map
      (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum≤|st.term.coefficient| *nativeActualWeightedProfileFrontierCost branches C L r depth*(st.tree.forkCost f+edgeBudget 0 as f) := by
  induction depth with
  | zero=>simp [nativeActualWeightedFrontier,nativeActualWeightedProfileFrontierCost]
  | succ depth ih=>
    simp only [nativeActualWeightedFrontier,List.map_flatMap,native_sum_flatMap]
    have HB Q (hQ : Q∈nativeActualWeightedFrontier Γ hs hl branches weight depth st) :=
      nativeActualWeightedBranchStep_wholeProfile_le ho Γ hΓ hs hl branches weight hC hw Q
        (nativeActualWeightedFrontier_leaves_le Γ hs hl branches weight L hL depth st Q hr hQ) f hf hlo
    apply (List.sum_le_sum HB).trans
    have Hsum : ((nativeActualWeightedFrontier Γ hs hl branches weight depth st).map
        (fun Q=>|Q.term.coefficient| *nativeActualWeightedProfileBranchCost branches C (r+2*depth*L)*
          (Q.tree.forkCost f+edgeBudget 0 as f))).sum=
        ((nativeActualWeightedFrontier Γ hs hl branches weight depth st).map
          (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum*
            nativeActualWeightedProfileBranchCost branches C (r+2*depth*L) := by
      rw [←List.sum_map_mul_right]
      congr 1
      apply List.map_congr_left
      intro Q hQ
      ring
    rw [Hsum]
    have H:=mul_le_mul_of_nonneg_right ih
      (nativeActualWeightedProfileBranchCost_nonneg branches hC (r+2*depth*L))
    simpa only [nativeActualWeightedProfileFrontierCost,mul_assoc,mul_left_comm,mul_comm] using H

end OAI.SKFluctuations.Hierarchy.ClockTree
