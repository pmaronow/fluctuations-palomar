module

public import ComparisonSignedCavityActualWeightedRecursion
public import ComparisonSignedCavityActualExpansionLeafBound

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

def nativeActualWeightedBranchCost (branches : NativeActualWeightedBranches) (C : ℝ) (r : ℕ) : ℝ :=
  C*(branches.map (fun b=>nativeActualExpansionVariation r b.2)).sum

def nativeActualWeightedFrontierCost (branches : NativeActualWeightedBranches) (C : ℝ) (L r : ℕ) : ℕ→ℝ
  | 0=>1
  | depth+1=>nativeActualWeightedFrontierCost branches C L r depth*
      nativeActualWeightedBranchCost branches C (r+2*depth*L)

theorem nativeActualWeightedBranchCost_nonneg
    (branches : NativeActualWeightedBranches) {C : ℝ} (hC : 0≤C) (r : ℕ) :
    0≤nativeActualWeightedBranchCost branches C r := by
  apply mul_nonneg hC
  apply List.sum_nonneg
  intro x hx
  obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hx
  exact nativeActualExpansionVariation_nonneg _ _

theorem nativeActualWeightedFrontierCost_nonneg
    (branches : NativeActualWeightedBranches) {C : ℝ} (hC : 0≤C) (L r depth : ℕ) :
    0≤nativeActualWeightedFrontierCost branches C L r depth := by
  induction depth with
  | zero=>exact zero_le_one
  | succ depth ih=>exact mul_nonneg ih (nativeActualWeightedBranchCost_nonneg branches hC _)

theorem nativeActualWeightedBranchStep_leaves_le
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (L : ℕ) (hL : ∀b∈branches,b.2.length≤L)
    (st Q : NativeActualResourceState S as i star) {r : ℕ} (hr : st.tree.leaves≤r)
    (hQ : Q∈nativeActualWeightedBranchStep Γ hs hl branches weight st) :
    Q.tree.leaves≤r+2*L := by
  obtain ⟨b,hb,hQ⟩:=List.mem_flatMap.mp hQ
  obtain ⟨P,hP,rfl⟩:=List.mem_map.mp hQ
  have HP:=nativeActualResourceExpansion_leaves_le Γ hs hl b.2 st P hr hP
  have HB:=hL b hb
  change P.tree.leaves≤r+2*L
  omega

theorem nativeActualWeightedFrontier_leaves_le
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (L : ℕ) (hL : ∀b∈branches,b.2.length≤L)
    (depth : ℕ) (st Q : NativeActualResourceState S as i star) {r : ℕ} (hr : st.tree.leaves≤r)
    (hQ : Q∈nativeActualWeightedFrontier Γ hs hl branches weight depth st) :
    Q.tree.leaves≤r+2*depth*L := by
  induction depth generalizing Q with
  | zero=>obtain rfl:=List.mem_singleton.mp hQ;simpa using hr
  | succ depth ih=>
    obtain ⟨P,hP,hQ⟩:=List.mem_flatMap.mp hQ
    have HQ:=nativeActualWeightedBranchStep_leaves_le Γ hs hl branches weight L hL P Q (ih P hP) hQ
    nlinarith

theorem nativeActualWeightedBranchStep_coefficient_variation_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0→|Γ st p|≤1)
    (hs : star<U) (hl : star≤as.length) (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    {C : ℝ} (hC : 0≤C) (hw : ∀st b,b∈branches→|weight st b.1|≤C)
    (st : NativeActualResourceState S as i star) {r : ℕ} (hr : st.tree.leaves≤r) :
    ((nativeActualWeightedBranchStep Γ hs hl branches weight st).map
      (fun Q=>|Q.term.coefficient|)).sum≤|st.term.coefficient| *nativeActualWeightedBranchCost branches C r := by
  simp only [nativeActualWeightedBranchStep,List.map_flatMap,native_sum_flatMap,List.map_map,
    Function.comp_def,NativeActualResourceState.reweight,NativeResourceTerm.reweight,abs_mul,
    List.sum_map_mul_left]
  have HB b (hb : b∈branches) :
      |weight st b.1| *((nativeActualResourceExpansion Γ hs hl b.2 st).map
        (fun Q=>|Q.term.coefficient|)).sum≤C*(|st.term.coefficient| *nativeActualExpansionVariation r b.2) := by
    have HP:=nativeActualResourceExpansion_coefficient_variation_le ho Γ hΓ hs hl b.2 st hr
    apply mul_le_mul (hw st b hb) HP _ hC
    apply List.sum_nonneg
    intro x hx
    obtain ⟨Q,hQ,rfl⟩:=List.mem_map.mp hx
    exact abs_nonneg _
  apply (List.sum_le_sum HB).trans
  simp only [List.sum_map_mul_left,nativeActualWeightedBranchCost]
  ring_nf
  exact le_refl _

theorem nativeActualWeightedFrontier_coefficient_variation_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0→|Γ st p|≤1)
    (hs : star<U) (hl : star≤as.length) (branches : NativeActualWeightedBranches)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    {C : ℝ} (hC : 0≤C) (hw : ∀st b,b∈branches→|weight st b.1|≤C)
    (L : ℕ) (hL : ∀b∈branches,b.2.length≤L)
    (depth : ℕ) (st : NativeActualResourceState S as i star) {r : ℕ} (hr : st.tree.leaves≤r) :
    ((nativeActualWeightedFrontier Γ hs hl branches weight depth st).map
      (fun Q=>|Q.term.coefficient|)).sum≤|st.term.coefficient| *nativeActualWeightedFrontierCost branches C L r depth := by
  induction depth with
  | zero=>simp [nativeActualWeightedFrontier,nativeActualWeightedFrontierCost]
  | succ depth ih=>
    simp only [nativeActualWeightedFrontier,List.map_flatMap,native_sum_flatMap]
    have HB Q (hQ : Q∈nativeActualWeightedFrontier Γ hs hl branches weight depth st) :=
      nativeActualWeightedBranchStep_coefficient_variation_le ho Γ hΓ hs hl branches weight hC hw Q
        (nativeActualWeightedFrontier_leaves_le Γ hs hl branches weight L hL depth st Q hr hQ)
    apply (List.sum_le_sum HB).trans
    rw [List.sum_map_mul_right]
    have H:=mul_le_mul_of_nonneg_right ih
      (nativeActualWeightedBranchCost_nonneg branches hC (r+2*depth*L))
    simpa only [nativeActualWeightedFrontierCost,mul_assoc] using H

end OAI.SKFluctuations.Hierarchy.ClockTree
