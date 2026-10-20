module

public import ComparisonSignedCavityActualWeightedHighProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open Cavity MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 18000000
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

theorem nativeActualFourCenteredForest_eq_frontiers
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hs : star < U) (hl : star ≤ as.length)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (depth : ℕ) (xs : List (NativeActualResourceState S as i star)) :
    nativeActualFourCenteredForest Γ hs hl weight depth xs=
      (xs.flatMap (fun Q=>[Q,Q.freeze])).flatMap
        (nativeActualWeightedFrontier Γ hs hl nativeActualOriginalFourGCenteredBranches weight depth) := by
  induction depth with
  | zero=>simp [nativeActualFourCenteredForest,nativeActualWeightedFrontier]
  | succ depth ih=>
    simp only [nativeActualFourCenteredForest,ih,nativeActualWeightedFrontier,List.flatMap_assoc]

theorem nativeActualFourCenteredForest_wholeProfile_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0→|Γ st p|≤1)
    (hs : star < U) (hl : star ≤ as.length)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀st tag,|weight st tag|≤C)
    (depth : ℕ) (xs : List (NativeActualResourceState S as i star))
    (r : ℕ) (hr : ∀Q∈xs,Q.tree.leaves≤r)
    (f : ℕ→ℝ) (hf : ∀j,0≤f j) (hlo : ∀j,j<U→f j=0) :
    ((nativeActualFourCenteredForest Γ hs hl weight depth xs).map
      (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum ≤
      2*nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches C 3 r depth*
        (xs.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum := by
  rw [nativeActualFourCenteredForest_eq_frontiers]
  rw [List.map_flatMap,native_sum_flatMap]
  have Hr Q (hQ : Q∈xs.flatMap (fun Q=>[Q,Q.freeze])) : Q.tree.leaves≤r := by
    obtain ⟨P,hP,hQ⟩:=List.mem_flatMap.mp hQ
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hQ
    rcases hQ with hQ|hQ
    · subst Q; exact hr _ hP
    · subst Q; exact hr P hP
  have HB Q (hQ : Q∈xs.flatMap (fun Q=>[Q,Q.freeze])):=
    nativeActualWeightedFrontier_wholeProfile_le ho Γ hΓ hs hl
      nativeActualOriginalFourGCenteredBranches weight hC (fun st b _=>hw st b.1)
      3 nativeActualOriginalFourGCenteredBranches_length depth Q (Hr Q hQ) f hf hlo
  apply (List.sum_le_sum HB).trans
  simp only [List.map_flatMap,native_sum_flatMap,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,NativeActualResourceState.freeze,NativeResourceTerm.freeze,abs_neg]
  have HE : (xs.map (fun Q=>|Q.term.coefficient| *
        nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches C 3 r depth*
        (Q.tree.forkCost f+edgeBudget 0 as f)+|Q.term.coefficient| *
        nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches C 3 r depth*
        (Q.tree.forkCost f+edgeBudget 0 as f))).sum=
      2*nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches C 3 r depth*
        (xs.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum := by
    rw [←List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro Q hQ
    ring
  exact HE.le

theorem nativeActualFourCenteredForest_leaves_bound
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hs : star < U) (hl : star ≤ as.length)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (depth : ℕ) (xs : List (NativeActualResourceState S as i star))
    (r : ℕ) (hr : ∀Q∈xs,Q.tree.leaves≤r)
    (Q : NativeActualResourceState S as i star)
    (hQ : Q∈nativeActualFourCenteredForest Γ hs hl weight depth xs) :
    Q.tree.leaves≤r+6*depth := by
  rw [nativeActualFourCenteredForest_eq_frontiers] at hQ
  obtain ⟨P,hP,hQ⟩:=List.mem_flatMap.mp hQ
  have HP : P.tree.leaves≤r := by
    obtain ⟨R,hR,hP⟩:=List.mem_flatMap.mp hP
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hP
    rcases hP with hP|hP
    · subst P; exact hr _ hR
    · subst P; exact hr R hR
  have H:=nativeActualWeightedFrontier_leaves_le Γ hs hl nativeActualOriginalFourGCenteredBranches
    weight 3 nativeActualOriginalFourGCenteredBranches_length depth P Q HP hQ
  omega

theorem nativeActualFourCenteredForest_generation_bound
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hs : star < U) (hl : star ≤ as.length)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    (depth : ℕ) (xs : List (NativeActualResourceState S as i star))
    (k : ℕ) (hk : ∀Q∈xs,Q.generation=k)
    (Q : NativeActualResourceState S as i star)
    (hQ : Q∈nativeActualFourCenteredForest Γ hs hl weight depth xs) :
    Q.generation=k+depth := by
  rw [nativeActualFourCenteredForest_eq_frontiers] at hQ
  obtain ⟨P,hP,hQ⟩:=List.mem_flatMap.mp hQ
  have HP : P.generation=k := by
    obtain ⟨R,hR,hP⟩:=List.mem_flatMap.mp hP
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hP
    rcases hP with hP|hP
    · subst P; exact hk _ hR
    · subst P; exact hk R hR
  have H:=nativeActualWeightedFrontier_generation Γ hs hl nativeActualOriginalFourGCenteredBranches
    weight 1 nativeActualOriginalFourGCenteredBranches_marked depth P Q hQ
  simpa only [HP,Nat.mul_one] using H

end OAI.SKFluctuations.Hierarchy.ClockTree
