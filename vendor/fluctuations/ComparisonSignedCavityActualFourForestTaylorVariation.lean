module

public import ComparisonSignedCavityActualFourForestHighProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open Cavity MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 18000000
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

theorem nativeActualFourCenteredForest_coefficient_variation_le
    (ho : MassOrdered 0 as)
    (Γ : (st : NativeHighSwitchState S as)→MarkedPlacement st.tree→ℝ)
    (hΓ : ∀st p,p∈st.tree.markedAttach 0→|Γ st p| ≤ 1)
    (hs : star<U) (hl : star ≤ as.length)
    (weight : NativeActualResourceState S as i star→ℕ→ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hw : ∀st tag,|weight st tag| ≤ C)
    (depth : ℕ) (xs : List (NativeActualResourceState S as i star))
    (r : ℕ) (hr : ∀Q∈xs,Q.tree.leaves ≤ r) :
    ((nativeActualFourCenteredForest Γ hs hl weight depth xs).map
      (fun Q=>|Q.term.coefficient|)).sum ≤
      2*nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches C 3 r depth*
        (xs.map (fun Q=>|Q.term.coefficient|)).sum := by
  rw [nativeActualFourCenteredForest_eq_frontiers,List.map_flatMap,native_sum_flatMap]
  have Hr Q (hQ : Q∈xs.flatMap (fun Q=>[Q,Q.freeze])) : Q.tree.leaves ≤ r:=by
    obtain ⟨P,hP,hQ⟩:=List.mem_flatMap.mp hQ
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hQ
    rcases hQ with hQ|hQ
    · subst Q;exact hr P hP
    · subst Q;exact hr P hP
  have HB Q (hQ : Q∈xs.flatMap (fun Q=>[Q,Q.freeze])):=
    nativeActualWeightedFrontier_coefficient_variation_le ho Γ hΓ hs hl
      nativeActualOriginalFourGCenteredBranches weight hC (fun st b _=>hw st b.1)
      3 nativeActualOriginalFourGCenteredBranches_length depth Q (Hr Q hQ)
  apply (List.sum_le_sum HB).trans_eq
  simp only [List.map_flatMap,native_sum_flatMap,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,NativeActualResourceState.freeze,NativeResourceTerm.freeze,abs_neg]
  rw [←List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro Q hQ
  ring

end OAI.SKFluctuations.Hierarchy.ClockTree
