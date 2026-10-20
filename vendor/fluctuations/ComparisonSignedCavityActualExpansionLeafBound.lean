module

public import ComparisonSignedCavityActualExpansionVariation

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass} {i star U : ℕ}

theorem nativeActualResourceExpansion_leaves_le
    (Γ : (st : NativeHighSwitchState S as) → MarkedPlacement st.tree → ℝ)
    (hs : star<U) (hl : star≤as.length) (ops : List NativeActualExpansionOp)
    (st Q : NativeActualResourceState S as i star) {r : ℕ} (hr : st.tree.leaves≤r)
    (hQ : Q∈nativeActualResourceExpansion Γ hs hl ops st) :
    Q.tree.leaves≤r+2*ops.length := by
  induction ops generalizing st r with
  | nil=>obtain rfl:=List.mem_singleton.mp hQ;simpa using hr
  | cons op ops ih=>
    obtain ⟨P,hP,hQ⟩:=List.mem_flatMap.mp hQ
    have H:=ih P (nativeActualResourceStep_leaves_le Γ hs hl op st P hr hP) hQ
    simp only [List.length_cons]
    omega

theorem nativeActualWeightedTerminalSum_abs_le {α : Type} (L : List α)
    (c F : α→ℝ) {B : ℝ} (hF : ∀q∈L,|F q|≤B) :
    |(L.map (fun q=>c q*F q)).sum|≤(L.map (fun q=>|c q|)).sum*B := by
  have Habs : |(L.map (fun q=>c q*F q)).sum|≤(L.map (fun q=>|c q*F q|)).sum := by
    induction L with
    | nil=>simp
    | cons q L ih=>
      simp only [List.map_cons,List.sum_cons]
      exact (abs_add_le _ _).trans (add_le_add (le_refl _)
        (ih (fun q hq=>hF q (List.mem_cons_of_mem _ hq))))
  apply Habs.trans
  rw [←List.sum_map_mul_right]
  apply List.sum_le_sum
  intro q hq
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hF q hq) (abs_nonneg _)

end OAI.SKFluctuations.Hierarchy.ClockTree
