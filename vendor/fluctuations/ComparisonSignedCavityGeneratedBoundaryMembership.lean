module

public import ComparisonSignedCavityGeneratedTestAncestry
public import ComparisonSignedCavityActualBoundaryLayerBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type*} {as : List PositiveMass} {T : ClockTree S as}

theorem NativeTestGenerated.edge_not_both_occupied {i star U cut : ℕ}
    {P : NativeGeneratedTest T} (hP : NativeTestGenerated i star T P)
    (hi : i ≤ star) (hstar : star < U) (hU : U ≤ cut)
    (s : T.Slot) (e : T.Slot × T.Slot) (he : e ∈ P.edges) :
    ¬(cut ≤ T.splitIndex s e.1 ∧ cut ≤ T.splitIndex s e.2) := by
  intro H
  have hleft : cut ≤ T.splitIndex e.1 s := by rw [T.splitIndex_symm];exact H.1
  have hhigh := T.splitIndex_cut_trans cut e.1 s e.2 hleft H.2
  exact (not_le.mpr ((hP.edges_boundary hi hstar e he).trans_le hU)) hhigh

def NativeGeneratedTest.boundaryAnchor (P : NativeGeneratedTest T)
    (s : T.Slot) (cut : ℕ) (e : Fin P.edges.length) : T.Slot :=
  if cut ≤ T.splitIndex s (P.edges.get e).1 then (P.edges.get e).2 else (P.edges.get e).1

def NativeGeneratedTest.boundaryTarget (P : NativeGeneratedTest T)
    (s : T.Slot) (cut : ℕ) (e : Fin P.edges.length) : T.Slot :=
  if cut ≤ T.splitIndex s (P.edges.get e).1 then (P.edges.get e).1 else (P.edges.get e).2

theorem NativeTestGenerated.boundaryAnchor_departed {i star U cut : ℕ}
    {P : NativeGeneratedTest T} (hP : NativeTestGenerated i star T P)
    (hi : i ≤ star) (hstar : star < U) (hU : U ≤ cut)
    (s : T.Slot) (e : Fin P.edges.length) :
    T.splitIndex s (P.boundaryAnchor s cut e) < cut := by
  have H := hP.edge_not_both_occupied hi hstar hU s (P.edges.get e) (List.get_mem _ e)
  unfold NativeGeneratedTest.boundaryAnchor
  split_ifs with h
  · omega
  · omega

theorem NativeGeneratedTest.oriented_low_split (P : NativeGeneratedTest T)
    (s : T.Slot) (cut : ℕ) (e : Fin P.edges.length) :
    T.splitIndex (P.boundaryAnchor s cut e) (P.boundaryTarget s cut e) =
      T.splitIndex (P.edges.get e).1 (P.edges.get e).2 := by
  unfold NativeGeneratedTest.boundaryAnchor NativeGeneratedTest.boundaryTarget
  split_ifs
  · exact T.splitIndex_symm _ _
  · rfl

theorem NativeTestGenerated.oriented_endpoints_distinct {i star U cut : ℕ}
    {P : NativeGeneratedTest T} (hP : NativeTestGenerated i star T P)
    (hi : i ≤ star) (hstar : star < U) (hU : U ≤ cut) (hcut : cut ≤ as.length)
    (s : T.Slot) (e : Fin P.edges.length) :
    P.boundaryAnchor s cut e ≠ P.boundaryTarget s cut e := by
  have hlow := (hP.edges_boundary hi hstar (P.edges.get e) (List.get_mem _ e)).trans_le hU
  have hneq : (P.edges.get e).1 ≠ (P.edges.get e).2 := by
    intro H
    rw [H,T.splitIndex_self] at hlow
    omega
  unfold NativeGeneratedTest.boundaryAnchor NativeGeneratedTest.boundaryTarget
  split_ifs
  · exact Ne.symm hneq
  · exact hneq

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem fullBoundaryAffineFactor_swap (n : ℕ) (α β : ℝ) (c d : Spin n×Bool) :
    fullBoundaryAffineFactor n α β c d = fullBoundaryAffineFactor n α β d c := by
  unfold fullBoundaryAffineFactor deletedOverlap
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  exact mul_comm _ _

theorem generated_boundary_oriented_factor_eq {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : T.NativeGeneratedTest)
    (s : T.Slot) (cut : ℕ) (e : Fin P.edges.length) (α β : ℝ) (σ : T.Assignment) :
    fullBoundaryAffineFactor n α β
      (T.atSlot σ (P.boundaryTarget s cut e)) (T.atSlot σ (P.boundaryAnchor s cut e)) =
      fullBoundaryAffineFactor n α β
        (T.atSlot σ (P.edges.get e).1) (T.atSlot σ (P.edges.get e).2) := by
  unfold ClockTree.NativeGeneratedTest.boundaryAnchor ClockTree.NativeGeneratedTest.boundaryTarget
  split_ifs
  · rfl
  · exact fullBoundaryAffineFactor_swap n α β _ _

def generatedActualBoundaryForest {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} {i star U cut : ℕ}
    {P : T.NativeGeneratedTest} (hP : ClockTree.NativeTestGenerated i star T P)
    (hi : i ≤ star) (hstar : star < U) (hU : U ≤ cut) (hcut : cut ≤ as.length)
    (s : T.Slot) (b h : ℕ → ℝ) (α β rho : Fin P.edges.length → ℝ)
    (hrho : ∀ e,0 < rho e)
    (hraw : ∀ e,nativeMixedBoundaryRawBudget n P.edges.length as b h
      (T.splitIndex (P.edges.get e).1 (P.edges.get e).2) (α e) (β e) ≤ (rho e)^(2*P.edges.length)) :
    ActualMixedBoundaryForest n P.edges.length T b h where
  α := α
  β := β
  i := P.boundaryAnchor s cut
  j := P.boundaryTarget s cut
  k := P.boundaryTarget s cut
  distinctLeft := hP.oriented_endpoints_distinct hi hstar hU hcut s
  distinctRight := hP.oriented_endpoints_distinct hi hstar hU hcut s
  sameLow := fun _ => rfl
  retainedHigh := fun _ H => (H rfl).elim
  lowInGrid := fun e => T.splitIndex_le_clockLength _ _
  rho := rho
  rhoPos := hrho
  raw := by intro e;rw [P.oriented_low_split];exact hraw e

theorem generatedActualBoundaryForest_product_eq {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} {i star U cut : ℕ}
    {P : T.NativeGeneratedTest} (hP : ClockTree.NativeTestGenerated i star T P)
    (hi : i ≤ star) (hstar : star < U) (hU : U ≤ cut) (hcut : cut ≤ as.length)
    (s : T.Slot) (b h : ℕ → ℝ) (α β rho : Fin P.edges.length → ℝ)
    (hrho : ∀ e,0 < rho e)
    (hraw : ∀ e,nativeMixedBoundaryRawBudget n P.edges.length as b h
      (T.splitIndex (P.edges.get e).1 (P.edges.get e).2) (α e) (β e) ≤ (rho e)^(2*P.edges.length))
    (σ : T.Assignment) :
    (generatedActualBoundaryForest hP hi hstar hU hcut s b h α β rho hrho hraw).product σ =
      ∏ e,fullBoundaryAffineFactor n (α e) (β e)
        (T.atSlot σ (P.edges.get e).1) (T.atSlot σ (P.edges.get e).2) := by
  unfold ActualMixedBoundaryForest.product fullBoundaryAffineProduct generatedActualBoundaryForest
  apply Finset.prod_congr rfl
  intro e _
  exact generated_boundary_oriented_factor_eq P s cut e (α e) (β e) σ

theorem generatedActualBoundaryForest_centered_product_eq {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} {i star U cut : ℕ}
    {P : T.NativeGeneratedTest} (hP : ClockTree.NativeTestGenerated i star T P)
    (hi : i ≤ star) (hstar : star < U) (hU : U ≤ cut) (hcut : cut ≤ as.length)
    (s : T.Slot) (b h C : ℕ → ℝ) (rho : Fin P.edges.length → ℝ)
    (hrho : ∀ e,0 < rho e)
    (hraw : ∀ e,nativeMixedBoundaryRawBudget n P.edges.length as b h
      (T.splitIndex (P.edges.get e).1 (P.edges.get e).2)
      (-C (T.splitIndex (P.edges.get e).1 (P.edges.get e).2)) 1 ≤ (rho e)^(2*P.edges.length))
    (σ : T.Assignment) :
    (generatedActualBoundaryForest hP hi hstar hU hcut s b h
      (fun e => -C (T.splitIndex (P.edges.get e).1 (P.edges.get e).2))
      (fun _ => 1) rho hrho hraw).product σ =
      P.value (fun u v => deletedOverlap n (joinSpin u) (joinSpin v)) C σ := by
  rw [generatedActualBoundaryForest_product_eq]
  unfold ClockTree.NativeGeneratedTest.value ClockTree.nativeGeneratedEdgeProduct
  let f := fun e : T.Slot × T.Slot =>
    deletedOverlap n (joinSpin (T.atSlot σ e.1)) (joinSpin (T.atSlot σ e.2))-C (T.splitIndex e.1 e.2)
  have H : (P.edges.map f).prod = ∏ e : Fin P.edges.length,f (P.edges.get e) := by
    rw [←List.prod_ofFn]
    change (P.edges.map f).prod = (List.ofFn (f ∘ P.edges.get)).prod
    rw [←List.map_ofFn,List.ofFn_get]
  rw [H]
  apply Finset.prod_congr rfl
  intro e _
  dsimp only [fullBoundaryAffineFactor,f]
  ring

theorem generatedActualBoundaryForest_clone_difference_eq {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} {i star U cut : ℕ}
    {P : T.NativeGeneratedTest} (hP : ClockTree.NativeTestGenerated i star T P)
    (hi : i ≤ star) (hstar : star < U) (hU : U ≤ cut) (hcut : cut ≤ as.length)
    (s : T.Slot) (b h : ℕ → ℝ) (α β rho : Fin P.edges.length → ℝ)
    (hrho : ∀ e,0 < rho e)
    (hraw : ∀ e,nativeMixedBoundaryRawBudget n P.edges.length as b h
      (T.splitIndex (P.edges.get e).1 (P.edges.get e).2) (α e) (β e) ≤ (rho e)^(2*P.edges.length))
    (σ : (ClockTree.nativeCloneBlockAtSlot T s cut).tree.Assignment) :
    let D := generatedActualBoundaryForest hP hi hstar hU hcut s b h α β rho hrho hraw
    (D.cloneAt s cut (hP.boundaryAnchor_departed hi hstar hU s)).difference σ =
      D.product ((ClockTree.nativeCloneBlockAtSlot T s cut).oldRestrict σ)-
        D.product ((ClockTree.nativeCloneBlockAtSlot T s cut).newRestrict σ) :=
  actual_cloned_boundary_forest_difference_eq
    (generatedActualBoundaryForest hP hi hstar hU hcut s b h α β rho hrho hraw) s cut
    (hP.boundaryAnchor_departed hi hstar hU s) σ

end OAI.SKFluctuations.Cavity
