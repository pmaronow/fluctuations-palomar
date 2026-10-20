module

public import ComparisonSignedCavityActualResourceCanonicalShape
public import ComparisonSignedCavityActualGammaPairedCanonicalSource
public import ComparisonSignedCavityGeneratedBoundaryMembership

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000
attribute [local instance] Classical.propDecidable

namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

def orientAway (G : ActualNaturalBoundaryShape n a T) (s : T.Slot) (U : ℕ) :
    ActualNaturalBoundaryShape n a T where
  α:=G.α
  β:=G.β
  i:=fun e=>if U ≤ T.splitIndex s (G.i e) then G.j e else G.i e
  j:=fun e=>if U ≤ T.splitIndex s (G.i e) then G.i e else G.j e
  distinct:=by
    intro e
    split_ifs
    · exact (G.distinct e).symm
    · exact G.distinct e
  lowInGrid:=fun _=>T.splitIndex_le_clockLength _ _

theorem orientAway_split (G : ActualNaturalBoundaryShape n a T) (s : T.Slot) (U : ℕ) (e : Fin a) :
    T.splitIndex ((G.orientAway s U).i e) ((G.orientAway s U).j e)=T.splitIndex (G.i e) (G.j e) := by
  dsimp only [orientAway]
  split_ifs
  · exact T.splitIndex_symm _ _
  · rfl

theorem orientAway_sourceLowMass (G : ActualNaturalBoundaryShape n a T) (s : T.Slot) (U : ℕ) (e : Fin a) :
    (G.orientAway s U).sourceLowMass e=G.sourceLowMass e := by
  unfold sourceLowMass
  rw [G.orientAway_split]

theorem orientAway_anchor_departed (G : ActualNaturalBoundaryShape n a T) (s : T.Slot) (U : ℕ)
    (hlow : ∀e,T.splitIndex (G.i e) (G.j e) < U) (e : Fin a) :
    T.splitIndex s ((G.orientAway s U).i e) < U := by
  dsimp only [orientAway]
  split_ifs with h
  · by_contra H
    have HH:=T.splitIndex_cut_trans U (G.i e) s (G.j e)
      (by rw [T.splitIndex_symm];exact h) (by omega)
    exact (not_le.mpr (hlow e)) HH
  · omega

theorem orientAway_anchor_at_occupied (G : ActualNaturalBoundaryShape n a T) (s d : T.Slot) (U cut : ℕ)
    (hlow : ∀e,T.splitIndex (G.i e) (G.j e) < U) (hD : U ≤ T.splitIndex s d)
    (hcut : U ≤ cut) (e : Fin a) :
    T.splitIndex d ((G.orientAway s U).i e)=T.splitIndex s ((G.orientAway s U).i e) ∧
      T.splitIndex d ((G.orientAway s U).i e) < U ∧
      T.splitIndex d ((G.orientAway s U).i e) < cut := by
  have HA:=G.orientAway_anchor_departed s U hlow e
  have HE:=T.splitIndex_low_eq_of_high d s ((G.orientAway s U).i e)
    (by rw [T.splitIndex_symm];exact hD) HA
  exact ⟨HE,HE.trans_lt HA,HE.trans_lt (HA.trans_le hcut)⟩

theorem orientAway_restProduct (G : ActualNaturalBoundaryShape n a T) (s : T.Slot) (U : ℕ)
    (σ : T.cavityLeft.Assignment) : (G.orientAway s U).restProduct σ=G.restProduct σ := by
  unfold restProduct
  apply Finset.prod_congr rfl
  intro e _
  dsimp only [orientAway]
  split_ifs
  · exact fullBoundaryAffineFactor_swap n _ _ _ _
  · rfl

theorem orientAway_canonical_restProduct
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (s : T.Slot) (U : ℕ)
    (forms : Fin a→NativeSourceFactorForm) (σ : T.cavityLeft.Assignment) :
    ((G.orientAway s U).canonicalMinimumSource M forms).restProduct σ=
      (G.canonicalMinimumSource M forms).restProduct σ := by
  unfold restProduct
  apply Finset.prod_congr rfl
  intro e _
  simp only [canonicalMinimumSource,G.orientAway_sourceLowMass]
  dsimp only [orientAway]
  split_ifs
  · exact fullBoundaryAffineFactor_swap n _ _ _ _
  · rfl

end ActualNaturalBoundaryShape

theorem native_actual_resource_canonical_factors_LOW
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star U : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hstar : star < U) (hU : U ≤ as.length)
    (e : Fin P.factors.length) :
    T.splitIndex ((nativeActualResourceCanonicalShape P hi (hstar.trans_le hU)).i e)
      ((nativeActualResourceCanonicalShape P hi (hstar.trans_le hU)).j e) < U := by
  change T.splitIndex (P.factors.get e).2.2 (P.factors.get e).2.1 < U
  rw [T.splitIndex_symm,P.cuts _ (List.get_mem _ e)]
  cases (P.factors.get e).1 <;> simp only [NativeResourceMark.cut] <;> omega

theorem native_second_low_fresh_observed_canonical_factors_LOW
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T) (s : T.Slot) (star U : ℕ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0)
    (hlow : ∀e,T.splitIndex (G.i e) (G.j e) < U) (e : Fin a) :
    p.tree.splitIndex ((nativeFreshObservedShape G s star p hp).i e)
      ((nativeFreshObservedShape G s star p hp).j e) < U := by
  dsimp only [nativeFreshObservedShape,ActualNaturalBoundaryShape.retainOnMarked]
  rw [((nativeFreshAtSlot T 0 s star).tree.markedAttach_embed_preserves 0 p hp).2,
    (nativeFreshAtSlot_old_splits T 0 s star).2]
  exact hlow e

theorem native_second_low_fresh_observed_oriented_complete_rest_source
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T) (s : T.Slot) (star U : ℕ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0) (c : p.tree.Slot)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin a→NativeSourceFactorForm) (σ : p.tree.cavityLeft.Assignment) :
    (((nativeFreshObservedShape G s star p hp).orientAway c U).canonicalMinimumSource M forms).restProduct σ=
      (G.canonicalMinimumSource M forms).restProduct
        ((nativeFreshAtSlot T 0 s star).restRestrict (p.restRestrict σ)) := by
  rw [ActualNaturalBoundaryShape.orientAway_canonical_restProduct,nativeFreshObservedShape,
    ActualNaturalBoundaryShape.retained_canonical_restProduct,
    ActualNaturalBoundaryShape.retained_canonical_restProduct]

theorem native_second_low_fresh_observed_oriented_source_mass
    {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (G : ActualNaturalBoundaryShape n a T) (s : T.Slot) (star U : ℕ)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0) (c : p.tree.Slot) (e : Fin a) :
    ((nativeFreshObservedShape G s star p hp).orientAway c U).sourceLowMass e=G.sourceLowMass e := by
  rw [ActualNaturalBoundaryShape.orientAway_sourceLowMass,nativeFreshObservedShape,
    ActualNaturalBoundaryShape.retained_source_mass,ActualNaturalBoundaryShape.retained_source_mass]

end OAI.SKFluctuations.Cavity
