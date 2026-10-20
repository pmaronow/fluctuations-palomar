module

public import ComparisonSignedCavitySecondLowFullCenteredResourceReadout
public import ComparisonSignedCavitySecondLowOccupiedOldCanonicalOrientation
public import ComparisonSignedCavityActualDyadicRetainedChain

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

theorem native_actual_resource_canonical_source_mass_eq_tag_cut
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hs : star < as.length) (e : Fin P.factors.length) :
    (nativeActualResourceCanonicalShape P hi hs).sourceLowMass e=
      partitionPoint 0 as ((P.factors.get e).1.cut i star) := by
  dsimp only [ActualNaturalBoundaryShape.sourceLowMass,nativeActualResourceCanonicalShape]
  rw [T.splitIndex_symm,P.cuts _ (List.get_mem _ e)]

theorem native_actual_resource_canonical_source_mass_initial_or_star
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hs : star < as.length) (e : Fin P.factors.length) :
    (nativeActualResourceCanonicalShape P hi hs).sourceLowMass e=partitionPoint 0 as i ∨
      (nativeActualResourceCanonicalShape P hi hs).sourceLowMass e=partitionPoint 0 as star := by
  rw [native_actual_resource_canonical_source_mass_eq_tag_cut]
  cases (P.factors.get e).1 with
  | initial=>exact Or.inl rfl
  | oldStar=>exact Or.inr rfl
  | markedStar k=>exact Or.inr rfl

theorem native_actual_resource_canonical_source_radius_gate
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hs : star < as.length)
    (bound : ℝ) (Hi : M.R (partitionPoint 0 as i) ≤ bound)
    (Hs : M.R (partitionPoint 0 as star) ≤ bound) (e : Fin P.factors.length) :
    M.R ((nativeActualResourceCanonicalShape P hi hs).sourceLowMass e) ≤ bound := by
  rcases native_actual_resource_canonical_source_mass_initial_or_star P hi hs e with H|H
  · rw [H];exact Hi
  · rw [H];exact Hs

theorem native_actual_resource_canonical_coarse_source_mass
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hs : star < as.length)
    (Cmass x W : ℝ) (hCm : 0 ≤ Cmass) (hxW : x ≤ W)
    (Hi : partitionPoint 0 as i ≤ Cmass*x) (Hs : partitionPoint 0 as star ≤ Cmass*W)
    (e : Fin P.factors.length) :
    (nativeActualResourceCanonicalShape P hi hs).sourceLowMass e ≤ Cmass*W := by
  rcases native_actual_resource_canonical_source_mass_initial_or_star P hi hs e with H|H
  · rw [H];exact Hi.trans (mul_le_mul_of_nonneg_left hxW hCm)
  · rw [H];exact Hs

theorem native_second_low_coarse_readout_from_retained_nodes
    (sourceMass : ℝ) (hsourceMass : 0 < sourceMass) (us : List PositiveMass)
    (hus : ∀u∈us,u.val ≤ 1)
    (hnodes : ∀j ≤ nativeDyadicCutDepth sourceMass,nativeDyadicMassCut sourceMass hsourceMass j∈us)
    (jGrid U : ℕ) (hU : U ≤ (finiteCutMasses us jGrid).length)
    (hmass : partitionPoint 0 (finiteCutMasses us jGrid) U=sourceMass) :
    NativeDyadicRetainedReadout sourceMass hsourceMass (finiteCutMasses us jGrid) U := by
  have ho:=finiteCutMasses_ordered us hus jGrid
  have ha1 : sourceMass ≤ 1:=by rw [←hmass];exact (partitionPoint_mem _ ho U).2
  exact native_dyadic_retained_readout hsourceMass ha1 _ ho
    (fun j hj=>finiteCutMasses_nodes us jGrid (hnodes j hj)) U hU hmass

end OAI.SKFluctuations.Cavity
