module

public import ComparisonSignedCavitySecondLowOccupiedOldCanonicalOrientation
public import ComparisonSignedCavitySecondLowActualClassifiedHighCSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 22000000

namespace NativeSecondLowClassifiedHighWholeCSource
variable {n : ℕ} {pre mid tail : List PositiveMass}
variable {T : ClockTree (Spin n×Bool) (pre++(mid++tail))} {f c z : T.Slot}
variable {v : RestCoordinate n→ℝ} {q : ℕ→RestCoordinate n→ℝ} {x : RestCoordinate n→ℝ}

theorem oriented_old_anchor_at_every_D
    (E : NativeSecondLowClassifiedHighWholeCSource n pre mid tail T f c z v q x)
    {a U cut : ℕ} (G : ActualNaturalBoundaryShape n a T)
    (hstar : pre.length+mid.length < U) (hU : U ≤ (pre++(mid++tail)).length)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T)
    (hlow : ∀e,T.splitIndex (G.i e) (G.j e) < U) (hcut : U ≤ cut)
    (d : E.source.core.D.Slot) (e : Fin a) :
    T.splitIndex (E.toRetainedCSource.originalSlot d) ((G.orientAway c U).i e)=
        T.splitIndex c ((G.orientAway c U).i e) ∧
      T.splitIndex (E.toRetainedCSource.originalSlot d) ((G.orientAway c U).i e) < U ∧
      T.splitIndex (E.toRetainedCSource.originalSlot d) ((G.orientAway c U).i e) < cut := by
  exact G.orientAway_anchor_at_occupied c (E.toRetainedCSource.originalSlot d) U cut hlow
    (E.toRetainedCSource.originalSlot_high hstar hU hT d) hcut e

theorem oriented_resource_anchor_at_every_D
    (E : NativeSecondLowClassifiedHighWholeCSource n pre mid tail T f c z v q x)
    {i U cut : ℕ} (P : NativeResourceMonomial i (pre.length+mid.length) T)
    (hi : i ≤ pre.length+mid.length) (hstar : pre.length+mid.length < U)
    (hU : U ≤ (pre++(mid++tail)).length)
    (hT : NativePersistentLowForks pre.length (pre.length+mid.length) U T) (hcut : U ≤ cut)
    (d : E.source.core.D.Slot) (e : Fin P.factors.length) :
    let G:=nativeActualResourceCanonicalShape P hi (hstar.trans_le hU)
    T.splitIndex (E.toRetainedCSource.originalSlot d) ((G.orientAway c U).i e) < U ∧
      T.splitIndex (E.toRetainedCSource.originalSlot d) ((G.orientAway c U).i e) < cut := by
  exact (E.oriented_old_anchor_at_every_D (nativeActualResourceCanonicalShape P hi (hstar.trans_le hU))
    hstar hU hT (native_actual_resource_canonical_factors_LOW P hi hstar hU) hcut d e).2

end NativeSecondLowClassifiedHighWholeCSource

def nativeSecondLowFreshObservedOccupiedOldShape
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star U : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hstar : star < U) (hU : U ≤ as.length)
    (s : T.Slot) (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0) (c : p.tree.Slot) :
    ActualNaturalBoundaryShape n P.factors.length p.tree :=
  (nativeFreshObservedShape (nativeActualResourceCanonicalShape P hi (hstar.trans_le hU)) s star p hp).orientAway c U

theorem native_second_low_actual_generated_old_anchor_departed_at_every_D
    (n : ℕ) (pre mid tail : List PositiveMass)
    {T : ClockTree (Spin n×Bool) (pre++(mid++tail))} {U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm pre.length (pre.length+mid.length) T}
    (hP : NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed k T P)
    (s : T.Slot) (hstar : pre.length+mid.length < U)
    (hU : U ≤ (pre++(mid++tail)).length)
    (B : NativeSecondLowFreshOccupiedMiddleBlock T s (pre.length+mid.length) U hU)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s (pre.length+mid.length)).tree)
    (hp : p∈nativeHighMarkedRows (nativeFreshAtSlot T 0 s (pre.length+mid.length)).tree
      ((nativeFreshAtSlot T 0 s (pre.length+mid.length)).embed s) (U-1) 0)
    (v : RestCoordinate n→ℝ) (q : ℕ→RestCoordinate n→ℝ) (x : RestCoordinate n→ℝ)
    (E : NativeSecondLowClassifiedHighWholeCSource n pre mid tail p.tree p.mark
      (p.embed ((nativeFreshAtSlot T 0 s (pre.length+mid.length)).embed
        (nativeSecondLowFreshOccupiedOldSlot T s (pre.length+mid.length) U hU B)))
      (p.embed (nativeFreshAtSlot T 0 s (pre.length+mid.length)).mark) v q x)
    (cut : ℕ) (hcut : U ≤ cut) (d : E.source.core.D.Slot) (e : Fin P.live.factors.length) :
    let hp0:=(mem_nativeHighMarkedRows _ _ _ _ p).mp hp |>.1
    let G:=nativeSecondLowFreshObservedOccupiedOldShape P.live (by omega) hstar hU s p hp0
      (p.embed ((nativeFreshAtSlot T 0 s (pre.length+mid.length)).embed
        (nativeSecondLowFreshOccupiedOldSlot T s (pre.length+mid.length) U hU B)))
    p.tree.splitIndex (E.toRetainedCSource.originalSlot d) (G.i e) < U ∧
      p.tree.splitIndex (E.toRetainedCSource.originalSlot d) (G.i e) < cut := by
  let g:=nativeFreshAtSlot T 0 s (pre.length+mid.length)
  obtain ⟨hp0,hpH⟩:=(mem_nativeHighMarkedRows g.tree (g.embed s) (U-1) 0 p).mp hp
  have HpH : U ≤ p.tree.splitIndex p.mark (p.embed (g.embed s)):=by
    rw [p.tree.splitIndex_symm]
    omega
  have Hp : NativePersistentLowForks pre.length (pre.length+mid.length) U p.tree:=
    ((hP.persistentLowForks (by omega)).freshStar 0 s).observedHigh
      (by omega) hstar 0 p hp0 (g.embed s) HpH
  have HL:=native_second_low_fresh_observed_canonical_factors_LOW
    (nativeActualResourceCanonicalShape P.live (by omega) (hstar.trans_le hU)) s
    (pre.length+mid.length) U p hp0 (native_actual_resource_canonical_factors_LOW P.live (by omega) hstar hU)
  exact (E.oriented_old_anchor_at_every_D
    (nativeFreshObservedShape (nativeActualResourceCanonicalShape P.live (by omega) (hstar.trans_le hU))
      s (pre.length+mid.length) p hp0) hstar hU Hp HL hcut d e).2

theorem native_second_low_fresh_observed_occupied_old_rest_source
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star U : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hstar : star < U) (hU : U ≤ as.length)
    (s : T.Slot) (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0) (c : p.tree.Slot)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin P.factors.length→NativeSourceFactorForm) (σ : p.tree.cavityLeft.Assignment) :
    ((nativeSecondLowFreshObservedOccupiedOldShape P hi hstar hU s p hp c).canonicalMinimumSource M forms).restProduct σ=
      ((nativeActualResourceCanonicalShape P hi (hstar.trans_le hU)).canonicalMinimumSource M forms).restProduct
        ((nativeFreshAtSlot T 0 s star).restRestrict (p.restRestrict σ)) :=
  native_second_low_fresh_observed_oriented_complete_rest_source
    (nativeActualResourceCanonicalShape P hi (hstar.trans_le hU)) s star U p hp c M forms σ

theorem native_second_low_fresh_observed_occupied_old_source_mass
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star U : ℕ}
    (P : NativeResourceMonomial i star T) (hi : i ≤ star) (hstar : star < U) (hU : U ≤ as.length)
    (s : T.Slot) (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0) (c : p.tree.Slot)
    (Cmass x W : ℝ) (hmi : partitionPoint 0 as i ≤ Cmass*x)
    (hms : partitionPoint 0 as star ≤ Cmass*W) (e : Fin P.factors.length) :
    (nativeSecondLowFreshObservedOccupiedOldShape P hi hstar hU s p hp c).sourceLowMass e ≤
      Cmass*sourceFactorScale x W (nativeActualResourceInitialFactors P) e := by
  unfold nativeSecondLowFreshObservedOccupiedOldShape
  rw [native_second_low_fresh_observed_oriented_source_mass]
  exact native_actual_resource_canonical_source_mass P hi (hstar.trans_le hU) Cmass x W hmi hms e

end OAI.SKFluctuations.Cavity
