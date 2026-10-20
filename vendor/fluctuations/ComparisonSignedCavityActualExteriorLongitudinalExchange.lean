module

public import ComparisonSignedCavityActualOriginalExteriorHighExchange
public import ComparisonSignedCavityActualOriginalLongitudinalGhost
public import ComparisonSignedCavityOriginalLawRowTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem native_original_exterior_observed_high_whole_exchange
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s t : T.Slot) (ht : t≠s) (k : ℕ)
    (h : ∀c : T.Slot,k ≤ T.splitIndex s c→c=s)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : k ≤ p.tree.splitIndex (p.embed s) p.mark)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (Q : T.Assignment→(Spin n×Bool)→ℝ) :
    nativeOriginalObservedHigh n v q x U K b C p.tree
      (fun σ=>Q (p.restrict σ) (p.spin σ)) (p.embed t)=
    nativeOriginalObservedHigh n v q x U K b C p.tree
      (fun σ=>Q (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
        (T.atSlot (p.restrict σ) s)) (p.embed t) := by
  let QD : T.withDummy.Assignment→((Spin n×Bool)×Bool)→ℝ:=fun σ z=>
    Q (T.withDummyPhysical σ) z.1*spinValue (T.withDummy.atSlot σ (T.withDummySlot t)).2
  let PL : p.tree.withDummy.Assignment→ℝ:=fun σ=>
    Q (p.restrict (p.tree.withDummyPhysical σ)) (p.spin (p.tree.withDummyPhysical σ))*
      spinValue (p.tree.withDummy.atSlot σ (p.tree.withDummySlot (p.embed t))).2
  let PR : p.tree.withDummy.Assignment→ℝ:=fun σ=>
    Q (nativeReplaceAtSlot T s (p.restrict (p.tree.withDummyPhysical σ))
      (p.spin (p.tree.withDummyPhysical σ))) (T.atSlot (p.restrict (p.tree.withDummyPhysical σ)) s)*
      spinValue (p.tree.withDummy.atSlot σ (p.tree.withDummySlot (p.embed t))).2
  have hpD : p.withDummy∈T.withDummy.markedAttach 0:=by
    rw [markedAttach_withDummy]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have hhD : k ≤ p.withDummy.tree.splitIndex (p.withDummy.embed (T.withDummySlot s)) p.withDummy.mark:=by
    change k ≤ p.tree.withDummy.splitIndex (p.withDummy.embed (T.withDummySlot s)) (p.tree.withDummySlot p.mark)
    rw [p.withDummy_embed,p.tree.splitIndex_withDummy]
    exact hh
  have HE (qc : ℕ→NativeDummyCoordinate n→ℝ≥0) (y : NativeDummyCoordinate n→ℝ) :
      p.tree.withDummy.expect (nativeDummyWeight n) (nativeDummyFeature n) qc PL y=
      p.tree.withDummy.expect (nativeDummyWeight n) (nativeDummyFeature n) qc PR y:=by
    have H:=native_target_singleton_whole_exchange T.withDummy (T.withDummySlot s) k
      (native_dummy_singleton T s k h) (nativeDummyWeight_pos n) (nativeDummyFeature n) ho
      p.withDummy hpD hhD qc QD y
    have HL : (fun σ=>QD (p.withDummy.restrict σ) (p.withDummy.spin σ))=PL:=by
      funext σ
      dsimp only [QD,PL]
      rw [p.withDummy_physical_restrict,p.withDummy_physical_spin,
        p.withDummy.restrict_at,p.withDummy_embed]
      rfl
    have HR : (fun σ=>QD
        (nativeReplaceAtSlot T.withDummy (T.withDummySlot s) (p.withDummy.restrict σ) (p.withDummy.spin σ))
        (T.withDummy.atSlot (p.withDummy.restrict σ) (T.withDummySlot s)))=PR:=by
      funext σ
      dsimp only [QD,PR]
      rw [native_dummy_physical_replace,p.withDummy_physical_restrict,p.withDummy_physical_spin,
        ←T.withDummyPhysical_atSlot,p.withDummy_physical_restrict,nativeReplaceAtSlot_at,
        ite_eq_right (fun H=>ht (T.withDummySlot.injective H)),p.withDummy.restrict_at,p.withDummy_embed]
      rfl
    erw [HL,HR] at H
    exact H
  rw [native_original_observed_high_eq_dummy_row n v q x U K b C p.tree ho,
    native_original_observed_high_eq_dummy_row n v q x U K b C p.tree ho]
  exact native_observed_covariance_transport_from_expect (nativeDummyWeight_pos n) (nativeDummyFeature n)
    p.tree.withDummy ho PL PR HE (nativeDummyRoot v) (nativeDummyClock q U K)
    (nativeDummyClock_monotone q U K hq hK hKm) (nativeDummyRoot_le_clock_zero v q U K hq0 hK)
    (nativeDummyHighDirection n U b C) (nativeDummyScalarRootDirection n) (nativeDummyField x)

theorem native_original_exterior_longitudinal_whole_exchange
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s t : T.Slot) (ht : t≠s) (k : ℕ)
    (h : ∀c : T.Slot,k ≤ T.splitIndex s c→c=s)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hh : k ≤ p.tree.splitIndex (p.embed s) p.mark)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (hU0 : 0 < U) (hU : U ≤ as.length)
    (Q : T.Assignment→(Spin n×Bool)→ℝ) :
    nativeOriginalLongitudinalPairing n v q x U K b C p.tree
      (fun σ=>Q (p.restrict σ) (p.spin σ)) (p.embed t)=
    nativeOriginalLongitudinalPairing n v q x U K b C p.tree
      (fun σ=>Q (nativeReplaceAtSlot T s (p.restrict σ) (p.spin σ))
        (T.atSlot (p.restrict σ) s)) (p.embed t) := by
  rw [native_original_longitudinal_eq_observed_sub n v q x U K b C p.tree ho _ _
      hq hq0 hK hKm hU0 hU,
    native_original_longitudinal_eq_observed_sub n v q x U K b C p.tree ho _ _
      hq hq0 hK hKm hU0 hU,
    native_original_exterior_observed_high_whole_exchange n v q x U K b C T ho s t ht k h
      p hp hh hq hq0 hK hKm Q]
  have H0:=native_original_exterior_high_slots_whole_exchange n v q x U K b C T ho s k h
    p hp hh hq hq0 hK hKm [] (by simp) Q
  simp only [List.map_nil] at H0
  rw [H0]

end OAI.SKFluctuations.Cavity
