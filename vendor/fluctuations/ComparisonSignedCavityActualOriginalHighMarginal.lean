module

public import ComparisonSignedCavityActualOriginalDummyJets
public import ComparisonSignedCavityActualFiniteProfileMarginal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
set_option maxHeartbeats 14000000
set_option backward.isDefEq.respectTransparency false

theorem native_original_high_slots_marked_preserves
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (es : List T.Slot)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) :
    nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C]
      p.tree (fun σ=>P (p.restrict σ)) (es.map p.embed)=
    nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C] T P es := by
  have hpD : p.withDummy∈T.withDummy.markedAttach 0 := by
    rw [markedAttach_withDummy]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  have H:=native_profile_single_marked_marginal (nativeDummyWeight_pos n) (nativeDummyFeature n)
    T.withDummy ho p.withDummy hpD (nativeDummyRoot v) (nativeDummyClock q U K)
    (nativeDummyClock_monotone q U K hq hK hKm) (nativeDummyRoot_le_clock_zero v q U K hq0 hK)
    (nativeDummyHighDirection n U b C)
    (fun σ=>P (T.withDummyPhysical σ)*nativeDummyMonomial T σ es) (nativeDummyField x)
  have HP : (fun σ=>P (T.withDummyPhysical (p.withDummy.restrict σ))*
        nativeDummyMonomial T (p.withDummy.restrict σ) es)=
      (fun σ=>P (p.restrict (p.tree.withDummyPhysical σ))*
        nativeDummyMonomial p.tree σ (es.map p.embed)) := by
    funext σ
    rw [p.withDummy_physical_restrict,nativeDummyMonomial_marked_restrict]
  rw [HP,←nativeDummyLiftKernel_high] at H
  change disorderProfileJets _ _ _ _ _
      ([nativeOriginalHighKernel n U b C].map nativeDummyLiftKernel) p.tree.withDummy _=
    disorderProfileJets _ _ _ _ _
      ([nativeOriginalHighKernel n U b C].map nativeDummyLiftKernel) T.withDummy _ at H
  rw [native_dummy_jets_eq_original_signed n v q x U K _ p.tree ho
      (fun σ=>P (p.restrict σ)) (es.map p.embed),
    native_dummy_jets_eq_original_signed n v q x U K _ T ho P es] at H
  exact H

theorem native_original_high_marked_preserves
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) :
    nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C]
      p.tree (fun σ=>P (p.restrict σ)) []=
    nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C] T P [] :=
  native_original_high_slots_marked_preserves n v q x U K b C T ho P [] p hp hq hq0 hK hKm

theorem native_original_connected_high_marked_preserves
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (a c : T.Slot) (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) :
    nativeOriginalConnectedHighResponse n v q x U K b C p.tree
      (fun σ=>P (p.restrict σ)) (p.embed a) (p.embed c)=
    nativeOriginalConnectedHighResponse n v q x U K b C T P a c := by
  unfold nativeOriginalConnectedHighResponse
  have H:=native_original_high_slots_marked_preserves n v q x U K b C T ho P [a,c] p hp
    hq hq0 hK hKm
  simp only [List.map_cons,List.map_nil] at H
  rw [H,native_original_high_marked_preserves n v q x U K b C T ho P p hp hq hq0 hK hKm,
    fullScalarCutGamma_marked_preserves T ho U K a c p hp]

end OAI.SKFluctuations.Cavity
