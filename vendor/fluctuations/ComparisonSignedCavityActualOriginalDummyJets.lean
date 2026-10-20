module

public import ComparisonSignedCavityActualOriginalHighResponse
public import ComparisonSignedCavityActualDummyScalarProduct
public import ComparisonSignedCavityActualDummyScalarMarked

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
set_option maxHeartbeats 14000000
set_option backward.isDefEq.respectTransparency false

def nativeDummyLiftKernel {n : ℕ} (A : ℕ→(Spin n×Bool)→(Spin n×Bool)→ℝ)
    (j : ℕ) (s t : (Spin n×Bool)×Bool) : ℝ :=
  spinValue s.2*spinValue t.2*A j s.1 t.1

theorem nativeDummyLiftKernel_high (n U : ℕ) (b C : ℕ→ℝ) :
    nativeDummyLiftKernel (nativeOriginalHighKernel n U b C)=
      ReplicaTree.coordinateProfile (nativeDummyFeature n) (nativeDummyHighDirection n U b C) := by
  funext j s t
  exact (nativeDummyHighDirection_coordinateProfile n U b C j s t).symm

theorem nativeDummyMonomial_marked_restrict {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (p : ClockTree.MarkedPlacement T)
    (es : List T.Slot) (σ : p.tree.withDummy.Assignment) :
    nativeDummyMonomial T (p.withDummy.restrict σ) es=
      nativeDummyMonomial p.tree σ (es.map p.embed) := by
  induction es with
  | nil=>rfl
  | cons s es ih=>
    change spinValue (T.withDummy.atSlot (p.withDummy.restrict σ) (T.withDummySlot s)).2*
        nativeDummyMonomial T (p.withDummy.restrict σ) es=
      spinValue (p.tree.withDummy.atSlot σ (p.tree.withDummySlot (p.embed s))).2*
        nativeDummyMonomial p.tree σ (es.map p.embed)
    rw [p.withDummy.restrict_at,p.withDummy_embed,ih]
    rfl

theorem nativeDummyMonomial_append {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (σ : T.withDummy.Assignment) (es fs : List T.Slot) :
    nativeDummyMonomial T σ (es++fs)=nativeDummyMonomial T σ es*nativeDummyMonomial T σ fs := by
  simp only [nativeDummyMonomial,List.map_append,ClockTree.slotProduct_append]

theorem native_dummy_profilePairTest {n : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (P : T.Assignment→ℝ)
    (A : ℕ→(Spin n×Bool)→(Spin n×Bool)→ℝ) (es : List T.Slot)
    (p : ClockTree.MarkedPlacement T) (r : ClockTree.MarkedPlacement p.tree)
    (σ : r.tree.withDummy.Assignment) :
    ClockTree.profilePairTest (fun τ=>P (T.withDummyPhysical τ)*nativeDummyMonomial T τ es)
      (nativeDummyLiftKernel A) p.withDummy r.withDummy σ=
    ClockTree.profilePairTest P A p r (r.tree.withDummyPhysical σ)*
      nativeDummyMonomial r.tree σ (insertedSiteSlots es p r) := by
  simp only [ClockTree.profilePairTest,nativeDummyLiftKernel]
  rw [p.withDummy_physical_restrict,r.withDummy_physical_restrict,
    p.withDummy_physical_spin,r.withDummy_physical_spin,r.withDummy_physical_restrict]
  have hsplit : r.withDummy.tree.splitIndex (r.withDummy.embed p.withDummy.mark)
      r.withDummy.mark=r.tree.splitIndex (r.embed p.mark) r.mark := by
    change r.tree.withDummy.splitIndex (r.withDummy.embed (p.tree.withDummySlot p.mark))
      (r.tree.withDummySlot r.mark)=_
    rw [r.withDummy_embed,r.tree.splitIndex_withDummy]
  rw [hsplit]
  simp only [insertedSiteSlots,nativeDummyMonomial_append,
    nativeDummyMonomial_marked_restrict,List.map_map,Function.comp_def]
  have hs : spinValue (p.withDummy.spin (r.withDummy.restrict σ)).2*
      spinValue (r.withDummy.spin σ).2=
    nativeDummyMonomial r.tree σ [r.embed p.mark,r.mark] := by
    rw [p.withDummy.spin_at]
    change spinValue (p.tree.withDummy.atSlot (r.withDummy.restrict σ)
        (p.tree.withDummySlot p.mark)).2*spinValue (r.withDummy.spin σ).2=_
    rw [r.withDummy.restrict_at,r.withDummy.spin_at]
    change spinValue (r.tree.withDummy.atSlot σ
        (r.withDummy.embed (p.tree.withDummySlot p.mark))).2*
      spinValue (r.tree.withDummy.atSlot σ (r.tree.withDummySlot r.mark)).2=_
    rw [r.withDummy_embed]
    simp only [nativeDummyMonomial,List.map_cons,List.map_nil,ClockTree.slotProduct,mul_one]
  rw [←hs]
  ring

theorem native_dummy_jets_eq_original_signed
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K : ℕ→ℝ)
    (As : List (ℕ→(Spin n×Bool)→(Spin n×Bool)→ℝ)) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (es : List T.Slot) :
    ClockTree.disorderProfileJets (nativeDummyWeight n) (nativeDummyFeature n)
      (nativeDummyRoot v) (nativeDummyClock q U K) (nativeDummyField x)
      (As.map nativeDummyLiftKernel) T.withDummy
      (fun σ=>P (T.withDummyPhysical σ)*nativeDummyMonomial T σ es)=
      nativeOriginalSignedJets n v q x U K As T P es := by
  induction As generalizing T with
  | nil=>exact native_dummy_baseline_monomial n T ho v q x U K P es
  | cons A As ih=>
    simp only [List.map_cons,ClockTree.disorderProfileJets,nativeOriginalSignedJets,
      ClockTree.markedAttach_withDummy,List.map_map,Function.comp_def,
      ClockTree.MarkedPlacement.withDummy_coeff]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    change p.coeff*((p.tree.withDummy.markedAttach 0).map _).sum=_
    rw [ClockTree.markedAttach_withDummy]
    simp only [List.map_map,Function.comp_def,ClockTree.MarkedPlacement.withDummy_coeff]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    congr 1
    have he : ClockTree.profilePairTest
        (fun σ=>P (T.withDummyPhysical σ)*nativeDummyMonomial T σ es)
        (nativeDummyLiftKernel A) p.withDummy r.withDummy=
      (fun σ=>ClockTree.profilePairTest P A p r (r.tree.withDummyPhysical σ)*
        nativeDummyMonomial r.tree σ (insertedSiteSlots es p r)) := by
      funext σ
      exact native_dummy_profilePairTest P A es p r σ
    rw [he]
    exact ih r.tree (ClockTree.profilePairTest P A p r) (insertedSiteSlots es p r)

end OAI.SKFluctuations.Cavity
