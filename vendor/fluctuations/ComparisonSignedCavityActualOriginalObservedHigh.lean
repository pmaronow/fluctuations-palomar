module

public import ComparisonSignedCavityActualOriginalDummyJets
public import ComparisonSignedCavityActualFiniteProfileMarginal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
set_option maxHeartbeats 14000000
set_option backward.isDefEq.respectTransparency false

def nativeOriginalObservedHigh (n : ℕ) (v : FullCoordinate n→ℝ)
    (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.Assignment→ℝ) (a : T.Slot) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C]
      p.tree (fun σ=>P (p.restrict σ)) [p.embed a,p.mark])).sum

theorem native_original_observed_high_eq_dummy_row
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (a : T.Slot) :
    nativeOriginalObservedHigh n v q x U K b C T P a=
      ClockTree.nativeMarkedProfileRow (nativeDummyWeight n) (nativeDummyFeature n) T.withDummy
        (nativeDummyRoot v) (nativeDummyClock q U K)
        [ReplicaTree.coordinateProfile (nativeDummyFeature n) (nativeDummyHighDirection n U b C)]
        (fun σ=>P (T.withDummyPhysical σ)*spinValue (T.withDummy.atSlot σ (T.withDummySlot a)).2)
        (fun s=>nativeDummyFeature n s (nativeDummyScalarRootDirection n)) (nativeDummyField x) := by
  symm
  unfold ClockTree.nativeMarkedProfileRow nativeOriginalObservedHigh
  rw [ClockTree.markedAttach_withDummy]
  simp only [List.map_map,Function.comp_def,ClockTree.MarkedPlacement.withDummy_coeff]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  congr 1
  have he : (fun σ : p.tree.withDummy.Assignment=>
      (P (T.withDummyPhysical (p.withDummy.restrict σ))*
        spinValue (T.withDummy.atSlot (p.withDummy.restrict σ) (T.withDummySlot a)).2)*
        nativeDummyFeature n (p.withDummy.spin σ) (nativeDummyScalarRootDirection n))=
      (fun σ=>P (p.restrict (p.tree.withDummyPhysical σ))*
        nativeDummyMonomial p.tree σ [p.embed a,p.mark]) := by
    funext σ
    rw [nativeDummyFeature_scalarRootDirection,p.withDummy_physical_restrict,
      p.withDummy.restrict_at,p.withDummy_embed,p.withDummy.spin_at]
    simp only [nativeDummyMonomial,List.map_cons,List.map_nil,ClockTree.slotProduct,mul_one]
    dsimp only [ClockTree.MarkedPlacement.withDummy]
    ring
  have H:=native_dummy_jets_eq_original_signed n v q x U K [nativeOriginalHighKernel n U b C]
    p.tree ho (fun σ=>P (p.restrict σ)) [p.embed a,p.mark]
  rw [List.map_singleton,nativeDummyLiftKernel_high] at H
  exact (congrArg (fun F : p.tree.withDummy.Assignment→ℝ=>
    ClockTree.disorderProfileJets (nativeDummyWeight n) (nativeDummyFeature n)
      (nativeDummyRoot v) (nativeDummyClock q U K) (nativeDummyField x)
      [ReplicaTree.coordinateProfile (nativeDummyFeature n) (nativeDummyHighDirection n U b C)]
      p.tree.withDummy F) he).trans H

theorem native_original_observed_high_marked_preserves
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (P : T.Assignment→ℝ) (a : T.Slot)
    (p : ClockTree.MarkedPlacement T) (hp : p∈T.markedAttach 0) :
    nativeOriginalObservedHigh n v q x U K b C p.tree (fun σ=>P (p.restrict σ)) (p.embed a)=
      nativeOriginalObservedHigh n v q x U K b C T P a := by
  rw [native_original_observed_high_eq_dummy_row n v q x U K b C p.tree ho,
    native_original_observed_high_eq_dummy_row n v q x U K b C T ho]
  let Obs:=fun σ : T.withDummy.Assignment=>P (T.withDummyPhysical σ)*
    spinValue (T.withDummy.atSlot σ (T.withDummySlot a)).2
  have hobs : (fun σ : p.tree.withDummy.Assignment=>P (p.restrict (p.tree.withDummyPhysical σ))*
      spinValue (p.tree.withDummy.atSlot σ (p.tree.withDummySlot (p.embed a))).2)=
      (fun σ=>Obs (p.withDummy.restrict σ)) := by
    funext σ
    dsimp only [Obs]
    rw [p.withDummy_physical_restrict,p.withDummy.restrict_at,p.withDummy_embed]
    rfl
  rw [hobs]
  have hpD : p.withDummy∈T.withDummy.markedAttach 0 := by
    rw [ClockTree.markedAttach_withDummy]
    exact List.mem_map.mpr ⟨p,hp,rfl⟩
  exact ClockTree.native_profile_row_single_marked_marginal (nativeDummyWeight_pos n)
    (nativeDummyFeature n) T.withDummy ho p.withDummy hpD (nativeDummyRoot v)
    (nativeDummyClock q U K) (nativeDummyClock_monotone q U K hq hK hKm)
    (nativeDummyRoot_le_clock_zero v q U K hq0 hK) (nativeDummyHighDirection n U b C)
    Obs (nativeDummyScalarRootDirection n) (nativeDummyField x)

end OAI.SKFluctuations.Cavity
