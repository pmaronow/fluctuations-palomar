module

public import ComparisonSignedCavityActualOriginalHighFreshResponse

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem native_dummy_high_response_pair
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (a c : T.Slot) :
    disorderProfileJets (nativeDummyWeight n) (nativeDummyFeature n) (nativeDummyRoot v)
      (nativeDummyClock q U K) (nativeDummyField x)
      [ReplicaTree.coordinateProfile (nativeDummyFeature n) (nativeDummyHighDirection n U b C)]
      T.withDummy (fun σ=>P (T.withDummyPhysical σ)*
        spinValue (T.withDummy.atSlot σ (T.withDummySlot a)).2*
        spinValue (T.withDummy.atSlot σ (T.withDummySlot c)).2)=
    nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C] T P [a,c] := by
  have H:=native_dummy_jets_eq_original_signed n v q x U K [nativeOriginalHighKernel n U b C]
    T ho P [a,c]
  simpa only [List.map_cons,List.map_nil,nativeDummyLiftKernel_high,nativeDummyMonomial,
    slotProduct,mul_one,mul_assoc] using H

theorem native_original_high_fresh_pair_response_row
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length) (aFresh aRow : ℝ)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (H : ℕ→Bool→ℝ)
    (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T aFresh s star
    ((nativeHighMarkedRows g.tree (g.embed s) star aRow).map (fun p=>p.coeff*
      H (p.tree.splitIndex (p.embed (g.embed s)) p.mark) (decide (p.mark=p.embed (g.embed s)))*
      nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C] p.tree
        (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ) (g.spin (p.restrict σ)))
        [p.embed (g.embed s),p.mark])).sum=
    ((nativeHighMarkedRows T s star aRow).map (fun r=>r.coeff*
      H (r.tree.splitIndex (r.embed s) r.mark) (decide (r.mark=r.embed s))*
      (let g:=nativeFreshAtSlot r.tree aFresh (r.embed s) star
      nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C] g.tree
        (fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ))
        [g.embed (r.embed s),g.embed r.mark]))).sum := by
  dsimp only
  let QD:=fun τ : T.withDummy.Assignment=>fun c z : (Spin n×Bool)×Bool=>
    Q (T.withDummyPhysical τ) c.1 z.1*
      spinValue (T.withDummy.atSlot τ (T.withDummySlot s)).2*spinValue c.2
  have HD:=native_high_fresh_full_covariance_signed_row_sum T.withDummy (T.withDummySlot s)
    star hstar aFresh aRow (nativeDummyWeight_pos n) (nativeDummyFeature n) ho
    (nativeDummyRoot v) (nativeDummyClock q U K) (nativeDummyClock_monotone q U K hq hK hKm)
    (nativeDummyRoot_le_clock_zero v q U K hq0 hK) (nativeDummyHighDirection n U b C)
    QD (nativeDummyField x) H
  rw [nativeFreshAtSlot_withDummy] at HD
  change ((nativeHighMarkedRows (nativeFreshAtSlot T aFresh s star).tree.withDummy
      ((nativeFreshAtSlot T aFresh s star).withDummy.embed (T.withDummySlot s)) star aRow).map _).sum=_ at HD
  rw [MarkedPlacement.withDummy_embed,nativeHighMarkedRows_withDummy,nativeHighMarkedRows_withDummy] at HD
  simp only [List.map_map,Function.comp_def,MarkedPlacement.withDummy_coeff,
    MarkedPlacement.withDummy_embed,
    MarkedPlacement.withDummy_split_mark,MarkedPlacement.withDummy_mark_eq] at HD
  simp only [QD,MarkedPlacement.withDummy_physical_restrict,MarkedPlacement.withDummy_physical_spin] at HD
  convert HD using 1
  · apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    congr 1
    rw [←native_dummy_high_response_pair n v q x U K b C p.tree ho]
    congr 1
    funext σ
    rw [(nativeFreshAtSlot T aFresh s star).withDummy.restrict_at,
      (nativeFreshAtSlot T aFresh s star).withDummy_embed]
    change _=Q _ _ _*spinValue ((nativeFreshAtSlot T aFresh s star).tree.withDummy.atSlot
      (p.withDummy.restrict σ) ((nativeFreshAtSlot T aFresh s star).tree.withDummySlot
        ((nativeFreshAtSlot T aFresh s star).embed s))).2*spinValue (p.withDummy.spin σ).2
    rw [p.withDummy.restrict_at,p.withDummy_embed,p.withDummy.spin_at]
    rfl
  · apply congrArg List.sum
    apply List.map_congr_left
    intro r hr
    erw [r.withDummy_fresh_at_old]
    simp only [MarkedPlacement.withDummy_physical_restrict,MarkedPlacement.withDummy_physical_spin]
    congr 1
    rw [←native_dummy_high_response_pair n v q x U K b C
      (nativeFreshAtSlot r.tree aFresh (r.embed s) star).tree ho]
    congr 1
    funext σ
    rw [r.withDummy.restrict_at,r.withDummy_embed,r.withDummy.spin_at]
    change _=Q _ _ _*spinValue (r.tree.withDummy.atSlot
      ((nativeFreshAtSlot r.tree aFresh (r.embed s) star).withDummy.restrict σ)
      (r.tree.withDummySlot (r.embed s))).2*spinValue (r.tree.withDummy.atSlot
      ((nativeFreshAtSlot r.tree aFresh (r.embed s) star).withDummy.restrict σ)
      (r.tree.withDummySlot r.mark)).2
    rw [(nativeFreshAtSlot r.tree aFresh (r.embed s) star).withDummy.restrict_at,
      (nativeFreshAtSlot r.tree aFresh (r.embed s) star).withDummy_embed,
      (nativeFreshAtSlot r.tree aFresh (r.embed s) star).withDummy.restrict_at,
      (nativeFreshAtSlot r.tree aFresh (r.embed s) star).withDummy_embed]
    rfl

end OAI.SKFluctuations.Cavity
