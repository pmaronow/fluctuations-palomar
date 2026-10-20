module

public import ComparisonSignedCavitySingleFreshOriginalLaw
public import ComparisonSignedCavityTwoFreshLongitudinal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open scoped NNReal

theorem native_withDummy_leaves {S : Type*} {as : List PositiveMass} (T : ClockTree S as) :
    T.withDummy.leaves=T.leaves := by
  induction T with
  | leaf=>rfl
  | step b T ih=>exact ih
  | fork T R ihT ihR=>simp only [withDummy,leaves,ihT,ihR]

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem native_original_one_leaf_fresh_observed_high_symmetric
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (hT : T.leaves=1)
    (ho : MassOrdered 0 as) (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (hA : ∀u v,A u v=A v u)
    (hq : ∀j,Monotone (fun u=>q u j)) (hq0 : ∀j,v j ≤ q 0 j)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) :
    let g:=nativeFreshAtSlot T 0 s star
    let P:=fun σ=>A (g.tree.atSlot σ (g.embed s)) (g.tree.atSlot σ g.mark)
    nativeOriginalObservedHigh n v q x U K b C g.tree P (g.embed s)=
      nativeOriginalObservedHigh n v q x U K b C g.tree P g.mark := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 s star
  let P:=fun σ=>A (g.tree.atSlot σ (g.embed s)) (g.tree.atSlot σ g.mark)
  let PL:=fun σ : g.tree.withDummy.Assignment=>P (g.tree.withDummyPhysical σ)*
    spinValue (g.tree.withDummy.atSlot σ (g.tree.withDummySlot (g.embed s))).2
  let PR:=fun σ : g.tree.withDummy.Assignment=>P (g.tree.withDummyPhysical σ)*
    spinValue (g.tree.withDummy.atSlot σ (g.tree.withDummySlot g.mark)).2
  have HPL (σ : g.tree.withDummy.Assignment) :
      A (T.withDummy.atSlot (g.withDummy.restrict σ) (T.withDummySlot s)).1 (g.withDummy.spin σ).1*
        spinValue (T.withDummy.atSlot (g.withDummy.restrict σ) (T.withDummySlot s)).2=PL σ := by
    rw [g.withDummy.restrict_at,g.withDummy_embed,g.withDummy.spin_at]
    simp only [PL,P,g.tree.withDummyPhysical_atSlot]
    rfl
  have HPR (σ : g.tree.withDummy.Assignment) :
      A (g.withDummy.spin σ).1 (T.withDummy.atSlot (g.withDummy.restrict σ) (T.withDummySlot s)).1*
        spinValue (g.withDummy.spin σ).2=PR σ := by
    rw [hA,g.withDummy.restrict_at,g.withDummy_embed,g.withDummy.spin_at]
    simp only [PR,P,g.tree.withDummyPhysical_atSlot]
    rfl
  have HE (qc : ℕ→NativeDummyCoordinate n→ℝ≥0) (y : NativeDummyCoordinate n→ℝ) :
      g.tree.withDummy.expect (nativeDummyWeight n) (nativeDummyFeature n) qc PL y=
        g.tree.withDummy.expect (nativeDummyWeight n) (nativeDummyFeature n) qc PR y := by
    have H:=native_one_leaf_fresh_expect_swap T.withDummy
      ((native_withDummy_leaves T).trans hT) 0 (T.withDummySlot s) star hstar
      (nativeDummyWeight_pos n) (nativeDummyFeature n) ho qc
      (fun u v=>A u.1 v.1*spinValue u.2) y
    rw [nativeFreshAtSlot_withDummy T 0 s star] at H
    dsimp only at H
    change g.tree.withDummy.expect (nativeDummyWeight n) (nativeDummyFeature n) qc
      (fun σ=>A (T.withDummy.atSlot (g.withDummy.restrict σ) (T.withDummySlot s)).1 (g.withDummy.spin σ).1*
        spinValue (T.withDummy.atSlot (g.withDummy.restrict σ) (T.withDummySlot s)).2) y=
      g.tree.withDummy.expect (nativeDummyWeight n) (nativeDummyFeature n) qc
      (fun σ=>A (g.withDummy.spin σ).1 (T.withDummy.atSlot (g.withDummy.restrict σ) (T.withDummySlot s)).1*
        spinValue (g.withDummy.spin σ).2) y at H
    simp_rw [HPL,HPR] at H
    exact H
  rw [native_original_observed_high_eq_dummy_row n v q x U K b C g.tree ho _ _,
    native_original_observed_high_eq_dummy_row n v q x U K b C g.tree ho _ _]
  exact native_observed_covariance_transport_from_expect (nativeDummyWeight_pos n) (nativeDummyFeature n)
    g.tree.withDummy ho PL PR HE (nativeDummyRoot v) (nativeDummyClock q U K)
    (nativeDummyClock_monotone q U K hq hK hKm) (nativeDummyRoot_le_clock_zero v q U K hq0 hK)
    (nativeDummyHighDirection n U b C) (nativeDummyScalarRootDirection n) (nativeDummyField x)

theorem native_original_one_leaf_fresh_longitudinal_symmetric
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (hT : T.leaves=1)
    (ho : MassOrdered 0 as) (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (hA : ∀u v,A u v=A v u)
    (hq : ∀j,Monotone (fun u=>q u j)) (hq0 : ∀j,v j ≤ q 0 j)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (hU0 : 0 < U) (hU : U ≤ as.length) :
    let g:=nativeFreshAtSlot T 0 s star
    let P:=fun σ=>A (g.tree.atSlot σ (g.embed s)) (g.tree.atSlot σ g.mark)
    nativeOriginalLongitudinalPairing n v q x U K b C g.tree P (g.embed s)=
      nativeOriginalLongitudinalPairing n v q x U K b C g.tree P g.mark := by
  dsimp only
  rw [native_original_longitudinal_eq_observed_sub n v q x U K b C _ ho _ _
      hq hq0 hK hKm hU0 hU,
    native_original_longitudinal_eq_observed_sub n v q x U K b C _ ho _ _
      hq hq0 hK hKm hU0 hU,
    native_original_one_leaf_fresh_observed_high_symmetric n v q x U K b C T hT ho s star hstar
      A hA hq hq0 hK hKm]

theorem native_original_single_fresh_longitudinal_symmetric
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (star : ℕ) (hstar : star ≤ as.length)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (hA : ∀u v,A u v=A v u)
    (hq : ∀j,Monotone (fun u=>q u j)) (hq0 : ∀j,v j ≤ q 0 j)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (hU0 : 0 < U) (hU : U ≤ as.length) :
    let T:=single (S:=Spin n×Bool) as
    let g:=nativeFreshAtSlot T 0 (singleSlot as) star
    let P:=fun σ=>A (g.tree.atSlot σ (g.embed (singleSlot as))) (g.tree.atSlot σ g.mark)
    nativeOriginalLongitudinalPairing n v q x U K b C g.tree P (g.embed (singleSlot as))=
      nativeOriginalLongitudinalPairing n v q x U K b C g.tree P g.mark :=
  native_original_one_leaf_fresh_longitudinal_symmetric n v q x U K b C _ (single_leaves_exact as)
    ho (singleSlot as) star hstar A hA hq hq0 hK hKm hU0 hU

theorem native_original_single_fresh_longitudinal_deleted_center
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (star : ℕ) (hstar : star ≤ as.length)
    (center : ℝ) (hq : ∀j,Monotone (fun u=>q u j)) (hq0 : ∀j,v j ≤ q 0 j)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (hU0 : 0 < U) (hU : U ≤ as.length) :
    let T:=single (S:=Spin n×Bool) as
    let g:=nativeFreshAtSlot T 0 (singleSlot as) star
    let A:=fun (u v : Spin n×Bool)=>deletedOverlap n (joinSpin u) (joinSpin v)-center
    let P:=fun σ=>A (g.tree.atSlot σ (g.embed (singleSlot as))) (g.tree.atSlot σ g.mark)
    nativeOriginalLongitudinalPairing n v q x U K b C g.tree P (g.embed (singleSlot as))=
      nativeOriginalLongitudinalPairing n v q x U K b C g.tree P g.mark := by
  exact native_original_single_fresh_longitudinal_symmetric n v q x U K b C as ho star hstar
    (fun u v : Spin n×Bool=>deletedOverlap n (joinSpin u) (joinSpin v)-center)
    (by intro u v;simp only [deletedOverlap,mul_comm]) hq hq0 hK hKm hU0 hU

end OAI.SKFluctuations.Cavity
