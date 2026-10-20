module

public import ComparisonSignedCavityTwoFreshOriginalLaw
public import ComparisonSignedCavityOriginalLawRowTransport
public import ComparisonSignedCavityActualOriginalLongitudinalGhost
public import ComparisonSignedCavityActualDummyFreshTopology

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem native_original_two_fresh_observed_high_equal
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length)
    (hq : ∀j,Monotone (fun u=>q u j)) (hq0 : ∀j,v j ≤ q 0 j)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) :
    let g:=nativeFreshAtSlot T 0 s star
    let f:=nativeFreshAtSlot g.tree 0 g.mark star
    let Q:=fun σ=>P (g.restrict (f.restrict σ))
    nativeOriginalObservedHigh n v q x U K b C f.tree Q (f.embed g.mark)=
      nativeOriginalObservedHigh n v q x U K b C f.tree Q f.mark := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 s star
  let f:=nativeFreshAtSlot g.tree 0 g.mark star
  let W:=f.tree
  let Q:=fun σ=>P (g.restrict (f.restrict σ))
  let PL:=fun σ : W.withDummy.Assignment=>Q (W.withDummyPhysical σ)*
    spinValue (W.withDummy.atSlot σ (W.withDummySlot (f.embed g.mark))).2
  let PR:=fun σ : W.withDummy.Assignment=>Q (W.withDummyPhysical σ)*
    spinValue (W.withDummy.atSlot σ (W.withDummySlot f.mark)).2
  have Hf : nativeFreshAtSlot g.withDummy.tree 0 g.withDummy.mark star=f.withDummy :=
    nativeFreshAtSlot_withDummy g.tree 0 g.mark star
  have HPL (σ : f.tree.withDummy.Assignment) :
      P (T.withDummyPhysical (g.withDummy.restrict (f.withDummy.restrict σ)))*
        spinValue (g.withDummy.spin (f.withDummy.restrict σ)).2=PL σ := by
    simp only [MarkedPlacement.withDummy_physical_restrict]
    dsimp only [PL,Q,W]
    have HR:=f.withDummy.restrict_at σ (g.tree.withDummySlot g.mark)
    rw [f.withDummy_embed] at HR
    change P (g.restrict (f.restrict (f.tree.withDummyPhysical σ)))*
        spinValue (g.tree.withDummy.atSlot (f.withDummy.restrict σ) (g.tree.withDummySlot g.mark)).2=
      P (g.restrict (f.restrict (f.tree.withDummyPhysical σ)))*
        spinValue (f.tree.withDummy.atSlot σ (f.tree.withDummySlot (f.embed g.mark))).2
    rw [HR]
    rfl
  have HPR (σ : f.tree.withDummy.Assignment) :
      P (T.withDummyPhysical (g.withDummy.restrict (f.withDummy.restrict σ)))*
        spinValue (f.withDummy.spin σ).2=PR σ := by
    simp only [MarkedPlacement.withDummy_physical_restrict]
    rfl
  have HE (qc : ℕ→NativeDummyCoordinate n→ℝ≥0) (y : NativeDummyCoordinate n→ℝ) :
      W.withDummy.expect (nativeDummyWeight n) (nativeDummyFeature n) qc PL y=
        W.withDummy.expect (nativeDummyWeight n) (nativeDummyFeature n) qc PR y := by
    have H:=native_two_fresh_expect_swap T.withDummy 0 (T.withDummySlot s) star hstar
      (nativeDummyWeight_pos n) (nativeDummyFeature n) ho qc
      (fun σ u (_ : (Spin n×Bool)×Bool)=>P (T.withDummyPhysical σ)*spinValue u.2) y
    rw [nativeFreshAtSlot_withDummy T 0 s star] at H
    dsimp only at H
    rw [Hf] at H
    change f.tree.withDummy.expect (nativeDummyWeight n) (nativeDummyFeature n) qc
      (fun σ=>P (T.withDummyPhysical (g.withDummy.restrict (f.withDummy.restrict σ)))*
        spinValue (g.withDummy.spin (f.withDummy.restrict σ)).2) y=
      f.tree.withDummy.expect (nativeDummyWeight n) (nativeDummyFeature n) qc
        (fun σ=>P (T.withDummyPhysical (g.withDummy.restrict (f.withDummy.restrict σ)))*
          spinValue (f.withDummy.spin σ).2) y at H
    simp_rw [HPL,HPR] at H
    exact H
  rw [native_original_observed_high_eq_dummy_row n v q x U K b C f.tree ho _ _,
    native_original_observed_high_eq_dummy_row n v q x U K b C f.tree ho _ _]
  exact native_observed_covariance_transport_from_expect (nativeDummyWeight_pos n) (nativeDummyFeature n)
    W.withDummy ho PL PR HE (nativeDummyRoot v) (nativeDummyClock q U K)
    (nativeDummyClock_monotone q U K hq hK hKm) (nativeDummyRoot_le_clock_zero v q U K hq0 hK)
    (nativeDummyHighDirection n U b C) (nativeDummyScalarRootDirection n) (nativeDummyField x)

theorem native_original_two_fresh_longitudinal_equal
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length)
    (hq : ∀j,Monotone (fun u=>q u j)) (hq0 : ∀j,v j ≤ q 0 j)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (hU0 : 0 < U) (hU : U ≤ as.length) :
    let g:=nativeFreshAtSlot T 0 s star
    let f:=nativeFreshAtSlot g.tree 0 g.mark star
    let Q:=fun σ=>P (g.restrict (f.restrict σ))
    nativeOriginalLongitudinalPairing n v q x U K b C f.tree Q (f.embed g.mark)=
      nativeOriginalLongitudinalPairing n v q x U K b C f.tree Q f.mark := by
  dsimp only
  rw [native_original_longitudinal_eq_observed_sub n v q x U K b C _ ho _ _
      hq hq0 hK hKm hU0 hU,
    native_original_longitudinal_eq_observed_sub n v q x U K b C _ ho _ _
      hq hq0 hK hKm hU0 hU,
    native_original_two_fresh_observed_high_equal n v q x U K b C T ho P s star hstar hq hq0 hK hKm]

theorem native_original_two_fresh_longitudinal_sum
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length)
    (hq : ∀j,Monotone (fun u=>q u j)) (hq0 : ∀j,v j ≤ q 0 j)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (hU0 : 0 < U) (hU : U ≤ as.length) :
    let g:=nativeFreshAtSlot T 0 s star
    let f:=nativeFreshAtSlot g.tree 0 g.mark star
    let Q:=fun σ=>P (g.restrict (f.restrict σ))
    nativeOriginalLongitudinalPairing n v q x U K b C f.tree Q (f.embed g.mark)+
      nativeOriginalLongitudinalPairing n v q x U K b C f.tree Q f.mark=
      2*nativeOriginalLongitudinalPairing n v q x U K b C g.tree
        (fun σ=>P (g.restrict σ)) g.mark := by
  dsimp only
  rw [←native_original_two_fresh_longitudinal_equal n v q x U K b C T ho P s star hstar hq hq0 hK hKm hU0 hU,
    native_original_longitudinal_fresh_star_preserves n v q x U K b C _ ho
      (fun σ=>P ((nativeFreshAtSlot T 0 s star).restrict σ))
      (nativeFreshAtSlot T 0 s star).mark (nativeFreshAtSlot T 0 s star).mark star
      hq hq0 hK hKm hU0 hU]
  ring

end OAI.SKFluctuations.Cavity
