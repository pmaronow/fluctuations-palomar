module

public import ComparisonSignedCavityOriginalGammaLawAdapter
public import ComparisonSignedCavityActualOriginalForwardLeadingContraction

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 20000000

theorem native_original_fresh_leading_response_eq_full_gamma_row
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) :
    nativeOriginalFreshPartnerLeadingResponse n v q x U K T s star Q=
      let g:=nativeFreshAtSlot T 0 s star
      ((g.tree.markedAttach 0).map (fun p=>p.coeff*
        fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
        p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
          (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ) (g.spin (p.restrict σ))) x)).sum := by
  let g:=nativeFreshAtSlot T 0 s star
  let FL (p : MarkedPlacement g.tree):=p.coeff*
    fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
    p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ) (g.spin (p.restrict σ))) x
  let FR (r : MarkedPlacement T):=r.coeff*fullScalarCutGamma r.tree U K (r.embed s) r.mark*
    (let g:=nativeFreshAtSlot r.tree 0 (r.embed s) star;
      g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ)) x)
  have HL:=native_high_row_sum_eq_full_of_support g.tree (g.embed s) star 0 FL (by
    intro p hp hh
    dsimp only [FL]
    rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hU (by omega)]
    ring)
  have HR:=native_high_row_sum_eq_full_of_support T s star 0 FR (by
    intro r hr hh
    dsimp only [FR]
    rw [fullScalarCutGamma_cross_zero r.tree ho U K _ _ hU (by omega)]
    ring)
  have HF:=native_original_high_fresh_gamma_expectation_row n v q x U K T ho s star
    (hs.le.trans hU) 0 0 Q
  change ((T.markedAttach 0).map FR).sum=((g.tree.markedAttach 0).map FL).sum
  exact HR.symm.trans (HF.symm.trans HL)

theorem native_original_fresh_leading_response_eq_projection_add_displacement
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) :
    nativeOriginalFreshPartnerLeadingResponse n v q x U K T s star (fun σ c d=>P σ*A c d)=
      let g:=nativeFreshAtSlot T 0 s star
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
          (fun σ=>P (g.restrict σ)*A (T.atSlot (g.restrict σ) s) (g.spin σ)) x+
      nativeOriginalGammaProjectedDisplacement T s star U K v q x A P := by
  rw [native_original_fresh_leading_response_eq_full_gamma_row n v q x U K T ho s star hs hU]
  dsimp only
  let g:=nativeFreshAtSlot T 0 s star
  have Hp (p : MarkedPlacement g.tree) :
      p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>P (g.restrict (p.restrict σ))*A (p.spin σ) (g.spin (p.restrict σ))) x=
      p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>P (g.restrict (p.restrict σ))*
          A (T.atSlot (g.restrict (p.restrict σ)) s) (g.spin (p.restrict σ))) x+
      p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>(A (p.spin σ) (g.spin (p.restrict σ))-
          A (T.atSlot (g.restrict (p.restrict σ)) s) (g.spin (p.restrict σ)))*
          P (g.restrict (p.restrict σ))) x := by
    unfold ClockTree.disorderExpect
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro σ hσ
    ring
  dsimp only [g] at Hp
  simp_rw [Hp]
  simp only [mul_add,List.sum_map_add]
  rw [native_observed_gamma_full_test_collapse n g.tree ho 0 ho U (by omega) K (g.embed s)
    v q (fun σ=>P (g.restrict σ)*A (T.atSlot (g.restrict σ) s) (g.spin σ)) x]
  unfold nativeOriginalGammaProjectedDisplacement nativeOriginalGammaWeightedExpectation
  dsimp only [g]
  simp only [mul_assoc]

theorem native_original_fresh_leading_response_eq_projection_rest_and_first_high
    (n : ℕ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (s : T.Slot) (star U : ℕ) (hs : star < U)
    (q : ℕ→RestCoordinate n→ℝ) (b h K : ℕ→ℝ) (hU : U ≤ as.length)
    (A : Spin n→Spin n→ℝ) (P : T.cavityLeft.Assignment→ℝ)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeOriginalFreshPartnerLeadingResponse n 0 (cutFullVariance n q U 1 1 b h K) 0 U K T s star
      (fun σ c d=>P (T.cavityAssignment σ).1*A c.1 d.1)=
      let g:=nativeFreshAtSlot T 0 s star
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        g.tree.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U 1 1 b h K)
          (fun σ=>P (T.cavityAssignment (g.restrict σ)).1*
            A (T.atSlot (g.restrict σ) s).1 (g.spin σ).1) 0+
      nativeRetainedGammaProjectedDisplacement T s star U q K A P+
      nativeGammaProjectedFirstHighDisplacement T s star U q b h K A P+
      nativeGammaProjectedHighSecondRestoration T s star U q b h K A P+
      nativeGammaProjectedLowSecondRestoration T s star U q b h K A P := by
  rw [native_original_fresh_leading_response_eq_projection_add_displacement n 0
    (cutFullVariance n q U 1 1 b h K) 0 U K T ho s star hs hU
    (fun σ τ=>A σ.1 τ.1) (fun σ=>P (T.cavityAssignment σ).1),
    native_original_gamma_projected_displacement_eq_retained_first_high_and_remainders n T ho s star U
      q b h K hU A P hq0 hq hb hh hK hbm hhm hKm]
  dsimp only
  ring

end OAI.SKFluctuations.Cavity
