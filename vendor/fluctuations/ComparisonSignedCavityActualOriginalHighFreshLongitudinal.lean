module

public import ComparisonSignedCavityActualOriginalHighFreshResponse

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
set_option maxHeartbeats 22000000
attribute [local instance] Classical.propDecidable

private theorem weighted_response_row_sub {A : Type*} (L : List A)
    (w F G : A→ℝ) (c : ℝ) :
    (L.map (fun a=>w a*(F a-c*G a))).sum=
      (L.map (fun a=>w a*F a)).sum-c*(L.map (fun a=>w a*G a)).sum := by
  induction L with
  | nil=>simp
  | cons a L ih=>simp only [List.map_cons,List.sum_cons,ih];ring

theorem native_original_high_fresh_longitudinal_row
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length) (aFresh aRow : ℝ)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (hU0 : 0 < U) (hU : U ≤ as.length)
    (H : ℕ→Bool→ℝ) (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T aFresh s star
    ((nativeHighMarkedRows g.tree (g.embed s) star aRow).map (fun p=>p.coeff*
      H (p.tree.splitIndex (p.embed (g.embed s)) p.mark) (decide (p.mark=p.embed (g.embed s)))*
      nativeOriginalLongitudinalPairing n v q x U K b C p.tree
        (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ) (g.spin (p.restrict σ))) (p.embed g.mark))).sum=
    ((nativeHighMarkedRows T s star aRow).map (fun r=>r.coeff*
      H (r.tree.splitIndex (r.embed s) r.mark) (decide (r.mark=r.embed s))*
      (let g:=nativeFreshAtSlot r.tree aFresh (r.embed s) star
      nativeOriginalLongitudinalPairing n v q x U K b C g.tree
        (fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ)) g.mark))).sum := by
  dsimp only
  simp_rw [native_original_longitudinal_eq_observed_sub n v q x U K b C _ ho _ _ hq hq0 hK hKm hU0 hU]
  rw [weighted_response_row_sub,weighted_response_row_sub]
  rw [native_original_high_fresh_observed_row n v q x U K b C T ho s star hstar aFresh aRow
      hq hq0 hK hKm H Q,
    native_original_high_fresh_response_row n v q x U K b C T ho s star hstar aFresh aRow
      hq hq0 hK hKm H Q]

end OAI.SKFluctuations.Cavity
