module

public import ComparisonSignedCavityActualOriginalHighFreshLongitudinal
public import ComparisonSignedCavityActualOriginalPartnerLongitudinal
public import ComparisonSignedCavityHighRowsSupportReduction
public import CavityScalarGammaTopology

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

private theorem original_gamma_bool_topology
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (U : ℕ) (K : ℕ→ℝ) (s : T.Slot) (p : MarkedPlacement T) :
    scalarGammaFromTopology as U K (p.tree.splitIndex (p.embed s) p.mark)
      (if decide (p.mark=p.embed s) then 1 else 0)=
      fullScalarCutGamma p.tree U K (p.embed s) p.mark := by
  rw [fullScalarCutGamma_marked_eq_topology T ho]
  simp only [MarkedPlacement.hit,decide_eq_true_eq]

theorem native_original_high_fresh_gamma_longitudinal_row
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length) (aFresh aRow : ℝ)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (hU0 : 0 < U) (hU : U ≤ as.length)
    (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T aFresh s star
    ((nativeHighMarkedRows g.tree (g.embed s) star aRow).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
      nativeOriginalLongitudinalPairing n v q x U K b C p.tree
        (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ) (g.spin (p.restrict σ))) (p.embed g.mark))).sum=
    ((nativeHighMarkedRows T s star aRow).map (fun r=>r.coeff*
      fullScalarCutGamma r.tree U K (r.embed s) r.mark*
      (let g:=nativeFreshAtSlot r.tree aFresh (r.embed s) star
      nativeOriginalLongitudinalPairing n v q x U K b C g.tree
        (fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ)) g.mark))).sum := by
  have H:=native_original_high_fresh_longitudinal_row n v q x U K b C T ho s star hstar
    aFresh aRow hq hq0 hK hKm hU0 hU
    (fun j hit=>scalarGammaFromTopology as U K j (if hit then 1 else 0)) Q
  dsimp only at H ⊢
  simpa only [original_gamma_bool_topology _ ho] using H

theorem native_original_high_fresh_gamma_expectation_row
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hstar : star ≤ as.length) (aFresh aRow : ℝ)
    (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T aFresh s star
    ((nativeHighMarkedRows g.tree (g.embed s) star aRow).map (fun p=>p.coeff*
      fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
      p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ) (g.spin (p.restrict σ))) x)).sum=
    ((nativeHighMarkedRows T s star aRow).map (fun r=>r.coeff*
      fullScalarCutGamma r.tree U K (r.embed s) r.mark*
      (let g:=nativeFreshAtSlot r.tree aFresh (r.embed s) star
      g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ)) x))).sum := by
  have H:=native_high_fresh_full_disorder_signed_row_sum T s star hstar aFresh aRow
    (fullWeight_pos n) (fullFeature n) ho v q Q x
    (fun j hit=>scalarGammaFromTopology as U K (j s) (if hit s then 1 else 0))
  dsimp only at H ⊢
  simpa only [original_gamma_bool_topology _ ho] using H

end OAI.SKFluctuations.Cavity
