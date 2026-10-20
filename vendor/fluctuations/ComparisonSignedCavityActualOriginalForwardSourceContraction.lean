module

public import ComparisonSignedCavityActualOriginalForwardPartner

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def nativeOriginalFreshPartnerGSource
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ((g.tree.markedAttach 0).map (fun p=>p.coeff*
    fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      nativeOriginalConnectedHighResponse n v q x U K b C r.tree
        (fun σ=>Q (g.restrict (p.restrict (r.restrict σ)))
          (p.spin (r.restrict σ)) (r.spin σ)) (r.embed (p.embed g.mark)) r.mark)).sum)).sum

def nativeOriginalFreshPartnerLResponse
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) : ℝ :=
  ((T.markedAttach 0).map (fun r=>r.coeff*
    fullScalarCutGamma r.tree U K (r.embed s) r.mark*
    (let g:=nativeFreshAtSlot r.tree 0 (r.embed s) star
    nativeOriginalLongitudinalPairing n v q x U K b C g.tree
      (fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ)) g.mark))).sum

theorem native_original_fresh_forward_G_source_eq_L_response
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) :
    nativeOriginalFreshPartnerGSource n v q x U K b C T s star Q=
      nativeOriginalFreshPartnerLResponse n v q x U K b C T s star Q := by
  let g:=nativeFreshAtSlot T 0 s star
  let FP (p : MarkedPlacement g.tree) := p.coeff*
    fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      nativeOriginalConnectedHighResponse n v q x U K b C r.tree
        (fun σ=>Q (g.restrict (p.restrict (r.restrict σ)))
          (p.spin (r.restrict σ)) (r.spin σ)) (r.embed (p.embed g.mark)) r.mark)).sum
  let FL (p : MarkedPlacement g.tree) := p.coeff*
    fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
    nativeOriginalLongitudinalPairing n v q x U K b C p.tree
      (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ) (g.spin (p.restrict σ))) (p.embed g.mark)
  let FR (r : MarkedPlacement T) := r.coeff*
    fullScalarCutGamma r.tree U K (r.embed s) r.mark*
    (let g:=nativeFreshAtSlot r.tree 0 (r.embed s) star
    nativeOriginalLongitudinalPairing n v q x U K b C g.tree
      (fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ)) g.mark)
  have HP:=native_high_row_sum_eq_full_of_support g.tree (g.embed s) star 0 FP (by
    intro p hp hh
    dsimp only [FP]
    rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hU (by omega)]
    ring)
  have HR:=native_high_row_sum_eq_full_of_support T s star 0 FR (by
    intro r hr hh
    dsimp only [FR]
    rw [fullScalarCutGamma_cross_zero r.tree ho U K _ _ hU (by omega)]
    ring)
  have HE : ((nativeHighMarkedRows g.tree (g.embed s) star 0).map FP).sum=
      ((nativeHighMarkedRows g.tree (g.embed s) star 0).map FL).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    have hp0:=((mem_nativeHighMarkedRows g.tree (g.embed s) star 0 p).mp hp).1
    by_cases hh : U ≤ p.tree.splitIndex (p.embed (g.embed s)) p.mark
    · dsimp only [FP,FL]
      rw [native_actual_fresh_high_partner_G_row_collapse n v q x U K b C T ho s star hs hU
        p hp0 hh hq hq0 hK hKm Q]
    · dsimp only [FP,FL]
      rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hU (lt_of_not_ge hh)]
      ring
  have HF:=native_original_high_fresh_gamma_longitudinal_row n v q x U K b C T ho s star
    (hs.le.trans hU) 0 0 hq hq0 hK hKm (by omega) hU Q
  change ((g.tree.markedAttach 0).map FP).sum=((T.markedAttach 0).map FR).sum
  exact HP.symm.trans (HE.trans (HF.trans HR))

end OAI.SKFluctuations.Cavity
