module

public import ComparisonSignedCavityActualOriginalForwardPartner

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def nativeOriginalFreshPartnerLeadingSource
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ((g.tree.markedAttach 0).map (fun p=>p.coeff*
    fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      fullScalarCutGamma r.tree U K (r.embed (p.embed g.mark)) r.mark*
      r.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>Q (g.restrict (p.restrict (r.restrict σ)))
          (p.spin (r.restrict σ)) (r.spin σ)) x)).sum)).sum

def nativeOriginalFreshPartnerLeadingResponse
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) : ℝ :=
  ((T.markedAttach 0).map (fun r=>r.coeff*
    fullScalarCutGamma r.tree U K (r.embed s) r.mark*
    (let g:=nativeFreshAtSlot r.tree 0 (r.embed s) star
    g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ)) x))).sum

private theorem original_leading_row_mul {A : Type*} (L : List A)
    (w F : A→ℝ) (c : ℝ) :
    (L.map (fun a=>w a*(c*F a))).sum=c*(L.map (fun a=>w a*F a)).sum := by
  induction L with
  | nil=>simp
  | cons a L ih=>simp only [List.map_cons,List.sum_cons,ih];ring

theorem native_original_fresh_forward_leading_source_eq_chi_response
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) :
    nativeOriginalFreshPartnerLeadingSource n v q x U K T s star Q=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        nativeOriginalFreshPartnerLeadingResponse n v q x U K T s star Q := by
  let g:=nativeFreshAtSlot T 0 s star
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let FP (p : MarkedPlacement g.tree) := p.coeff*
    fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      fullScalarCutGamma r.tree U K (r.embed (p.embed g.mark)) r.mark*
      r.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>Q (g.restrict (p.restrict (r.restrict σ)))
          (p.spin (r.restrict σ)) (r.spin σ)) x)).sum
  let FL (p : MarkedPlacement g.tree) := p.coeff*
    fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
    p.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ) (g.spin (p.restrict σ))) x
  let FR (r : MarkedPlacement T) := r.coeff*
    fullScalarCutGamma r.tree U K (r.embed s) r.mark*
    (let g:=nativeFreshAtSlot r.tree 0 (r.embed s) star
    g.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ)) x)
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
      chi*((nativeHighMarkedRows g.tree (g.embed s) star 0).map FL).sum := by
    rw [←original_leading_row_mul]
    apply congrArg List.sum
    apply List.map_congr_left
    intro p hp
    have hp0:=((mem_nativeHighMarkedRows g.tree (g.embed s) star 0 p).mp hp).1
    by_cases hh : U ≤ p.tree.splitIndex (p.embed (g.embed s)) p.mark
    · dsimp only [FP]
      rw [native_actual_fresh_high_partner_gamma_row_collapse T ho s star U hs hU K p hp0 hh v q x Q]
    · dsimp only [FP]
      rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hU (lt_of_not_ge hh)]
      ring
  have HF:=native_original_high_fresh_gamma_expectation_row n v q x U K T ho s star
    (hs.le.trans hU) 0 0 Q
  change ((g.tree.markedAttach 0).map FP).sum=chi*((T.markedAttach 0).map FR).sum
  exact HP.symm.trans (HE.trans (congrArg (fun z=>chi*z) (HF.trans HR)))

end OAI.SKFluctuations.Cavity
