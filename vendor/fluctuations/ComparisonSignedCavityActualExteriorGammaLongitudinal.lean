module

public import ComparisonSignedCavityActualExteriorLongitudinalExchange
public import ComparisonSignedCavityActualOriginalForwardSourceContraction

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem native_original_singleton_exterior_gamma_longitudinal_row_collapse
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s t : T.Slot) (ht : t≠s) (star : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (h : NativeTargetStarSingleton T s star)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (Q : T.Assignment→(Spin n×Bool)→ℝ)
    (hQ : ∀σ u z,Q (nativeReplaceAtSlot T s σ u) z=Q σ z) :
    ((T.markedAttach 0).map (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed s) p.mark*
      nativeOriginalLongitudinalPairing n v q x U K b C p.tree
        (fun σ=>Q (p.restrict σ) (p.spin σ)) (p.embed t))).sum=
    (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
      nativeOriginalLongitudinalPairing n v q x U K b C T
        (fun σ=>Q σ (T.atSlot σ s)) t := by
  let L:=nativeOriginalLongitudinalPairing n v q x U K b C T (fun σ=>Q σ (T.atSlot σ s)) t
  have Hrow : (T.markedAttach 0).map (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed s) p.mark*
      nativeOriginalLongitudinalPairing n v q x U K b C p.tree
        (fun σ=>Q (p.restrict σ) (p.spin σ)) (p.embed t))=
      (T.markedAttach 0).map (fun p=>(p.coeff*fullScalarCutGamma p.tree U K (p.embed s) p.mark)*L):=by
    apply List.map_congr_left
    intro p hp
    by_cases hh : U ≤ p.tree.splitIndex (p.embed s) p.mark
    · have Hs : ∀c : T.Slot,star+1 ≤ T.splitIndex s c→c=s:=by intro c hc;exact h c (by omega)
      have H:=native_original_exterior_longitudinal_whole_exchange n v q x U K b C T ho s t ht
        (star+1) Hs p hp (by omega) hq hq0 hK hKm (by omega) hU Q
      simp_rw [hQ] at H
      rw [H,native_original_longitudinal_marked_preserves n v q x U K b C T ho
        (fun σ=>Q σ (T.atSlot σ s)) t p hp hq hq0 hK hKm (by omega) hU]
    · rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hU (lt_of_not_ge hh)]
      ring
  rw [Hrow,List.sum_map_mul_right,native_full_gamma_row_hessian n T ho 0 ho U (by omega) K s]

theorem native_original_fresh_partner_longitudinal_constant_row_collapse
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (h : NativeTargetStarSingleton T s star)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    nativeOriginalFreshPartnerLResponse n v q x U K b C T s star (fun _ c d=>A c d)=
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        nativeOriginalLongitudinalPairing n v q x U K b C g.tree
          (fun σ=>A (T.atSlot (g.restrict σ) s) (g.spin σ)) g.mark := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 s star
  let FL (p : MarkedPlacement g.tree):=p.coeff*fullScalarCutGamma p.tree U K (p.embed (g.embed s)) p.mark*
    nativeOriginalLongitudinalPairing n v q x U K b C p.tree
      (fun σ=>A (p.spin σ) (g.spin (p.restrict σ))) (p.embed g.mark)
  let FR (r : MarkedPlacement T):=r.coeff*fullScalarCutGamma r.tree U K (r.embed s) r.mark*
    (let f:=nativeFreshAtSlot r.tree 0 (r.embed s) star
    nativeOriginalLongitudinalPairing n v q x U K b C f.tree
      (fun σ=>A (r.spin (f.restrict σ)) (f.spin σ)) f.mark)
  have HL:=native_high_row_sum_eq_full_of_support g.tree (g.embed s) star 0 FL (by
    intro p hp hh
    dsimp only [FL]
    rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hU (by omega)]
    ring)
  have HR:=native_high_row_sum_eq_full_of_support T s star 0 FR (by
    intro p hp hh
    dsimp only [FR]
    rw [fullScalarCutGamma_cross_zero p.tree ho U K _ _ hU (by omega)]
    ring)
  have HF:=native_original_high_fresh_gamma_longitudinal_row n v q x U K b C T ho s star
    (hs.le.trans hU) 0 0 hq hq0 hK hKm (by omega) hU (fun _ c d=>A c d)
  change ((nativeHighMarkedRows g.tree (g.embed s) star 0).map FL).sum=
    ((nativeHighMarkedRows T s star 0).map FR).sum at HF
  have HE : nativeOriginalFreshPartnerLResponse n v q x U K b C T s star (fun _ c d=>A c d)=
      ((g.tree.markedAttach 0).map FL).sum:=by
    change ((T.markedAttach 0).map FR).sum=_
    exact HR.symm.trans (HF.symm.trans HL)
  rw [HE]
  have Hsingle : NativeTargetStarSingleton g.tree (g.embed s) star:=h.retain_fresh 0 le_rfl
  have Hne : g.mark≠g.embed s:=nativeFreshAtSlot_distinct T 0 s star s
  have HC:=native_original_singleton_exterior_gamma_longitudinal_row_collapse n v q x U K b C
    g.tree ho (g.embed s) g.mark Hne star hs hU Hsingle hq hq0 hK hKm
    (fun σ z=>A z (g.spin σ)) (by
      intro σ u z
      rw [g.spin_at,nativeReplaceAtSlot_at,ite_eq_right Hne,←g.spin_at])
  have Htest : (fun σ : g.tree.Assignment=>A (g.tree.atSlot σ (g.embed s)) (g.spin σ))=
      (fun σ=>A (T.atSlot (g.restrict σ) s) (g.spin σ)):=by
    funext σ
    rw [g.restrict_at]
  rw [Htest] at HC
  exact HC

end OAI.SKFluctuations.Cavity
