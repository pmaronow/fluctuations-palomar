module

public import ComparisonSignedCavityActualOriginalHighExchange
public import ComparisonSignedCavityActualOriginalLongitudinalGhost
public import ComparisonSignedCavityActualExteriorPartnerRowCollapse

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
set_option maxHeartbeats 20000000

theorem native_original_connected_high_cross_zero
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (a c : T.Slot) (hU : U ≤ as.length)
    (hac : T.splitIndex a c < U) :
    nativeOriginalConnectedHighResponse n v q x U K b C T P a c=0 := by
  rw [←native_original_G_rows_eq_connected_response n v q x U K b C T ho P a c hU]
  have Htest (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0) :
      (fun σ=>P (p.restrict (r.restrict σ))*nativeOriginalHighGAtom r.tree U K b C
        (r.embed (p.embed a)) (r.embed (p.embed c)) (r.embed p.mark) r.mark σ)=fun _=>0 := by
    funext σ
    have Hsplit : r.tree.splitIndex (r.embed (p.embed a)) (r.embed (p.embed c))=T.splitIndex a c := by
      rw [(p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2]
    simp only [nativeOriginalHighGAtom,Hsplit,not_le.mpr hac,false_and,ite_false,mul_zero]
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hy
  rw [mul_eq_zero]
  right
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hz
  rw [Htest p hp r hr]
  simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]

theorem native_original_singleton_exterior_G_row_collapse
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (h : NativeTargetStarSingleton T s star)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (Q : T.Assignment→(Spin n×Bool)→ℝ)
    (hQ : ∀σ u z,Q (nativeReplaceAtSlot T s σ u) z=Q σ z) :
    ((T.markedAttach 0).map (fun p=>p.coeff*
      nativeOriginalConnectedHighResponse n v q x U K b C p.tree
        (fun σ=>Q (p.restrict σ) (p.spin σ)) (p.embed s) p.mark)).sum=
    nativeOriginalLongitudinalPairing n v q x U K b C T
      (fun σ=>Q σ (T.atSlot σ s)) s := by
  rw [native_original_longitudinal_eq_connected_rows n v q x U K b C T ho _ _ hU]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  by_cases hh : U ≤ p.tree.splitIndex (p.embed s) p.mark
  · have Hs : ∀c : T.Slot,star+1 ≤ T.splitIndex s c→c=s := by
      intro c hc
      exact h c (by omega)
    have H:=native_original_connected_high_whole_exchange n v q x U K b C T ho s (star+1)
      Hs p hp (by omega) hq hq0 hK hKm Q
    simp_rw [hQ] at H
    rw [H]
  · rw [native_original_connected_high_cross_zero n v q x U K b C p.tree ho _ _ _ hU
        (lt_of_not_ge hh),
      native_original_connected_high_cross_zero n v q x U K b C p.tree ho _ _ _ hU
        (lt_of_not_ge hh)]

theorem native_original_fresh_partner_G_row_collapse
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (Q : T.Assignment→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    ((g.tree.markedAttach 0).map (fun p=>p.coeff*
      nativeOriginalConnectedHighResponse n v q x U K b C p.tree
        (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ)) (p.embed g.mark) p.mark)).sum=
    nativeOriginalLongitudinalPairing n v q x U K b C g.tree
      (fun σ=>Q (g.restrict σ) (g.spin σ)) g.mark := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 s star
  have H:=native_original_singleton_exterior_G_row_collapse n v q x U K b C g.tree ho
    g.mark star hs hU (native_fresh_target_star_singleton T 0 s star) hq hq0 hK hKm
    (fun σ z=>Q (g.restrict σ) z) (by intro σ u z;rw [native_fresh_replace_restrict T s star])
  simpa only [←g.spin_at] using H

theorem native_actual_fresh_high_partner_G_row_collapse
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (p : MarkedPlacement (nativeFreshAtSlot T 0 s star).tree)
    (hp : p∈(nativeFreshAtSlot T 0 s star).tree.markedAttach 0)
    (hh : U ≤ p.tree.splitIndex (p.embed ((nativeFreshAtSlot T 0 s star).embed s)) p.mark)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      nativeOriginalConnectedHighResponse n v q x U K b C r.tree
        (fun σ=>Q (g.restrict (p.restrict (r.restrict σ)))
          (p.spin (r.restrict σ)) (r.spin σ)) (r.embed (p.embed g.mark)) r.mark)).sum=
    nativeOriginalLongitudinalPairing n v q x U K b C p.tree
      (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ) (g.spin (p.restrict σ))) (p.embed g.mark) := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 s star
  have hab : g.tree.splitIndex (g.embed s) g.mark=star := by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,
      Nat.min_eq_left (hs.le.trans hU)]
  have Hsplit : p.tree.splitIndex (p.embed g.mark) p.mark=star := by
    have HE : p.tree.splitIndex (p.embed (g.embed s)) (p.embed g.mark)=star := by
      rw [(g.tree.markedAttach_embed_preserves 0 p hp).2,hab]
    have HE' : p.tree.splitIndex (p.embed (g.embed s)) (p.embed g.mark) < U := by omega
    have HB : U ≤ p.tree.splitIndex (p.embed g.mark) (p.embed g.mark) := by
      rw [p.tree.splitIndex_self]
      exact hU
    have HX:=native_cross_split_of_same_cut_blocks p.tree U (p.embed (g.embed s)) (p.embed g.mark)
      p.mark (p.embed g.mark) HE' hh HB
    exact (p.tree.splitIndex_symm _ _).trans (HX.trans HE)
  have Hsingle : NativeTargetStarSingleton p.tree (p.embed g.mark) star :=
    (native_fresh_target_star_singleton T 0 s star).retain_outside_mark p hp Hsplit.le
  have Hmark : p.mark≠p.embed g.mark := by
    intro HE
    rw [HE,p.tree.splitIndex_self] at Hsplit
    omega
  have Hold (σ : p.tree.Assignment) (u : Spin n×Bool) :
      g.restrict (p.restrict (nativeReplaceAtSlot p.tree (p.embed g.mark) σ u))=
        g.restrict (p.restrict σ) := by
    apply T.assignment_ext
    intro c
    rw [g.restrict_at,g.restrict_at,p.restrict_at,p.restrict_at,nativeReplaceAtSlot_at,
      ite_eq_right]
    exact fun HE=>nativeFreshAtSlot_distinct T 0 s star c
      ((g.tree.markedAttach_embed_preserves 0 p hp).1 (HE.symm))
  have Hspin (σ : p.tree.Assignment) (u : Spin n×Bool) :
      p.spin (nativeReplaceAtSlot p.tree (p.embed g.mark) σ u)=p.spin σ := by
    rw [p.spin_at,p.spin_at,nativeReplaceAtSlot_at,ite_eq_right Hmark]
  have H:=native_original_singleton_exterior_G_row_collapse n v q x U K b C p.tree ho
    (p.embed g.mark) star hs hU Hsingle hq hq0 hK hKm
    (fun σ d=>Q (g.restrict (p.restrict σ)) (p.spin σ) d)
    (by intro σ u d;rw [Hold,Hspin])
  have HE : (fun σ : p.tree.Assignment=>Q (g.restrict (p.restrict σ)) (p.spin σ)
      (p.tree.atSlot σ (p.embed g.mark)))=
    (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ) (g.spin (p.restrict σ))) := by
    funext σ
    rw [←p.restrict_at,←g.spin_at]
  rw [HE] at H
  exact H

end OAI.SKFluctuations.Cavity
