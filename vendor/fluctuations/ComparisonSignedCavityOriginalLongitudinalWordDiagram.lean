module

public import ComparisonSignedCavityOriginalGWordDiagram

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

def nativeOriginalLongitudinalPairDiagramValue {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (U : ℕ) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (D : NativeObservedDiagram T) : ℝ :=
  match D.marks with
  | [f,e,c,t]=>D.tree.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ=>A (T.atSlot (D.read σ) s) (D.tree.atSlot σ t)*
        nativeOriginalHighGAtom D.tree U K b C (D.embed s) c e f σ) x
  | _=>0

theorem native_original_longitudinal_eq_three_high_rows
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (s : T.Slot) (star U : ℕ)
    (hs : star < U) (hU : U ≤ as.length) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (P : T.Assignment→ℝ) :
    nativeOriginalLongitudinalPairing n v q x U K b C T P s=
      ((nativeHighMarkedRows T s star 0).map (fun p=>p.coeff*
        nativeOriginalLocalizedHighPairing n v q x U star K b C p.tree
          (fun σ=>P (p.restrict σ)) (p.embed s) p.mark)).sum := by
  rw [native_original_longitudinal_eq_connected_rows n v q x U K b C T ho P s hU]
  rw [←native_high_row_sum_eq_full_of_support T s star 0 _ (by
    intro p hp hnot
    rw [native_original_connected_high_cross_zero n v q x U K b C p.tree ho _ _ _ hU
      (by omega)]
    exact mul_zero _)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [native_original_connected_high_response_eq_localized_rows n v q x U star K b C
    p.tree ho _ _ _ hs hU]

theorem native_original_longitudinal_pair_eq_word_after_fresh
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (s : T.Slot) (star U : ℕ)
    (hs : star < U) (hU : U ≤ as.length) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    nativeOriginalLongitudinalPairing n v q x U K b C g.tree
      (fun σ=>A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)=
      nativeObservedHighWordSum ((NativeObservedDiagram.identity T).fresh s star 0) s star 3
        (nativeOriginalLongitudinalPairDiagramValue T s U K b C v q x A) := by
  dsimp only
  rw [native_original_longitudinal_eq_three_high_rows _ ho _ star U hs hU]
  unfold nativeOriginalLocalizedHighPairing
  simp only [native_observed_high_word_sum_succ,native_observed_high_word_sum_zero,
    NativeObservedDiagram.identity,NativeObservedDiagram.fresh,NativeObservedDiagram.observe,
    List.map_nil,List.nil_append,List.map_cons,nativeOriginalLongitudinalPairDiagramValue]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro r hr
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro z hz
  congr 1
  apply congrArg (fun J=>z.tree.disorderExpect (fullWeight n) (fullFeature n) v q J x)
  funext σ
  simp only [id_eq,p.restrict_at,r.restrict_at,z.restrict_at,
    (nativeFreshAtSlot T 0 s star).spin_at]

theorem native_original_longitudinal_pair_eq_word_before_fresh
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (s : T.Slot) (star U : ℕ)
    (hs : star < U) (hU : U ≤ as.length) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    nativeOriginalLongitudinalPairing n v q x U K b C g.tree
      (fun σ=>A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)=
      nativeObservedHighWordSum (NativeObservedDiagram.identity T) s star 3
        (fun D=>nativeOriginalLongitudinalPairDiagramValue T s U K b C v q x A
          (D.fresh s star 0)) := by
  dsimp only
  rw [native_original_longitudinal_pair_eq_word_after_fresh T ho s star U hs hU,
    native_observed_high_word_sum_fresh 3 _ s star (hs.le.trans hU) 0]

end OAI.SKFluctuations.Cavity
