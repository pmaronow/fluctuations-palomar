module

public import ComparisonSignedCavityActualOriginalGProjectedRow
public import ComparisonSignedCavityHighRowsSupportReduction

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

theorem native_original_G_atom_first_source_cross_zero {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K b C : ℕ→ℝ)
    (a c e f : T.Slot) (he : T.splitIndex a e < U) (σ : T.Assignment) :
    nativeOriginalHighGAtom T U K b C a c e f σ=0 := by
  simp only [nativeOriginalHighGAtom,not_le.mpr he,and_false,false_and,ite_false]

theorem native_original_G_atom_second_source_cross_zero {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (K b C : ℕ→ℝ)
    (a c e f : T.Slot) (hf : T.splitIndex a f < U) (σ : T.Assignment) :
    nativeOriginalHighGAtom T U K b C a c e f σ=0 := by
  simp only [nativeOriginalHighGAtom,not_le.mpr hf,and_false,false_and,ite_false]

def nativeOriginalLocalizedHighPairing (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U star : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ) (a c : T.Slot) : ℝ :=
  ((nativeHighMarkedRows T a star 0).map (fun p=>p.coeff*
    ((nativeHighMarkedRows p.tree (p.embed a) star 0).map (fun r=>r.coeff*
      r.tree.disorderExpect (fullWeight n) (fullFeature n) v q
        (fun σ=>P (p.restrict (r.restrict σ))*nativeOriginalHighGAtom r.tree U K b C
          (r.embed (p.embed a)) (r.embed (p.embed c)) (r.embed p.mark) r.mark σ) x)).sum)).sum

theorem native_original_connected_high_response_eq_localized_rows (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U star : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (a c : T.Slot) (hs : star < U) (hU : U ≤ as.length) :
    nativeOriginalConnectedHighResponse n v q x U K b C T P a c=
      nativeOriginalLocalizedHighPairing n v q x U star K b C T P a c := by
  rw [←native_original_G_rows_eq_connected_response n v q x U K b C T ho P a c hU]
  unfold nativeOriginalLocalizedHighPairing
  symm
  apply native_two_high_nested_full_of_support T a a star 0
  · intro p hp r hr hnot
    have he : r.tree.splitIndex (r.embed (p.embed a)) (r.embed p.mark) < U := by
      rw [(p.tree.markedAttach_embed_preserves 0 r hr).2]
      omega
    have HT : (fun σ : r.tree.Assignment=>P (p.restrict (r.restrict σ))*
        nativeOriginalHighGAtom r.tree U K b C (r.embed (p.embed a))
          (r.embed (p.embed c)) (r.embed p.mark) r.mark σ)=fun _=>0 := by
      funext σ
      rw [native_original_G_atom_first_source_cross_zero r.tree U K b C _ _ _ _ he σ,mul_zero]
    rw [HT]
    simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
  · intro p hp r hr hnot
    have hf : r.tree.splitIndex (r.embed (p.embed a)) r.mark < U := by omega
    have HT : (fun σ : r.tree.Assignment=>P (p.restrict (r.restrict σ))*
        nativeOriginalHighGAtom r.tree U K b C (r.embed (p.embed a))
          (r.embed (p.embed c)) (r.embed p.mark) r.mark σ)=fun _=>0 := by
      funext σ
      rw [native_original_G_atom_second_source_cross_zero r.tree U K b C _ _ _ _ hf σ,mul_zero]
    rw [HT]
    simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]

def nativeActualOriginalGProjectedLocalizedResampling {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ((nativeHighMarkedRows g.tree (g.embed s) star 0).map (fun p=>p.coeff*
    nativeOriginalLocalizedHighPairing n v q x U star K b C p.tree
      (fun σ=>(A (p.spin σ) (g.spin (p.restrict σ))-
        A (T.atSlot (g.restrict (p.restrict σ)) s) (g.spin (p.restrict σ)))*
        (P (g.restrict (p.restrict σ))-
          P (nativeReplaceAtSlot T s (g.restrict (p.restrict σ)) (p.spin σ))))
      (p.embed (g.embed s)) p.mark)).sum

theorem native_original_G_projected_resampling_eq_three_high_rows
    {n : ℕ} {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (s : T.Slot) (star U : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (K b C : ℕ→ℝ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) :
    nativeActualOriginalGProjectedResampling T s star U K b C v q x A P=
      nativeActualOriginalGProjectedLocalizedResampling T s star U K b C v q x A P := by
  unfold nativeActualOriginalGProjectedResampling nativeActualOriginalGProjectedLocalizedResampling
  dsimp only
  let g:=nativeFreshAtSlot T 0 s star
  rw [←native_high_row_sum_eq_full_of_support g.tree (g.embed s) star 0 _ (by
    intro p hp hnot
    rw [native_original_connected_high_cross_zero n v q x U K b C p.tree ho _ _ _ hU
      (by change p.tree.splitIndex (p.embed (g.embed s)) p.mark < U;omega)]
    exact mul_zero _)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [native_original_connected_high_response_eq_localized_rows n v q x U star K b C p.tree ho
    _ _ _ hs hU]

end OAI.SKFluctuations.Cavity
