module

public import ComparisonSignedCavityActualOriginalForwardExteriorContraction
public import ComparisonSignedCavityActualOriginalGProjectedPolarization

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem native_original_fresh_exterior_response_eq_full_connected_row
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (Q : T.Assignment→(Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    nativeOriginalFreshExteriorGResponse n v q x U K b C T s star Q=
    ((g.tree.markedAttach 0).map (fun p=>p.coeff*
      nativeOriginalConnectedHighResponse n v q x U K b C p.tree
        (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ) (g.spin (p.restrict σ)))
        (p.embed (g.embed s)) p.mark)).sum := by
  dsimp only
  let g:=nativeFreshAtSlot T 0 s star
  let FL (p : MarkedPlacement g.tree) := p.coeff*
    nativeOriginalConnectedHighResponse n v q x U K b C p.tree
      (fun σ=>Q (g.restrict (p.restrict σ)) (p.spin σ) (g.spin (p.restrict σ)))
      (p.embed (g.embed s)) p.mark
  let FR (r : MarkedPlacement T) := r.coeff*
    (let g:=nativeFreshAtSlot r.tree 0 (r.embed s) star
    nativeOriginalConnectedHighResponse n v q x U K b C g.tree
      (fun σ=>Q (r.restrict (g.restrict σ)) (r.spin (g.restrict σ)) (g.spin σ))
      (g.embed (r.embed s)) (g.embed r.mark))
  have HL:=native_high_row_sum_eq_full_of_support g.tree (g.embed s) star 0 FL (by
    intro p hp hh
    dsimp only [FL]
    rw [native_original_connected_high_cross_zero n v q x U K b C p.tree ho _ _ _ hU (by omega),mul_zero])
  have HR:=native_high_row_sum_eq_full_of_support T s star 0 FR (by
    intro r hr hh
    dsimp only [FR]
    rw [native_original_connected_high_cross_zero n v q x U K b C _ ho _ _ _ hU]
    · exact mul_zero _
    · rw [(r.tree.markedAttach_embed_preserves 0 (nativeFreshAtSlot r.tree 0 (r.embed s) star)
          (nativeFreshAtSlot_mem r.tree 0 (r.embed s) star)).2]
      omega)
  have HF:=native_original_high_fresh_connected_response_row n v q x U K b C T ho s star
    (hs.le.trans hU) hq hq0 hK hKm Q
  exact HR.symm.trans (HF.symm.trans HL)

theorem native_original_fresh_exterior_projected_response_eq_L
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (P : T.Assignment→ℝ) (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    nativeOriginalFreshExteriorGResponse n v q x U K b C T s star
      (fun σ _ d=>P σ*A (T.atSlot σ s) d)=
    nativeOriginalLongitudinalPairing n v q x U K b C g.tree
      (fun σ=>P (g.restrict σ)*A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s) := by
  dsimp only
  rw [native_original_fresh_exterior_response_eq_full_connected_row n v q x U K b C T ho s star
    hs hU hq hq0 hK hKm (fun σ _ d=>P σ*A (T.atSlot σ s) d)]
  exact (native_original_longitudinal_eq_connected_rows n v q x U K b C
    (nativeFreshAtSlot T 0 s star).tree ho
    (fun σ=>P ((nativeFreshAtSlot T 0 s star).restrict σ)*
      A (T.atSlot ((nativeFreshAtSlot T 0 s star).restrict σ) s) ((nativeFreshAtSlot T 0 s star).spin σ))
    ((nativeFreshAtSlot T 0 s star).embed s) hU).symm

def nativeOriginalFreshExteriorGDisplacement
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star : ℕ)
    (P : T.Assignment→ℝ) (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) : ℝ :=
  nativeOriginalFreshExteriorGResponse n v q x U K b C T s star
    (fun σ c d=>P σ*(A c d-A (T.atSlot σ s) d))

theorem native_original_fresh_exterior_response_eq_projection_add_displacement
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (P : T.Assignment→ℝ) (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) :
    let g:=nativeFreshAtSlot T 0 s star
    nativeOriginalFreshExteriorGResponse n v q x U K b C T s star (fun σ c d=>P σ*A c d)=
    nativeOriginalLongitudinalPairing n v q x U K b C g.tree
      (fun σ=>P (g.restrict σ)*A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)+
      nativeOriginalFreshExteriorGDisplacement n v q x U K b C T s star P A := by
  dsimp only
  conv_rhs => rw [←native_original_fresh_exterior_projected_response_eq_L n v q x U K b C T ho s star
    hs hU hq hq0 hK hKm P A]
  unfold nativeOriginalFreshExteriorGDisplacement nativeOriginalFreshExteriorGResponse
  conv_rhs => rw [←List.sum_map_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  dsimp only
  let g:=nativeFreshAtSlot p.tree 0 (p.embed s) star
  let F:=fun σ : g.tree.Assignment=>P (p.restrict (g.restrict σ))*
    A (T.atSlot (p.restrict (g.restrict σ)) s) (g.spin σ)
  let D:=fun σ : g.tree.Assignment=>P (p.restrict (g.restrict σ))*
    (A (p.spin (g.restrict σ)) (g.spin σ)-A (T.atSlot (p.restrict (g.restrict σ)) s) (g.spin σ))
  have HE : (fun σ : g.tree.Assignment=>P (p.restrict (g.restrict σ))*A (p.spin (g.restrict σ)) (g.spin σ))=
      fun σ=>(1:ℝ)*F σ+1*D σ := by
    funext σ
    dsimp only [F,D]
    ring
  rw [HE,native_original_connected_high_test_linear n v q x U K b C g.tree ho F D _ _ hU 1 1]
  ring

end OAI.SKFluctuations.Cavity
