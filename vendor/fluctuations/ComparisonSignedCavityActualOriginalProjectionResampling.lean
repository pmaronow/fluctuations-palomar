module

public import ComparisonSignedCavityActualOriginalProjectionDisplacement
public import ComparisonSignedCavityActualOriginalGProjectedRow

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

theorem native_original_fresh_exterior_displacement_eq_projected_row
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s : T.Slot) (star : ℕ) (hs : star < U) (hU : U ≤ as.length)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (P : T.Assignment→ℝ) (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) :
    nativeOriginalFreshExteriorGDisplacement n v q x U K b C T s star P A=
      nativeActualOriginalGProjectedDisplacement T s star U K b C v q x A P := by
  unfold nativeOriginalFreshExteriorGDisplacement
  rw [native_original_fresh_exterior_response_eq_full_connected_row n v q x U K b C T ho s star
    hs hU hq hq0 hK hKm (fun σ c d=>P σ*(A c d-A (T.atSlot σ s) d))]
  unfold nativeActualOriginalGProjectedDisplacement
  dsimp only
  simp only [mul_comm]

theorem native_actual_generated_original_forward_G_eq_projection_add_resampling
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (K b C : ℕ→ℝ) (hq : ∀j,Monotone (fun u=>q u j)) (hq0 : ∀j,v j ≤ q 0 j)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) :
    let s:=P₀.live.test.target
    let g:=nativeFreshAtSlot T 0 s star
    nativeOriginalConnectedLowForward n v q x U K b C g.tree (fun σ=>P (g.restrict σ))
      (g.embed s) g.mark A=
    (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
      (nativeOriginalLongitudinalPairing n v q x U K b C g.tree
        (fun σ=>P (g.restrict σ)*A (T.atSlot (g.restrict σ) s) (g.spin σ)) (g.embed s)+
        (1/2:ℝ)*nativeActualOriginalGProjectedResampling T s star U K b C v q x A P) := by
  dsimp only
  rw [native_original_fresh_forward_exterior_G_eq_chi_response n v q x U K b C T ho
      P₀.live.test.target star hs hP.highCut_le_length hq hq0 hK hKm P A,
    native_original_fresh_exterior_response_eq_projection_add_displacement n v q x U K b C T ho
      P₀.live.test.target star hs hP.highCut_le_length hq hq0 hK hKm P A,
    native_original_fresh_exterior_displacement_eq_projected_row n v q x U K b C T ho
      P₀.live.test.target star hs hP.highCut_le_length hq hq0 hK hKm P A,
    native_actual_generated_original_G_projected_row_polarization hP hi hs ho v q x K b C
      hq hq0 hK hKm A P]

end OAI.SKFluctuations.Cavity
