module

public import ComparisonSignedCavityActualOriginalGeneratedGPolarization
public import ComparisonSignedCavityActualOriginalPartnerLongitudinal

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

def nativeActualOriginalGProjectedDisplacement {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ((g.tree.markedAttach 0).map (fun p=>p.coeff*
    nativeOriginalConnectedHighResponse n v q x U K b C p.tree
      (fun σ=>(A (p.spin σ) (g.spin (p.restrict σ))-
        A (T.atSlot (g.restrict (p.restrict σ)) s) (g.spin (p.restrict σ)))*
        P (g.restrict (p.restrict σ))) (p.embed (g.embed s)) p.mark)).sum

def nativeActualOriginalGProjectedResampling {n : ℕ} {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (s : T.Slot) (star U : ℕ) (K b C : ℕ→ℝ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) : ℝ :=
  let g:=nativeFreshAtSlot T 0 s star
  ((g.tree.markedAttach 0).map (fun p=>p.coeff*
    nativeOriginalConnectedHighResponse n v q x U K b C p.tree
      (fun σ=>(A (p.spin σ) (g.spin (p.restrict σ))-
        A (T.atSlot (g.restrict (p.restrict σ)) s) (g.spin (p.restrict σ)))*
        (P (g.restrict (p.restrict σ))-
          P (nativeReplaceAtSlot T s (g.restrict (p.restrict σ)) (p.spin σ))))
      (p.embed (g.embed s)) p.mark)).sum

theorem native_actual_generated_original_G_projected_row_polarization
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {i star U k : ℕ} {seed : List NativeResourceMark} {P₀ : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P₀) (hi : i ≤ star) (hs : star < U)
    (ho : MassOrdered 0 as)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (K b C : ℕ→ℝ) (hq : ∀j,Monotone (fun u=>q u j)) (hq0 : ∀j,v j ≤ q 0 j)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) (P : T.Assignment→ℝ) :
    nativeActualOriginalGProjectedDisplacement T P₀.live.test.target star U K b C v q x A P=
      (1/2:ℝ)*nativeActualOriginalGProjectedResampling T P₀.live.test.target star U K b C v q x A P := by
  unfold nativeActualOriginalGProjectedDisplacement nativeActualOriginalGProjectedResampling
  dsimp only
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  by_cases hh : U ≤ p.tree.splitIndex
      (p.embed ((nativeFreshAtSlot T 0 P₀.live.test.target star).embed P₀.live.test.target)) p.mark
  · rw [native_actual_generated_original_G_fresh_displacement_polarization hP hi hs ho v q x K b C
      p hp hh hq hq0 hK hKm A P]
    ring
  · rw [native_original_connected_high_cross_zero n v q x U K b C p.tree ho _ _ _
        hP.highCut_le_length (lt_of_not_ge hh),
      native_original_connected_high_cross_zero n v q x U K b C p.tree ho _ _ _
        hP.highCut_le_length (lt_of_not_ge hh)]
    ring

end OAI.SKFluctuations.Cavity
