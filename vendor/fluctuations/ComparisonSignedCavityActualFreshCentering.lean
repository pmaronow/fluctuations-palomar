module

public import ComparisonSignedCavityActualOriginalForwardSourceEndpoint
public import ComparisonSignedCavityActualFreshSourceMarginals

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree
open scoped BigOperators NNReal
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false

theorem native_original_rest_test_marked_mean (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (p : MarkedPlacement T)
    (hp : p∈T.markedAttach 0) :
    nativeOriginalRestTestExpectation n q U b h K p.tree (fun σ=>P (p.restRestrict σ))=
      nativeOriginalRestTestExpectation n q U b h K T P := by
  unfold nativeOriginalRestTestExpectation
  simp_rw [←p.restRestrict_actual]
  exact native_marked_disorder_marginal T ho p hp (fullWeight_pos n) (fullFeature n)
    0 (cutFullVariance n q U 1 1 b h K) (fun σ=>P (T.cavityAssignment σ).1) 0

theorem native_original_centered_rest_test_marked (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (p : MarkedPlacement T)
    (hp : p∈T.markedAttach 0) :
    nativeOriginalCenteredRestTest n q U b h K p.tree (fun σ=>P (p.restRestrict σ))=
      fun σ=>nativeOriginalCenteredRestTest n q U b h K T P (p.restRestrict σ) := by
  funext σ
  unfold nativeOriginalCenteredRestTest
  rw [native_original_rest_test_marked_mean n q U b h K T ho P p hp]

theorem native_original_centered_rest_test_fresh (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (s : T.Slot) (star : ℕ) :
    let g:=nativeFreshAtSlot T 0 s star
    nativeOriginalCenteredRestTest n q U b h K g.tree (fun σ=>P (g.restRestrict σ))=
      fun σ=>nativeOriginalCenteredRestTest n q U b h K T P (g.restRestrict σ) := by
  dsimp only
  exact native_original_centered_rest_test_marked n q U b h K T ho P
    (nativeFreshAtSlot T 0 s star) (nativeFreshAtSlot_mem T 0 s star)

end OAI.SKFluctuations.Cavity
