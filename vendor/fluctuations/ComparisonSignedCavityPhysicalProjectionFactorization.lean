module

public import ComparisonSignedCavityActualObservedProjectionFactorization
public import ComparisonSignedCavityStarProjectionPowerMoments

@[expose] public section

noncomputable section
open scoped Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

theorem nativeStarPairFactor_eq_centered_projection (n : ℕ)
    (as : List PositiveMass) (star : ℕ) (q : ℕ→RestCoordinate n→ℝ≥0)
    (center : ℝ) (x : RestCoordinate n→ℝ) (σ : Spin n) :
    nativeStarPairFactor (restWeight n) (restFeature n) as star q
      (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))-center) x σ=
      nativeStarCenteredProjection n (as.drop star) (fun j=>q (star+j)) center x σ := by
  unfold nativeStarPairFactor nativeStarCenteredProjection singleMean
  rfl

theorem nativeStarPairFactor_two_level_centered_projection (n : ℕ)
    (pre mid tail : List PositiveMass) (q : ℕ→RestCoordinate n→ℝ≥0)
    (center : ℝ) (x : RestCoordinate n→ℝ) (σ : Spin n) :
    nativeStarPairFactor (restWeight n) (restFeature n) (pre++(mid++tail))
      (pre.length+mid.length) q
      (fun u v=>deletedOverlap n (joinSpin (u,false)) (joinSpin (v,false))-center) x σ=
      nativeStarCenteredProjection n tail (fun j=>q (pre.length+(mid.length+j))) center x σ := by
  rw [nativeStarPairFactor_eq_centered_projection]
  simp only [Nat.add_assoc]
  simp

end OAI.SKFluctuations.Cavity
