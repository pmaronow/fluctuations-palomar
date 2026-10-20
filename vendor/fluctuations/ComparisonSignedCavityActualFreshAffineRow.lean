module

public import ComparisonSignedCavityOriginalFreshAffineIdentity

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem canonical_low_rest_factor_eq_restLowKernel (n : ℕ) {as : List PositiveMass}
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (U : ℕ) (i j : T.Slot)
    (hlow : T.splitIndex i j < U) (σ : T.cavityLeft.Assignment) :
    ActualNaturalBoundaryShape.canonicalLowRestFactor M i j σ=
      restLowKernel n U (fun l=>(M.bf (partitionPoint 0 as l):ℝ))
        (fun l=>(M.hf (partitionPoint 0 as l):ℝ)) (T.splitIndex i j)
        (T.cavityLeft.atSlot σ (T.cavityLeftSlot j)) (T.cavityLeft.atSlot σ (T.cavityLeftSlot i)) := by
  simp [ActualNaturalBoundaryShape.canonicalLowRestFactor,restLowKernel,hlow,
    fullBoundaryAffineFactor,deletedOverlap,joinSpin]

def nativeCanonicalObservedFreshAffineHighRow (n a : ℕ) {as : List PositiveMass}
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (star U : ℕ) (c b fslot : T.Slot) (useNew : Bool)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) : ℝ :=
  ((T.markedAttach 0).map fun p=>p.coeff*
    (if U≤p.tree.splitIndex (p.embed c) p.mark then
      fullScalarCutGamma p.tree U K (p.embed c) p.mark*
        nativeOriginalFreshAffineResidual n M p.tree (p.embed c) p.mark (p.embed b) star q
          (fun σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor M
            (nativeObservedRemainingTarget c p useNew) (p.embed fslot) σ*
            (G.canonicalMinimumSource M forms).restProduct (p.restRestrict σ)) else 0)).sum

theorem native_canonical_observed_fresh_affine_row_eq_bond_mul
    (n a : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (star U : ℕ) (hU : star < U)
    (c b fslot : T.Slot) (useNew : Bool) (hcb : T.splitIndex c b≤ star)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) :
    nativeCanonicalObservedFreshAffineHighRow n a M T star U c b fslot useNew G forms q K=
      (M.bf (partitionPoint 0 as (T.splitIndex c b)):ℝ)*
        nativeCanonicalObservedFreshHighRow n a M T star U c b fslot useNew G forms q K := by
  unfold nativeCanonicalObservedFreshAffineHighRow nativeCanonicalObservedFreshHighRow
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  by_cases hhigh : U≤p.tree.splitIndex (p.embed c) p.mark
  · simp only [hhigh,↓reduceIte]
    rw [native_original_fresh_affine_residual_eq_bond_mul n M p.tree ho
      (p.embed c) p.mark (p.embed b) star (by omega) (by
        rw [(T.markedAttach_embed_preserves 0 p hp).2];exact hcb),
      (T.markedAttach_embed_preserves 0 p hp).2]
    ring
  · simp only [hhigh,↓reduceIte,mul_zero]

end OAI.SKFluctuations.Cavity
