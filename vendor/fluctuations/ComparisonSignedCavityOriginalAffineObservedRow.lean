module

public import ComparisonSignedCavityActualExpansionFreshAffineRow

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeCanonicalObservedFreshAffineRow (n a : ℕ) {as : List PositiveMass}
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (star U : ℕ) (c b fslot : T.Slot) (useNew : Bool)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) : ℝ :=
  ((T.markedAttach 0).map fun p=>p.coeff*
    (fullScalarCutGamma p.tree U K (p.embed c) p.mark*
      nativeOriginalFreshAffineResidual n M p.tree (p.embed c) p.mark (p.embed b) star q
        (fun σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor M
          (nativeObservedRemainingTarget c p useNew) (p.embed fslot) σ*
          (G.canonicalMinimumSource M forms).restProduct (p.restRestrict σ)))).sum

theorem native_canonical_observed_fresh_affine_row_eq_high
    (n a : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (star U : ℕ) (hU : U≤as.length)
    (c b fslot : T.Slot) (useNew : Bool)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) :
    nativeCanonicalObservedFreshAffineRow n a M T star U c b fslot useNew G forms q K=
      nativeCanonicalObservedFreshAffineHighRow n a M T star U c b fslot useNew G forms q K := by
  unfold nativeCanonicalObservedFreshAffineRow nativeCanonicalObservedFreshAffineHighRow
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  by_cases hhigh : U≤p.tree.splitIndex (p.embed c) p.mark
  · simp only [hhigh,↓reduceIte]
  · have hzero:=fullScalarCutGamma_cross_zero p.tree ho U K (p.embed c) p.mark hU (by omega)
    simp only [hhigh,↓reduceIte,hzero,zero_mul,mul_zero]

end OAI.SKFluctuations.Cavity
