module

public import ComparisonActualHighOnlyLowB0ObservedAffineReadoutSourceAlong
public import ComparisonSignedCavityActualFreshAffineRow

@[expose] public section
noncomputable section
set_option maxHeartbeats 12000000
set_option autoImplicit false
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
def nativeCanonicalObservedFreshHighRow_high_only (n a : ℕ) {as : List PositiveMass}
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (star U : ℕ) (c b fslot : T.Slot) (useNew : Bool)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) : ℝ :=
  ((T.markedAttach 0).map fun p=>p.coeff*
    (if U≤p.tree.splitIndex (p.embed c) p.mark then
      fullScalarCutGamma p.tree U K (p.embed c) p.mark*
        nativeOriginalFreshResidual n p.tree (p.embed c) p.mark (p.embed b) 0 star 0 q 0
          (fun σ=>ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M
            (nativeObservedRemainingTarget c p useNew) (p.embed fslot) σ*
            (G.canonicalHighOnlySource M forms).restProduct (p.restRestrict σ)) else 0)).sum

theorem native_original_fresh_affine_residual_eq_bond_mul_high_only
    (n : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (s e b : T.Slot) (star : ℕ)
    (hhigh : star < T.splitIndex s e) (hlow : T.splitIndex s b≤ star)
    (q : ℕ→RestCoordinate n→ℝ) (Z : T.cavityLeft.Assignment→ℝ) :
    nativeOriginalFreshAffineResidual_high_only n M T s e b star q Z=
      (M.bf (partitionPoint 0 as (T.splitIndex s b)):ℝ)*
        nativeOriginalFreshResidual n T s e b 0 star 0 q 0 Z := by
  have heb : T.splitIndex e b=T.splitIndex s b :=
    T.splitIndex_low_eq_of_high e s b (U:=star+1)
      (by rw [T.splitIndex_symm];omega) (by omega)
  have heblow : T.splitIndex e b≤ star:=by simpa only [heb] using hlow
  let g:=nativeFreshAtSlot T 0 b star
  have hgs : g.tree.splitIndex g.mark (g.embed s)=T.splitIndex s b:=
    native_fresh_low_pair_split T s b 0 star hlow
  have hge : g.tree.splitIndex g.mark (g.embed e)=T.splitIndex s b:=
    (native_fresh_low_pair_split T e b 0 star heblow).trans heb
  unfold nativeOriginalFreshAffineResidual_high_only nativeOriginalFreshResidual
  dsimp only
  rw [←g.tree.cavityLeft.disorderExpect_const_mul (restWeight_pos n) (restFeature n) ho]
  congr 1
  funext σ
  change Z (g.restRestrict σ)*
    (ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M g.mark (g.embed s) σ-
      ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only M g.mark (g.embed e) σ)=_
  unfold ActualNaturalBoundaryShape.canonicalLowRestFactor_high_only
  rw [hgs,hge]
  simp only [fullBoundaryAffineFactor,MarkedPlacement.restSpin]
  rw [←g.restRestrict_at σ s,←g.restRestrict_at σ e]
  dsimp only [g]
  ring

theorem native_canonical_observed_fresh_affine_row_eq_bond_mul_high_only
    (n a : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as) (star U : ℕ) (hU : star < U)
    (c b fslot : T.Slot) (useNew : Bool) (hcb : T.splitIndex c b≤ star)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) :
    nativeCanonicalObservedFreshAffineHighRow_high_only n a M T star U c b fslot useNew G forms q K=
      (M.bf (partitionPoint 0 as (T.splitIndex c b)):ℝ)*
        nativeCanonicalObservedFreshHighRow_high_only n a M T star U c b fslot useNew G forms q K := by
  unfold nativeCanonicalObservedFreshAffineHighRow_high_only nativeCanonicalObservedFreshHighRow_high_only
  rw [←List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  by_cases hhigh : U≤p.tree.splitIndex (p.embed c) p.mark
  · simp only [hhigh,↓reduceIte]
    rw [native_original_fresh_affine_residual_eq_bond_mul_high_only n M p.tree ho
      (p.embed c) p.mark (p.embed b) star (by omega) (by
        rw [(T.markedAttach_embed_preserves 0 p hp).2];exact hcb),
      (T.markedAttach_embed_preserves 0 p hp).2]
    ring
  · simp only [hhigh,↓reduceIte,mul_zero]

end OAI.SKFluctuations.Cavity
